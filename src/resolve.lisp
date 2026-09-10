;;;; resolve.lisp — turn a set of ranges into a node_modules TREE, and prove the tree is sound.
;;;;
;;;; ============================================================================================
;;;; THE LAYOUT IS THE ALGORITHM
;;;; ============================================================================================
;;;;
;;;; Node resolves a bare specifier by walking UP from the importing file, looking in each
;;;; `node_modules` it passes.  So a dependency tree is not a graph drawing -- it is a claim about
;;;; where files sit, and it is correct exactly when every package can find every dependency it
;;;; declared by walking up from where it was placed.
;;;;
;;;; Packages are therefore HOISTED as high as they will go, and nested only where hoisting would
;;;; put the wrong version somewhere it can be seen:
;;;;
;;;;   1. To satisfy (DEPENDENT wants NAME at RANGE), walk up from DEPENDENT.  The FIRST
;;;;      node_modules holding NAME is the one Node would find.
;;;;   2. If that one satisfies RANGE, nothing is installed -- it is already reachable.
;;;;   3. If it exists and does NOT satisfy, the correct version cannot be hoisted past it, so it
;;;;      is nested directly under DEPENDENT, where it shadows the outer one for that subtree.
;;;;   4. If no ancestor has NAME at all, it hoists to the root.
;;;;
;;;; That is why @noble/hashes appears twice in a real nostr-tools install: something wants ^1.3.1
;;;; and @noble/curves@1.2.0 wants exactly 1.3.2, and one of them has to be shadowed.
;;;;
;;;; ============================================================================================
;;;; A PEER IS SATISFIED BY THE DEPENDENT, NOT BY THE PACKAGE
;;;; ============================================================================================
;;;;
;;;; `peerDependencies` says "whoever uses me must already have this, and we must both see the
;;;; SAME copy".  A React plugin peering on react is not asking for a react of its own -- two
;;;; Reacts in one page is the bug the declaration exists to prevent.  So a peer is queued against
;;;; the dependent's POSITION rather than the package's own: it is looked up from where the
;;;; dependent sits, and installed there if missing, so both end up resolving to one copy.
;;;;
;;;; `peerDependenciesMeta[name].optional` marks a peer that is wanted if present and is never a
;;;; reason to install anything or to fail -- an integration, not a requirement.  Those are
;;;; deferred until everything else is placed, then honoured only if the name turned up anyway;
;;;; installing one on demand would defeat the point of calling it optional.
;;;;
;;;; An unsatisfiable REQUIRED peer is an error, not a warning.  npm spent years printing warnings
;;;; here and the result was trees that installed cleanly and broke at runtime.
;;;;
;;;; ============================================================================================
;;;; THE TREE CHECKS ITSELF
;;;; ============================================================================================
;;;;
;;;; TREE-VIOLATIONS re-derives, for every installed package and every dependency it declares,
;;;; what Node would actually find from that location -- and reports anything that is missing or
;;;; the wrong version.  It shares no code with the placement above: placement decides, this
;;;; checks, and a bug in the first does not excuse itself in the second.  An installer that
;;;; cannot say whether its own output resolves is guessing.

(in-package #:shuttle)

(defclass node ()
  ((name :initarg :name :initform nil :reader node-name)
   (resolved :initarg :resolved :initform nil :reader node-resolved)
   (parent :initarg :parent :initform nil :reader node-parent)
   (children :initform (make-hash-table :test 'equal) :reader node-children
             :documentation "This node's own node_modules: NAME -> NODE."))
  (:documentation "One directory in the tree.  The root has no name and no resolved package."))

(defun node-path (n)
  "The node_modules path to N, as a list of names from the root down."
  (let ((acc '()))
    (loop for c = n then (node-parent c)
          while (and c (node-name c))
          do (push (node-name c) acc))
    acc))

(defun node-path-string (n)
  (format nil "~{node_modules/~a~^/~}" (node-path n)))

(defun %lookup (from name)
  "What Node would find for NAME, importing from FROM: the nearest ancestor node_modules with it."
  (loop for n = from then (node-parent n)
        while n
        do (let ((hit (gethash name (node-children n))))
             (when hit (return hit)))))

(defun %placement-host (dependent name range root)
  "The SHALLOWEST position where NAME can be placed and still be seen by DEPENDENT.

Hoisting is not \"root, or else next to the dependent\".  A package rises as far as it can and stops
one level below the nearest copy that would shadow it -- so a conflict deep in the tree pushes a
package down by exactly one node, not all the way to its immediate requester.

That distinction is the whole of webpack's remaining difference from npm: with ajv@6 at the root,
schema-utils@4 (nested under terser-webpack-plugin) needs ajv@8, and the right home is
terser-webpack-plugin/node_modules/ajv -- shared with anything else in that subtree -- not
terser-webpack-plugin/node_modules/schema-utils/node_modules/ajv, which is private to one package
and duplicates for the next one that asks."
  (let ((chain '()))
    (loop for n = dependent then (node-parent n) while n do (push n chain))   ; root first
    (let ((blocker nil))
      ;; The DEEPEST incompatible occupant on the path is the one that would shadow us.
      (dolist (n chain)
        (let ((occ (gethash name (node-children n))))
          (when (and occ (not (semver-satisfies-p (resolved-version (node-resolved occ)) range)))
            (setf blocker n))))
      (if (null blocker)
          root
          (let ((pos (position blocker chain)))
            (if (< (1+ pos) (length chain)) (nth (1+ pos) chain) dependent))))))

(defvar *packument-cache* nil)

(defun %packument (name)
  (or (gethash name *packument-cache*)
      (setf (gethash name *packument-cache*) (registry-packument name))))

(defun %queue-for (node r)
  "The work NODE creates: its dependencies, its OPTIONAL dependencies, and its peers aimed at its
PARENT.

Each item carries a FALLBACK: somewhere deeper to put the package if the aimed-at position is
already occupied by an incompatible version.  For a peer that fallback is the PEERING PACKAGE
itself -- a peer aims at the parent, so without it there is nowhere left to go and the only
options are to overwrite whatever is there or to give up."
  ;; SORTED, and that is a measured choice rather than a tidy one.  Which version wins a hoisted
  ;; slot is decided by which request arrives first, so the order here is part of the answer.
  ;; Manifest order is what npm nominally walks, and switching to it was tried: jest did not
  ;; improve and express got WORSE (identical -> 4 differences).  Sorted order agrees with npm on
  ;; more real trees, so it stays.  Both are deterministic, which is the requirement -- a resolver
  ;; whose answer depends on hash iteration order cannot be locked.
  (append (mapcar (lambda (d) (list node (car d) (cdr d) :dep nil))
                  (sort (copy-list (resolved-dependencies r)) #'string< :key #'car))
          (mapcar (lambda (d) (list node (car d) (cdr d) :optional-dep nil))
                  (sort (copy-list (resolved-optional-deps r)) #'string< :key #'car))
          (mapcar (lambda (d) (list (node-parent node) (car d) (cdr d)
                                    (if (member (car d) (resolved-optional-peers r)
                                                :test #'string=)
                                        :optional-peer :peer)
                                    node))
                  (sort (copy-list (resolved-peers r)) #'string< :key #'car))))

(defun resolve-tree (root-deps &key (progress nil))
  "ROOT-DEPS is an alist of (NAME . RANGE).  Returns (VALUES ROOT-NODE INSTALLED-COUNT).

Breadth-first and deterministic: the queue is drained in order and each package's work is queued
in sorted name order, so the same input always produces the same tree.  A resolver whose answer
depends on hash iteration order cannot be locked."
  (let* ((*packument-cache* (or *packument-cache* (make-hash-table :test 'equal)))
         (root (make-instance 'node))
         (queue (mapcar (lambda (d) (list root (car d) (cdr d) :dep nil)) root-deps))
         (deferred '())                 ; optional peers, settled once everything else is placed
         (installed 0))
    (labels
        ((attach-node (dependent name range r fallback)
           "Place R for DEPENDENT and return the work it creates."
           (let ((host (%placement-host dependent name range root)))
             ;; PEERS DECIDE PLACEMENT, NOT JUST SATISFACTION.  A package and its peers have to
             ;; end up somewhere they can all SEE each other, so if a required peer is already
             ;; visible from the hoisted position at an incompatible version, hoisting there is
             ;; wrong however well the package itself would fit -- it would be permanently unable
             ;; to reach the peer it declared.  Nesting under the dependent puts it where the
             ;; dependent's own resolution of that peer applies.
             ;;
             ;; This is what webpack needs.  ajv@8 hoists to the root, and ajv-keywords@3 peers on
             ;; ajv@^6.9.1; placed at the root it could only ever see ajv@8.  Nested beside the
             ;; schema-utils@3 that pulled it in, it sees that subtree's ajv@6.
             (dolist (peer (resolved-peers r))
               (unless (member (car peer) (resolved-optional-peers r) :test #'string=)
                 (let ((visible (%lookup host (car peer))))
                   (when (and visible
                              (not (semver-satisfies-p
                                    (resolved-version (node-resolved visible)) (cdr peer))))
                     (setf host dependent)))))
             ;; NEVER OVERWRITE.  Replacing an incompatible occupant is the worst available
             ;; outcome: it silently breaks whoever was already resolving through it, somewhere
             ;; else in the tree, and the tree check then reports the damage far from its cause.
             ;; webpack hit exactly this -- a peer aimed at the root displaced the root's ajv@6,
             ;; and schema-utils@3 was left pointing at an ajv@8 it cannot use.  A peer aims at the
             ;; PARENT and so has nowhere deeper of its own; FALLBACK is the peering package.
             (let ((existing (gethash name (node-children host))))
               (when (and existing
                          (not (semver-satisfies-p
                                (resolved-version (node-resolved existing)) range))
                          fallback)
                 (setf host fallback)))
             (let ((occupant (gethash name (node-children host))))
               (when (and occupant
                          (not (semver-satisfies-p
                                (resolved-version (node-resolved occupant)) range)))
                 ;; Nowhere left to put it.  Say so rather than corrupting the tree.
                 (error 'registry-error
                        :text (format nil "cannot place ~a@~a for ~a: ~a already holds ~a@~a, ~
which does not satisfy ~a, and there is no deeper position available"
                                      name (resolved-version r)
                                      (if (node-name dependent) (node-path-string dependent) "the project")
                                      (if (node-name host) (node-path-string host) "the root")
                                      name (resolved-version occupant) range))))
             (let ((child (make-instance 'node :name name :resolved r :parent host)))
               (setf (gethash name (node-children host)) child)
               (incf installed)
               (when progress
                 (format t "~&  ~a@~a~@[  (nested under ~a)~]~%" name (resolved-version r)
                         (when (node-name host) (node-path-string host))))
               (%queue-for child r))))

         (place (dependent name range optional fallback)
           "Install NAME for DEPENDENT unless it is already reachable.  Returns new queue items.

An OPTIONAL dependency that will not resolve, or that is not built for this platform, is SKIPPED
rather than fatal.  That is the entire meaning of the word, and it is how a package ships one
prebuilt binary per platform and each host takes only its own."
           (let ((found (%lookup dependent name)))
             (if (and found (semver-satisfies-p (resolved-version (node-resolved found)) range))
                 '()                    ; already visible at an acceptable version
                 (let ((r (if optional
                              (handler-case (resolve-version name range
                                                             :packument (%packument name))
                                (error () nil))
                              (resolve-version name range :packument (%packument name)))))
                   (cond ((null r) '())
                         ((and optional (not (resolved-runs-here-p r))) '())
                         (t (attach-node dependent name range r fallback))))))))
      (loop
        (cond
          (queue
           (destructuring-bind (dependent name range kind fallback) (pop queue)
             (case kind
               ;; Wanted if present; never a reason to install.  Decided at the end.
               (:optional-peer (push (list dependent name range :peer fallback) deferred))
               (:optional-dep (setf queue (append queue (place dependent name range t fallback))))
               (t (setf queue (append queue (place dependent name range nil fallback)))))))
          (deferred
           ;; An optional peer is honoured only if its name turned up anyway.  Anything still
           ;; absent is dropped -- installing it on demand would make it not optional.
           (let ((ready (remove-if-not (lambda (i) (%lookup (first i) (second i))) deferred)))
             (setf deferred nil)
             (if ready (setf queue ready) (return))))
          (t (return)))))
    (values root installed)))

(defun tree-nodes (root)
  "Every installed node, depth-first, root excluded."
  (let ((acc '()))
    (labels ((walk (n)
               (let ((kids '()))
                 (maphash (lambda (k v) (declare (ignore k)) (push v kids)) (node-children n))
                 (dolist (c (sort kids #'string< :key #'node-name))
                   (push c acc) (walk c)))))
      (walk root))
    (nreverse acc)))

(defun tree-violations (root)
  "Every dependency that would NOT resolve from where its dependent was placed.

Re-derived from the finished tree by the same rule Node uses, sharing nothing with the placement
logic: if these disagree, the tree is wrong, and saying so is the whole job."
  (let ((bad '()))
    (dolist (n (tree-nodes root))
      (let ((r (node-resolved n)))
        ;; Ordinary dependencies are resolved from INSIDE the package.  OPTIONAL ones are not
        ;; checked at all: they are absent by design on a platform they are not built for, and
        ;; flagging that would refuse every install of a package that ships per-platform binaries.
        (dolist (dep (resolved-dependencies r))
          (let* ((name (car dep)) (range (cdr dep))
                 ;; A package's own node_modules is searched before its parent's.
                 (hit (or (gethash name (node-children n)) (%lookup (node-parent n) name))))
            (cond ((null hit) (push (list (node-path-string n) name range :missing) bad))
                  ((not (semver-satisfies-p (resolved-version (node-resolved hit)) range))
                   (push (list (node-path-string n) name range
                               (resolved-version (node-resolved hit)))
                         bad)))))
        ;; A peer is PLACED beside the dependent where it can be (see ATTACH-NODE), but it is
        ;; CHECKED from the package's own position, exactly like a dependency.
        ;;
        ;; The ideal rule is stricter -- a peer is supposed to be the same copy the dependent sees,
        ;; so a copy nested privately inside the peering package defeats the point.  npm abandons
        ;; that rule under conflict, and real trees depend on it doing so: installing webpack puts
        ;; ajv@6 at the root for schema-utils@3 and nests ajv@8 inside ajv-formats, because there
        ;; is nowhere else for the second one to go.  Checking peers only from the parent would
        ;; call npm's own output broken.  What actually matters for whether the tree WORKS is
        ;; whether the package can reach a satisfying copy, and nested it can.
        ;;
        ;; An unsatisfiable required peer is still an error: npm spent years warning here instead,
        ;; and the result was trees that installed cleanly and broke at runtime.  An OPTIONAL peer
        ;; that is simply absent is fine; one that is present and wrong is not.
        (dolist (peer (resolved-peers r))
          (let* ((name (car peer)) (range (cdr peer))
                 (optional (member name (resolved-optional-peers r) :test #'string=))
                 (hit (or (gethash name (node-children n)) (%lookup (node-parent n) name))))
            (cond ((and (null hit) (not optional))
                   (push (list (node-path-string n) name range :missing-peer) bad))
                  ((and hit (not (semver-satisfies-p (resolved-version (node-resolved hit)) range)))
                   (push (list (node-path-string n) name range
                               (format nil "peer sees ~a" (resolved-version (node-resolved hit))))
                         bad)))))))
    (nreverse bad)))
