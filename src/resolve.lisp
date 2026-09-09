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

(defvar *packument-cache* nil)

(defun %packument (name)
  (or (gethash name *packument-cache*)
      (setf (gethash name *packument-cache*) (registry-packument name))))

(defun %queue-for (node r)
  "The work NODE creates: its own dependencies, and its peers aimed at its PARENT."
  (append (mapcar (lambda (d) (list node (car d) (cdr d) :dep))
                  (sort (copy-list (resolved-dependencies r)) #'string< :key #'car))
          (mapcar (lambda (d) (list (node-parent node) (car d) (cdr d)
                                    (if (member (car d) (resolved-optional-peers r)
                                                :test #'string=)
                                        :optional-peer :peer)))
                  (sort (copy-list (resolved-peers r)) #'string< :key #'car))))

(defun resolve-tree (root-deps &key (progress nil))
  "ROOT-DEPS is an alist of (NAME . RANGE).  Returns (VALUES ROOT-NODE INSTALLED-COUNT).

Breadth-first and deterministic: the queue is drained in order and each package's own work is
queued in sorted name order, so the same input always produces the same tree.  That matters more
than matching npm's exact output -- a resolver whose answer depends on hash iteration order cannot
be locked."
  (let* ((*packument-cache* (or *packument-cache* (make-hash-table :test 'equal)))
         (root (make-instance 'node))
         (queue (mapcar (lambda (d) (list root (car d) (cdr d) :dep)) root-deps))
         (deferred '())                 ; optional peers, settled once everything else is placed
         (installed 0))
    (labels
        ((place (dependent name range)
           "Install NAME for DEPENDENT if it is not already reachable.  Returns new queue items."
           (let ((found (%lookup dependent name)))
             (if (and found (semver-satisfies-p (resolved-version (node-resolved found)) range))
                 '()                    ; already visible at an acceptable version
                 (let* ((r (resolve-version name range :packument (%packument name)))
                        ;; Hoist to the root unless an ancestor already holds a DIFFERENT version
                        ;; of this name, in which case the new one must nest under the dependent or
                        ;; it would simply be shadowed by the one already there.
                        (host (if found dependent root)))
                   ;; The nested slot may itself be taken by an incompatible version -- two
                   ;; siblings of one package wanting different things.  Then the deeper one wins
                   ;; its own subtree, which is the only place it is needed.
                   (let ((existing (gethash name (node-children host))))
                     (when (and existing
                                (not (semver-satisfies-p
                                      (resolved-version (node-resolved existing)) range)))
                       (setf host dependent)))
                   (let ((child (make-instance 'node :name name :resolved r :parent host)))
                     (setf (gethash name (node-children host)) child)
                     (incf installed)
                     (when progress
                       (format t "~&  ~a@~a~@[  (nested under ~a)~]~%" name (resolved-version r)
                               (when (node-name host) (node-path-string host))))
                     (%queue-for child r)))))))
      (loop
        (cond
          (queue
           (destructuring-bind (dependent name range kind) (pop queue)
             (if (eq kind :optional-peer)
                 ;; Wanted if present; never a reason to install.  Decided at the end.
                 (push (list dependent name range :peer) deferred)
                 (setf queue (append queue (place dependent name range))))))
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
        ;; Ordinary dependencies are resolved from INSIDE the package.
        (dolist (dep (resolved-dependencies r))
          (let* ((name (car dep)) (range (cdr dep))
                 ;; A package's own node_modules is searched before its parent's.
                 (hit (or (gethash name (node-children n)) (%lookup (node-parent n) name))))
            (cond ((null hit) (push (list (node-path-string n) name range :missing) bad))
                  ((not (semver-satisfies-p (resolved-version (node-resolved hit)) range))
                   (push (list (node-path-string n) name range
                               (resolved-version (node-resolved hit)))
                         bad)))))
        ;; A peer is resolved from the DEPENDENT's position, and must be the same copy the
        ;; dependent sees -- so it is looked up from the parent, NOT from inside this package.
        ;; An unsatisfiable required peer is an error: npm spent years warning here instead, and
        ;; the result was trees that installed cleanly and broke at runtime.  An OPTIONAL peer
        ;; that is simply absent is fine; one that is present and wrong is not.
        (dolist (peer (resolved-peers r))
          (let* ((name (car peer)) (range (cdr peer))
                 (optional (member name (resolved-optional-peers r) :test #'string=))
                 (hit (%lookup (node-parent n) name)))
            (cond ((and (null hit) (not optional))
                   (push (list (node-path-string n) name range :missing-peer) bad))
                  ((and hit (not (semver-satisfies-p (resolved-version (node-resolved hit)) range)))
                   (push (list (node-path-string n) name range
                               (format nil "peer sees ~a" (resolved-version (node-resolved hit))))
                         bad)))))))
    (nreverse bad)))
