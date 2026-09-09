;;;; npm-gate.lisp — the parts of the npm client that can be checked WITHOUT a network.
;;;;
;;;; Resolution and install need a registry, so they are exercised by hand against the real one.
;;;; What can be pinned here is the logic that decides things: whether a lockfile survives a round
;;;; trip, whether a lockfile still covers what a project declares, and -- the important one --
;;;; whether TREE-VIOLATIONS can actually REPORT a violation.
;;;;
;;;; That last one is why this file exists.  INSTALL-TREE refuses to write when the check finds a
;;;; problem, so the check is load-bearing; and every real tree so far has come back clean, which
;;;; is exactly the evidence a check that always returns NIL would also produce.  So a tree is
;;;; broken ON PURPOSE here and the check must catch it.
;;;;
;;;;   sbcl --script inspect/npm-gate.lisp

(require :asdf)
(require :sb-bsd-sockets)
(let* ((here (truename *load-truename*))
       (root (make-pathname :directory (butlast (pathname-directory here)))))
  (push root asdf:*central-registry*)
  (dolist (sib '("seal" "natrium" "cram"))
    (let ((p (probe-file (merge-pathnames (format nil "../~a/" sib) root))))
      (when p (push p asdf:*central-registry*)))))
(handler-bind ((warning #'muffle-warning))
  (let ((*standard-output* (make-broadcast-stream))) (asdf:load-system "shuttle/npm")))
(in-package #:shuttle)

(defvar *f* 0)
(defun ok (name p &optional detail)
  (format t "~&  ~:[FAIL~;ok  ~] ~a~@[   ~a~]~%" p name detail)
  (unless p (incf *f*)))

(defun mk (name version &optional deps)
  (make-instance 'resolved :name name :version version
                 :tarball (format nil "https://registry.npmjs.org/~a/-/~a-~a.tgz" name name version)
                 :integrity (format nil "sha512-~a" (make-string 86 :initial-element #\A))
                 :algorithm :sha512 :dependencies deps))

(defun attach (parent name resolved)
  (let ((n (make-instance 'node :name name :parent parent :resolved resolved)))
    (setf (gethash name (node-children parent)) n)
    n))

(format t "~&~%== the tree check, on a tree that is WRONG ==~%")

;; a -> b@^2.0.0, but only b@1.0.0 is placed where a can see it.
(let* ((root (make-instance 'node))
       (a (attach root "a" (mk "a" "1.0.0" '(("b" . "^2.0.0")))))
       (b (attach root "b" (mk "b" "1.0.0"))))
  (declare (ignore a b))
  (let ((bad (tree-violations root)))
    (ok "a wrong VERSION is reported" (= 1 (length bad)) (first bad))
    (ok "and it names what would be found instead"
        (equal (fourth (first bad)) "1.0.0"))))

;; a -> c, and c is nowhere.
(let* ((root (make-instance 'node)))
  (attach root "a" (mk "a" "1.0.0" '(("c" . "*"))))
  (let ((bad (tree-violations root)))
    (ok "a MISSING dependency is reported" (and (= 1 (length bad))
                                                (eq (fourth (first bad)) :missing))
        (first bad))))

;; The control: the same shape, but correct -- so a check that always complained would fail here.
(let* ((root (make-instance 'node)))
  (attach root "a" (mk "a" "1.0.0" '(("b" . "^2.0.0"))))
  (attach root "b" (mk "b" "2.3.4"))
  (ok "a SOUND tree reports nothing" (null (tree-violations root))))

;; Nesting: the outer b is wrong for a, the nested one is right, and Node finds the nested one.
(let* ((root (make-instance 'node))
       (a (attach root "a" (mk "a" "1.0.0" '(("b" . "^2.0.0"))))))
  (attach root "b" (mk "b" "1.0.0"))
  (attach a "b" (mk "b" "2.0.1"))
  (ok "a nested copy SHADOWS an incompatible outer one" (null (tree-violations root))))

(format t "~&~%== the lockfile round trip ==~%")

(let* ((root (make-instance 'node))
       (curves (attach root "@noble/curves" (mk "@noble/curves" "1.2.0"))))
  (attach root "nostr-tools" (mk "nostr-tools" "2.15.0"))
  (attach curves "@noble/hashes" (mk "@noble/hashes" "1.3.2"))
  (attach root "@noble/hashes" (mk "@noble/hashes" "1.3.1"))
  (let ((path "/tmp/shuttle-npm-gate-lock.json")
        (deps '(("nostr-tools" . "2.15.0"))))
    (write-lockfile root path :root-deps deps)
    (multiple-value-bind (back back-deps) (read-lockfile path)
      (ok "every package comes back" (= (length (tree-nodes back)) (length (tree-nodes root)))
          (format nil "~d" (length (tree-nodes back))))
      (ok "the root dependency list comes back" (equal back-deps deps))
      (ok "positions survive, INCLUDING the nesting"
          (equal (mapcar #'node-path-string (tree-nodes back))
                 (mapcar #'node-path-string (tree-nodes root)))
          (find "node_modules/@noble/curves/node_modules/@noble/hashes"
                (mapcar #'node-path-string (tree-nodes back)) :test #'string=))
      (ok "a SCOPED name is not split into two directories"
          (gethash "@noble/curves" (node-children back)))
      (ok "integrity survives, because it is what pins the bytes"
          (every (lambda (a b) (string= (resolved-integrity (node-resolved a))
                                        (resolved-integrity (node-resolved b))))
                 (tree-nodes back) (tree-nodes root)))
      ;; Writing what was read must reproduce the file, or the lock is not a lock.
      (let ((again "/tmp/shuttle-npm-gate-lock-2.json"))
        (write-lockfile back again :root-deps back-deps)
        (ok "re-writing what was read is byte-identical"
            (string= (slurp-file path) (slurp-file again)))))))

(format t "~&~%== does the lockfile still cover what is declared? ==~%")
(let* ((root (make-instance 'node)))
  (attach root "b" (mk "b" "2.3.4"))
  (ok "a range the locked version satisfies is covered" (lock-covers-p root '(("b" . "^2.0.0"))))
  (ok "a widened range that it no longer satisfies is NOT covered"
      (not (lock-covers-p root '(("b" . "^3.0.0")))))
  (ok "a dependency the lockfile has never heard of is NOT covered"
      (not (lock-covers-p root '(("b" . "^2.0.0") ("zzz" . "*"))))))

(format t "~&~%== ~[all npm checks passed~:;~:*~d FAILED~] ==~%~%" *f*)
(sb-ext:exit :code (if (zerop *f*) 0 1))
