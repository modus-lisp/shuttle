;;;; test262-sub.lisp — score ONE test262 subtree (a focused development gate).
;;;;   SHUTTLE_TEST262=<checkout> SHUTTLE_SUB=built-ins/Array/prototype/filter \
;;;;     sbcl --control-stack-size 8 --dynamic-space-size 3072 --script inspect/test262-sub.lisp
;;;; Reuses the full runner's engine (test262-lib.lisp: same harness/skip/scoring).
;;;; SHUTTLE_SUB is a case-sensitive substring matched against each test's path
;;;; under test/ (a directory prefix like "built-ins/Array/prototype/fill" or any
;;;; substring). Prints each FAIL path then "SUMMARY <pass> <total>".
(require :asdf)
(push (truename (merge-pathnames "../" (directory-namestring *load-truename*))) asdf:*central-registry*)
(handler-bind ((warning #'muffle-warning)) (asdf:load-system "shuttle"))
(in-package #:shuttle)
(load (merge-pathnames "test262-lib.lisp" (directory-namestring *load-truename*)))

(let* ((sub (or (sb-ext:posix-getenv "SHUTTLE_SUB")
                (error "set SHUTTLE_SUB to the subtree/substring to score")))
       (rootlen (length (namestring (merge-pathnames "test/" *root*))))
       (tp 0) (tt 0) (skip 0) (fails '()))
  (dolist (path (directory (merge-pathnames "test/**/*.js" *root*)))
    (let ((n (namestring path)))
      (when (and (not (search "_FIXTURE" n)) (search sub (subseq n rootlen)))
        (let ((r (run-test path)))
          (case r
            (:skip (incf skip))
            (:pass (incf tp) (incf tt))
            (:fail (incf tt) (push (subseq n rootlen) fails)))))))
  (dolist (f (sort (nreverse fails) #'string<)) (format t "FAIL ~a~%" f))
  (format t "~&== ~a ==~%" sub)
  (format t "  ~d/~d passing  (~,1f%)   [~d skipped]~%"
          tp tt (if (plusp tt) (* 100.0 (/ tp tt)) 0) skip)
  (format t "SUMMARY ~d ~d~%" tp tt)
  (sb-ext:exit :code 0))
