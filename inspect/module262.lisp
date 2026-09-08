(require :sb-posix)
;;;; module262.lisp — the test262 module-code suite, scored on its own.
;;;;
;;;; The main runner folds these into the whole-corpus number, where 566 tests disappear into
;;;; 47,000.  Modules are new enough here to be worth watching separately, and the headline needs
;;;; splitting anyway: TOP-LEVEL AWAIT is not implemented, and its tests are a third of this
;;;; directory.  A number that mixes "we get this wrong" with "we do not do this yet" tells you
;;;; nothing about either.
;;;;
;;;; Run:  SHUTTLE_TEST262=$PWD/test262-full sbcl --script inspect/module262.lisp \
;;;;         $PWD/test262-full/test/language/module-code/
(require :asdf)
(push (truename (merge-pathnames "../" (directory-namestring *load-truename*)))
      asdf:*central-registry*)
(handler-bind ((warning #'muffle-warning))
  (let ((*standard-output* (make-broadcast-stream))) (asdf:load-system "shuttle")))
(load (merge-pathnames "test262-lib.lisp" (directory-namestring *load-truename*)))
(in-package #:shuttle)
(let* ((dir (second sb-ext:*posix-argv*))
       (files (sort (remove-if (lambda (p) (search "_FIXTURE" (namestring p)))
                               (directory (merge-pathnames "**/*.js" dir)))
                    #'string< :key #'namestring))
       (pass 0) (fail 0) (skip 0) (fails '()))
  (dolist (f files)
    (let ((r (handler-case (run-test f) (error () :fail))))
      (cond ((eq r :pass) (incf pass))
            ((eq r :skip) (incf skip))
            (t (incf fail) (push (file-namestring f) fails)))))
  (setf fails (nreverse fails))
  (format t "~&~a/~a pass (~,1f%), ~a skipped~%" pass (+ pass fail)
          (if (plusp (+ pass fail)) (* 100.0 (/ pass (+ pass fail))) 0) skip)
  (with-open-file (o (or (sb-ext:posix-getenv "SHUTTLE_MODULE_FAILS") "/tmp/modfails.txt")
                     :direction :output :if-exists :supersede)
    (dolist (f fails) (write-line f o)))
  (format t "~&prefix clusters:~%")
  (let ((h (make-hash-table :test 'equal)) (ks '()))
    (dolist (f fails)
      (incf (gethash (subseq f 0 (min 13 (length f))) h 0)))
    (maphash (lambda (k v) (push (cons k v) ks)) h)
    (dolist (kv (subseq (sort ks #'> :key #'cdr) 0 (min 14 (length ks))))
      (format t "  ~4a ~a~%" (cdr kv) (car kv)))))
