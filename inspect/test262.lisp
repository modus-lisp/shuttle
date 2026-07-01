;;;; test262.lisp — run the WHOLE suite and report a pass-rate, per area.
;;;;   SHUTTLE_TEST262=<checkout> sbcl --script inspect/test262.lisp
;;;; Defaults to the committed slice (inspect/test262/); point it at a full
;;;; checkout for the whole suite. Positive test passes iff it runs without
;;;; throwing; negative iff it throws. Prints a "SUMMARY <pass> <total>" line
;;;; and a per-area table; a per-instruction budget guards against infinite loops.
;;;; The scoring engine lives in test262-lib.lisp (shared with test262-sub.lisp).
(require :asdf)
(push (truename (merge-pathnames "../" (directory-namestring *load-truename*))) asdf:*central-registry*)
(handler-bind ((warning #'muffle-warning)) (asdf:load-system "shuttle"))
(in-package #:shuttle)
(load (merge-pathnames "test262-lib.lisp" (directory-namestring *load-truename*)))

(let ((areas (make-hash-table :test 'equal)) (tp 0) (tt 0) (skip 0) (i 0)
      (rootlen (length (namestring (merge-pathnames "test/" *root*)))))
  (dolist (path (directory (merge-pathnames "test/**/*.js" *root*)))
    (let ((n (namestring path)))
      (unless (search "_FIXTURE" n)
        (incf i) (when (zerop (mod i 2000)) (format *error-output* "~&  ...~d~%" i))
        (let* ((rel (subseq n rootlen))
               (parts (split rel #\/))
               (area (if (>= (length parts) 2) (format nil "~a/~a" (first parts) (second parts)) (first parts)))
               (r (run-test path)) (cell (gethash area areas (list 0 0))))
          (if (eq r :skip) (incf skip)
              (progn (incf (second cell)) (incf tt) (when (eq r :pass) (incf (first cell)) (incf tp))
                     (setf (gethash area areas) cell)))))))
  ;; report: roll first-level areas up for the headline, keep 2nd-level detail in a file
  (with-open-file (d (merge-pathnames "test262-detail.tsv" (directory-namestring *load-truename*))
                     :direction :output :if-exists :supersede :if-does-not-exist :create)
    (dolist (a (sort (loop for k being the hash-keys of areas collect k) #'string<))
      (destructuring-bind (p n) (gethash a areas) (format d "~a~c~d~c~d~%" a #\Tab p #\Tab n))))
  (let ((tops (make-hash-table :test 'equal)))
    (maphash (lambda (a pn) (let* ((top (first (split a #\/))) (c (gethash top tops (list 0 0))))
                              (incf (first c) (first pn)) (incf (second c) (second pn)) (setf (gethash top tops) c)))
             areas)
    (format t "~&== test262  (~a) ==~%" (namestring *root*))
    (dolist (top (sort (loop for k being the hash-keys of tops collect k) #'string<))
      (destructuring-bind (p n) (gethash top tops)
        (format t "  ~6d/~6d  ~5,1f%  ~a~%" p n (if (plusp n) (* 100.0 (/ p n)) 0) top))))
  (format t "  ----~%  TOTAL ~d/~d  (~,2f%)   [~d skipped]~%" tp tt (if (plusp tt) (* 100.0 (/ tp tt)) 0) skip)
  (format t "SUMMARY ~d ~d~%" tp tt)
  (sb-ext:exit :code 0))
