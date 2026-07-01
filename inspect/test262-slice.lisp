;;;; test262-slice.lisp — run ONE contiguous slice of the (deterministically
;;;; sorted) test corpus, in its own process. A fatal SBCL condition (heap/stack
;;;; exhaustion from a pathological test) then kills only this slice, not the
;;;; whole measurement — the batch driver (run262.sh) re-runs the rest.
;;;;   SHUTTLE_TEST262=<checkout> SHUTTLE_SLICE=<start>:<count> \
;;;;   SHUTTLE_SLICE_OUT=<results-file> sbcl ... --script inspect/test262-slice.lisp
;;;; Appends one "AREA <area> <pass> <total>" line per area to the results file,
;;;; plus a final "SLICE <start> <count> <pass> <total> <skip>" line, then exits.
(require :asdf)
(push (truename (merge-pathnames "../" (directory-namestring *load-truename*))) asdf:*central-registry*)
(handler-bind ((warning #'muffle-warning)) (asdf:load-system "shuttle"))
(in-package #:shuttle)
(load (merge-pathnames "test262-lib.lisp" (directory-namestring *load-truename*)))

(defun all-test-files ()
  "Deterministically ordered list of runnable test files (fixtures excluded)."
  (sort (remove-if (lambda (p) (search "_FIXTURE" (namestring p)))
                   (directory (merge-pathnames "test/**/*.js" *root*)))
        #'string< :key #'namestring))

(let* ((spec (or (sb-ext:posix-getenv "SHUTTLE_SLICE") (error "set SHUTTLE_SLICE=start:count")))
       (colon (position #\: spec))
       (start (parse-integer spec :end colon))
       (count (parse-integer spec :start (1+ colon)))
       (out (or (sb-ext:posix-getenv "SHUTTLE_SLICE_OUT") "/tmp/slice-results"))
       (files (all-test-files))
       (n (length files))
       (end (min n (+ start count)))
       (rootlen (length (namestring (merge-pathnames "test/" *root*))))
       (areas (make-hash-table :test 'equal)) (tp 0) (tt 0) (skip 0))
  (loop for idx from start below end
        for path = (nth idx files) do
    ;; tracer: last file this slice touched (for post-mortem if it crashes)
    (ignore-errors (with-open-file (c "/tmp/cur262" :direction :output :if-exists :supersede
                                      :if-does-not-exist :create) (write-string (namestring path) c)))
    (let* ((nm (namestring path))
           (rel (subseq nm rootlen))
           (parts (split rel #\/))
           (area (if (>= (length parts) 2) (format nil "~a/~a" (first parts) (second parts)) (first parts)))
           (r (run-test path)) (cell (gethash area areas (list 0 0))))
      (if (eq r :skip) (incf skip)
          (progn (incf (second cell)) (incf tt) (when (eq r :pass) (incf (first cell)) (incf tp))
                 (setf (gethash area areas) cell))))
    (when (zerop (mod (- idx start) 2000)) (sb-ext:gc :full t)))
  (with-open-file (o out :direction :output :if-exists :append :if-does-not-exist :create)
    (dolist (a (sort (loop for k being the hash-keys of areas collect k) #'string<))
      (destructuring-bind (p tot) (gethash a areas) (format o "AREA~c~a~c~d~c~d~%" #\Tab a #\Tab p #\Tab tot)))
    (format o "SLICE~c~d~c~d~c~d~c~d~c~d~%" #\Tab start #\Tab count #\Tab tp #\Tab tt #\Tab skip))
  (format t "slice ~d:~d -> ~d/~d (~d skip)~%" start count tp tt skip)
  (sb-ext:exit :code 0))
