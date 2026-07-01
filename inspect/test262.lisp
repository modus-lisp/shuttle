;;;; test262.lisp — run test262 and report a pass-rate, per area.
;;;;   SHUTTLE_TEST262=<checkout> sbcl --script inspect/test262.lisp
;;;; Defaults to the committed slice (inspect/test262/); point it at a full
;;;; checkout for the whole suite. Positive test passes iff it runs without
;;;; throwing; negative iff it throws. Prints a "SUMMARY <pass> <total>" line
;;;; and a per-area table; a per-instruction budget guards against infinite loops.
(require :asdf)
(push (truename (merge-pathnames "../" (directory-namestring *load-truename*))) asdf:*central-registry*)
(handler-bind ((warning #'muffle-warning)) (asdf:load-system "shuttle"))
(in-package #:shuttle)

(defparameter *root*
  (let ((e (sb-ext:posix-getenv "SHUTTLE_TEST262")))
    (if e (truename (merge-pathnames "" (pathname (format nil "~a/" e))))
        (merge-pathnames "test262/" (directory-namestring *load-truename*)))))

(defun slurp (p) (with-open-file (s p :external-format :utf-8)
                   (let ((o (make-string (file-length s)))) (subseq o 0 (read-sequence o s)))))
(defun split (str ch) (loop with start = 0 for p = (position ch str :start start)
                            collect (string-trim " " (subseq str start (or p (length str))))
                            while p do (setf start (1+ p))))
(defun frontmatter (src) (let ((s (search "/*---" src)) (e (search "---*/" src)))
                           (if (and s e) (subseq src (+ s 5) e) "")))
(defun fm-list (fm key)
  (let ((p (search (format nil "~a:" key) fm)))
    (when p (let* ((lb (position #\[ fm :start p)) (nl (position #\Newline fm :start p)))
              (when (and lb (or (null nl) (< lb nl)))
                (let ((rb (position #\] fm :start lb)))
                  (when rb (remove "" (split (subseq fm (1+ lb) rb) #\,) :test #'string=))))))))
(defun fm-flag (fm f) (member f (fm-list fm "flags") :test #'string=))
(defun fm-negative (fm) (search "negative:" fm))

(defvar *hcache* (make-hash-table :test 'equal))
(defun include-code (name)
  (or (gethash name *hcache*)
      (setf (gethash name *hcache*)
            (compile-toplevel (slurp (merge-pathnames (format nil "harness/~a" name) *root*))))))
(defparameter *default-harness*
  (compile-toplevel (concatenate 'string (slurp (merge-pathnames "harness/sta.js" *root*))
                                 (string #\Newline) (slurp (merge-pathnames "harness/assert.js" *root*)))))

(defun run-code (code realm)
  (let ((*current-realm* realm)) (with-js-floats (run code (realm-global-env realm) (realm-global realm)))))

(defun run-test (path)
  (let* ((src (slurp path)) (fm (frontmatter src)) (neg (fm-negative fm)))
    (when (or (fm-flag fm "module") (fm-flag fm "async") (fm-flag fm "CanBlockIsFalse")) (return-from run-test :skip))
    (let ((*steps* 0) (*standard-output* (make-broadcast-stream)))
      (let ((outcome
              (handler-case
                  (sb-ext:with-timeout 5
                    (let ((realm (make-realm)))
                      (unless (fm-flag fm "raw")
                        (run-code *default-harness* realm)
                        (dolist (inc (fm-list fm "includes")) (run-code (include-code inc) realm)))
                      (run-code (compile-toplevel src) realm)
                      :ok))
                (sb-ext:timeout () :timeout)
                (shuttle-error () :threw)
                (shuttle-timeout () :timeout)
                (error () :limit)
                (storage-condition () :limit))))
        (if neg (if (eq outcome :threw) :pass :fail)
            (if (eq outcome :ok) :pass :fail))))))

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
