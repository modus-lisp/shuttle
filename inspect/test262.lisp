;;;; test262.lisp — run the vendored test262 slice and report a real pass-rate.
;;;; Positive test: passes iff it runs without throwing. Negative test: passes
;;;; iff it throws. Each test gets sta.js + assert.js (+ any `includes`)
;;;; prepended (the standard harness). module/async/raw flags are skipped.
;;;;   sbcl --script inspect/test262.lisp
(require :asdf)
(push (truename (merge-pathnames "../" (directory-namestring *load-truename*))) asdf:*central-registry*)
(asdf:load-system "shuttle")
(in-package #:shuttle)

(defparameter *root* (merge-pathnames "test262/" (directory-namestring *load-truename*)))
(defun slurp (p) (with-open-file (s p :external-format :utf-8)
                   (let ((o (make-string (file-length s)))) (subseq o 0 (read-sequence o s)))))
(defun split (str ch) (loop with start = 0 for p = (position ch str :start start)
                            collect (string-trim " " (subseq str start (or p (length str))))
                            while p do (setf start (1+ p))))

(defun frontmatter (src)
  (let ((s (search "/*---" src)) (e (search "---*/" src)))
    (if (and s e) (subseq src (+ s 5) e) "")))
(defun fm-list (fm key)
  (let ((p (search (format nil "~a:" key) fm)))
    (when p (let* ((lb (position #\[ fm :start p)) (nl (position #\Newline fm :start p)))
              (when (and lb (or (null nl) (< lb nl)))
                (let ((rb (position #\] fm :start lb)))
                  (when rb (remove "" (split (subseq fm (1+ lb) rb) #\,) :test #'string=))))))))
(defun fm-flag (fm flag) (let ((fs (fm-list fm "flags"))) (member flag fs :test #'string=)))
(defun fm-negative (fm) (search "negative:" fm))

(let ((harness (make-hash-table :test 'equal)))
  (flet ((inc (name) (or (gethash name harness)
                         (setf (gethash name harness)
                               (slurp (merge-pathnames (format nil "harness/~a" name) *root*))))))
    (defun build-source (body fm)
      (if (fm-flag fm "raw") body
          (format nil "~a~%~a~%~{~a~%~}~a"
                  (inc "sta.js") (inc "assert.js")
                  (mapcar #'inc (fm-list fm "includes")) body)))))

(defun run-test (path)
  "-> :pass :fail or :skip"
  (let* ((src (slurp path)) (fm (frontmatter src)) (neg (fm-negative fm)))
    (when (or (fm-flag fm "module") (fm-flag fm "async") (fm-flag fm "CanBlockIsFalse")) (return-from run-test :skip))
    (let ((threw (handler-case (progn (eval-script (make-realm) (build-source src fm)) nil)
                   (shuttle-error () :threw)
                   (error () :limit))))      ; CL error = a shuttle limitation (also "didn't run clean")
      (if neg (if (eq threw :threw) :pass :fail)
          (if threw :fail :pass)))))

(let ((dirs (make-hash-table :test 'equal)) (tp 0) (tt 0) (skipped 0))
  (dolist (path (sort (directory (merge-pathnames "test/**/*.js" *root*)) #'string< :key #'namestring))
    (unless (search "_FIXTURE" (namestring path))
      (let* ((dir (let ((n (namestring path))) (subseq n (length (namestring *root*)) (1+ (position #\/ n :from-end t)))))
             (r (run-test path)) (cell (gethash dir dirs (list 0 0))))
        (case r (:skip (incf skipped))
          (t (incf (second cell)) (incf tt) (when (eq r :pass) (incf (first cell)) (incf tp))
             (setf (gethash dir dirs) cell))))))
  (format t "~&== test262 (vendored slice) ==~%")
  (dolist (d (sort (loop for k being the hash-keys of dirs collect k) #'string<))
    (destructuring-bind (p n) (gethash d dirs)
      (format t "  ~3d/~3d  ~a~%" p n d)))
  (format t "  ----~%  TOTAL ~d/~d passing  (~,1f%)   [~d skipped: module/async]~%"
          tp tt (if (plusp tt) (* 100.0 (/ tp tt)) 0) skipped)
  (sb-ext:exit :code 0))
