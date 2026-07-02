;;;; test262-lib.lisp — shared test262 engine (loaded by both the full runner
;;;; test262.lisp and the per-subtree gate test262-sub.lisp). No driver here:
;;;; just *root*, the frontmatter parser, the harness cache, and run-test — the
;;;; single source of truth for how a test is scored.
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

(defun install-262 (realm)
  "Install a fallback test262 `$262` (evalScript + global) ONLY if the realm
   doesn't already have one. make-realm installs the full $262 (with createRealm +
   detachArrayBuffer via install-262-hooks); this must not clobber it."
  (when (js-truthy* (js-has (realm-global realm) "$262"))
    (return-from install-262))
  (let ((*current-realm* realm)
        (o (make-object :proto (realm-object-proto realm))))
    (put o "global" (realm-global realm) :enumerable t)
    (put o "evalScript"
         (native-function realm "evalScript"
           (lambda (this args) (declare (ignore this))
             (let ((src (if args (to-string (first args)) "")))
               (run-code (compile-toplevel src) realm)))
           1)
         :enumerable t)
    (define-global realm "$262" o)))

(defun run-test (path)
  "Score one test file: :pass / :fail / :skip (module/async/CanBlockIsFalse)."
  (let* ((src (slurp path)) (fm (frontmatter src)) (neg (fm-negative fm)))
    (when (or (fm-flag fm "module") (fm-flag fm "async") (fm-flag fm "CanBlockIsFalse")) (return-from run-test :skip))
    (let ((*steps* 0) (*standard-output* (make-broadcast-stream)))
      (let ((outcome
              (handler-case
                  (sb-ext:with-timeout 20
                    (let ((realm (make-realm)))
                      (unless (fm-flag fm "raw")
                        (install-262 realm)
                        (run-code *default-harness* realm)
                        (dolist (inc (fm-list fm "includes")) (run-code (include-code inc) realm)))
                      ;; onlyStrict tests must run in strict mode — prepend the directive
                      (let ((tsrc (if (fm-flag fm "onlyStrict")
                                      (concatenate 'string "\"use strict\";" (string #\Newline) src)
                                      src)))
                        (run-code (compile-toplevel tsrc) realm))
                      :ok))
                (sb-ext:timeout () :timeout)
                (shuttle-error () :threw)
                (shuttle-timeout () :timeout)
                (error () :limit)
                (storage-condition () :limit))))
        ;; reclaim any generator worker threads this test left suspended — else
        ;; they accumulate (realm + 2MB stack each) and eventually exhaust the heap.
        (ignore-errors (terminate-all-generators))
        (if neg (if (eq outcome :threw) :pass :fail)
            (if (eq outcome :ok) :pass :fail))))))
