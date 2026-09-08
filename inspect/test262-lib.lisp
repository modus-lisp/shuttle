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

(defvar *printed* nil
  "Everything the test printed, newest last.  An ASYNC test reports its outcome by PRINTING --
doneprintHandle.js defines $DONE to print Test262:AsyncTestComplete or ...Failure -- so the only
way to score one is to capture that.")

(defun install-print (realm)
  "test262's async harness calls print(); shuttle has no such global, so async tests could not
even reach their own reporting.  This captures instead of writing."
  (define-global realm "print"
    (native-function realm "print"
      (lambda (this args) (declare (ignore this))
        (push (if args (to-string (first args)) "") *printed*)
        *undefined*)
      1)))

(defun run-test (path)
  "Score one test file: :pass / :fail / :skip (module/async/CanBlockIsFalse)."
  (let* ((src (slurp path)) (fm (frontmatter src)) (neg (fm-negative fm))
         (asyncp (fm-flag fm "async")))
    (when (fm-flag fm "CanBlockIsFalse") (return-from run-test :skip))
    (let ((*steps* 0) (*standard-output* (make-broadcast-stream)) (*printed* '()))
      (let ((outcome
              (handler-case
                  (sb-ext:with-timeout 20
                    (let ((realm (make-realm)))
                      (unless (fm-flag fm "raw")
                        (install-262 realm)
                        (install-print realm)
                        (run-code *default-harness* realm)
                        ;; doneprintHandle.js is IMPLICIT for an async test, the way assert.js and
                        ;; sta.js are for every test -- INTERPRETING.md says so and the tests do
                        ;; not list it.  Without it $DONE is undefined and every async test dies
                        ;; on its own reporting call.
                        (when asyncp (run-code (include-code "doneprintHandle.js") realm))
                        (dolist (inc (fm-list fm "includes")) (run-code (include-code inc) realm)))
                      (if (fm-flag fm "module")
                          ;; A MODULE TEST is loaded through the module pipeline, not compiled as
                          ;; a script: its imports have to resolve to the sibling _FIXTURE files
                          ;; the test ships with, so the host is rooted at the test's own
                          ;; directory.  The harness above is still SCRIPT code in the same realm,
                          ;; and a module environment's parent is the global one, so `assert` and
                          ;; friends are visible from inside the module exactly as they should be.
                          (eval-module realm (namestring (truename path))
                                       :host (make-file-module-host))
                          ;; onlyStrict tests must run in strict mode — prepend the directive
                          (let ((tsrc (if (fm-flag fm "onlyStrict")
                                          (concatenate 'string "\"use strict\";" (string #\Newline) src)
                                          src)))
                            (run-code (compile-toplevel tsrc) realm)))
                      ;; An async test has not finished when its last statement runs: it finishes
                      ;; when it calls $DONE, which happens from a promise job.  Drain, then read
                      ;; what it printed.  Silence means it never reported at all, which is a
                      ;; failure and not a pass -- the most important case to get right, since
                      ;; every broken async test is silent.
                      (if asyncp
                          (progn
                            (drain-microtasks)
                            (let ((out (find-if (lambda (l) (search "Test262:Async" l)) *printed*)))
                              (cond ((null out) :async-silent)
                                    ((search "Test262:AsyncTestComplete" out) :ok)
                                    (t :async-failed))))
                          :ok)))
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
