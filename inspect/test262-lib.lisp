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

(defun fm-negative-type (fm)
  "The error constructor a negative test DECLARES it will throw.

Scoring a negative test on \"it threw something\" is how a suite flatters itself: a test that
wants a SyntaxError passes on a TypeError from an unrelated failure, and the engine gets credit
for a bug.  This is how dynamic-import/syntax appeared to pass 461 tests while import() was
throwing \"no module host is installed\" at every one of them."
  (let ((p (search "negative:" fm)))
    (when p
      (let ((tp (search "type:" fm :start2 p)))
        (when tp
          (let* ((start (+ tp 5))
                 (nl (or (position #\Newline fm :start start) (length fm)))
                 (raw (string-trim '(#\Space #\Tab #\Return) (subseq fm start nl))))
            (and (plusp (length raw)) raw)))))))

(defun fm-negative-phase (fm)
  (let ((p (search "negative:" fm)))
    (when p
      (let ((ph (search "phase:" fm :start2 p)))
        (when ph
          (let* ((start (+ ph 6))
                 (nl (or (position #\Newline fm :start start) (length fm)))
                 (raw (string-trim '(#\Space #\Tab #\Return) (subseq fm start nl))))
            (and (plusp (length raw)) raw)))))))

(defun thrown-error-name (v)
  "The NAME of a thrown JS error value, or NIL if it is not one."
  (and (js-object-p v)
       (or (let ((n (ignore-errors (js-get v "name")))) (and (stringp n) n))
           (let ((c (ignore-errors (js-get v "constructor"))))
             (and (js-object-p c)
                  (let ((n (ignore-errors (js-get c "name")))) (and (stringp n) n)))))))

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
         (neg-type (and neg (fm-negative-type fm)))
         (neg-phase (and neg (fm-negative-phase fm)))
         (thrown nil) (threw-before-eval nil)
         (asyncp (fm-flag fm "async")))
    (when (fm-flag fm "CanBlockIsFalse") (return-from run-test :skip))
    (let ((*steps* 0) (*standard-output* (make-broadcast-stream)) (*printed* '()))
      (let ((outcome
              (handler-case
                  (sb-ext:with-timeout 20
                    ;; HANDLER-BIND, not the HANDLER-CASE clause below: a handler-case handler runs
                    ;; AFTER the stack unwinds, by which point *CURRENT-REALM* is no longer bound
                    ;; and the error object cannot be read.  Every negative test then compared its
                    ;; declared type against NIL and failed.
                    (handler-bind ((shuttle-error
                                     (lambda (e)
                                       (setf thrown
                                             (ignore-errors
                                              (thrown-error-name (shuttle-error-value e)))))))
                    ;; *CURRENT-REALM* bound for the WHOLE test, not just while running: a
                    ;; SyntaxError is thrown by the PARSER, before any code runs, and an error
                    ;; built with no realm current has no prototype and therefore no `name` --
                    ;; so a negative test could never match the type it declared.
                    (let* ((realm (make-realm)) (*current-realm* realm))
                      (unless (fm-flag fm "raw")
                        (install-262 realm)
                        (install-print realm)
                        ;; EVERY test gets a module host, not just module tests: `import()` is an
                        ;; expression and works in ordinary script code, where there is no module
                        ;; to inherit a host from.  Rooted at the test's own directory, which is
                        ;; where its _FIXTURE files live.
                        (set-module-host realm (make-file-module-host
                                                :root (namestring
                                                       (make-pathname :name nil :type nil
                                                                      :version nil
                                                                      :defaults (truename path)))))
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
                          ;; Split so a PHASE can be told apart: parsing and linking both happen
                          ;; before a line of the module runs, which is what `phase: parse` and
                          ;; `phase: resolution` mean.  eval-module does all three at once.
                          (let* ((*module-host*
                                   (make-file-module-host
                                    :root (namestring (make-pathname :name nil :type nil
                                                                     :version nil
                                                                     :defaults (truename path)))))
                                 (*current-realm* realm))
                            (setf threw-before-eval t)
                            (let ((m (resolve-imported-module nil (namestring (truename path)))))
                              (link-module m)
                              (setf threw-before-eval nil)
                              (let ((pr (evaluate-module m)))
                                (drain-microtasks)
                                (when (eq (promise-state pr) :rejected)
                                  (js-throw (promise-value pr))))))
                          ;; onlyStrict tests must run in strict mode — prepend the directive
                          (let* ((tsrc (if (fm-flag fm "onlyStrict")
                                           (concatenate 'string "\"use strict\";" (string #\Newline) src)
                                           src))
                                 ;; compiled SEPARATELY so a throw here is known to be a parse-phase
                                 ;; error rather than something the program did once running
                                 (code (progn (setf threw-before-eval t)
                                              (prog1 (compile-toplevel tsrc)
                                                (setf threw-before-eval nil)))))
                            (run-code code realm)))
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
                          :ok))))
                (sb-ext:timeout () :timeout)
                (shuttle-error () :threw)
                (shuttle-timeout () :timeout)
                (error () :limit)
                (storage-condition () :limit))))
        ;; reclaim any generator worker threads this test left suspended — else
        ;; they accumulate (realm + 2MB stack each) and eventually exhaust the heap.
        (ignore-errors (terminate-all-generators))
        (if neg
            ;; A negative test passes only if it threw the error it NAMED.  The phase matters too:
            ;; `phase: parse` means the program must not have run at all, so the throw has to come
            ;; from compilation.
            (if (and (eq outcome :threw)
                     (or (null neg-type) (equal thrown neg-type))
                     ;; parse and resolution are both BEFORE evaluation; runtime is after.
                     (or (not (member neg-phase '("parse" "resolution") :test #'equal))
                         threw-before-eval))
                :pass :fail)
            (if (eq outcome :ok) :pass :fail))))))
