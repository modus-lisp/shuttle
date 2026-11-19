;;;; threads.lisp -- running shuttle on a thread whose stores into shared globals are refused.
;;;;
;;;; A realm build and a running script write shuttle's globals: the well-known symbols, the
;;;; per-realm prototype caches, the microtask queue, the interned string table, the step and
;;;; generator counters.  On SBCL that is merely racy between threads; on modus, whose threads
;;;; share no state, a worker's first such store is refused.  WITH-THREAD-STATE gives BODY its
;;;; own binding of every one of them, starting from the value the calling thread sees, so a
;;;; thread can build realms and run scripts -- a web page's whole JavaScript -- privately.
;;;; scribe:with-thread-state is the same idea for scribe's caches.

(in-package #:shuttle)

(defparameter *thread-state-vars*
  '(;; vm.lisp
    *current-realm* *current-module* *symbol-iterator* *current-generator* *generators-created*
    *live-generators* *generator-proto-cache* *symbol-to-string-tag* *symbol-async-iterator*
    *mtq* *weak-kept-alive* *promise-proto-cache* *promise-ctor-cache* *promise-global-installed*
    *symbol-species* *async-generator-proto-cache* *run-depth* *steps*
    ;; value.lisp
    *interned-strings* *new-target* *depth* *symbol-to-primitive*
    ;; module-runtime, bundle, resolve
    *module-host* *async-eval-counter* *json-realm* *packument-cache*
    ;; builtins: well-known symbols and per-realm prototypes, set as each realm is built
    *arraybuffer-proto* *symbol-is-concat-spreadable* *clock-fn* *dataview-proto*
    *intl-locale-proto* *symbol-dispose* *symbol-async-dispose* *intl-dtf-proto* *intl-dtf-ctor*
    *intl-legacy-symbol* *intl-namespace* *intl-collator-proto* *intl-segmenter-proto*
    *intl-segments-proto* *intl-segment-iterator-proto* *intl-displaynames-proto*
    *intl-durationformat-proto* *iterator-prototype* *array-iterator-prototype*
    *string-iterator-prototype* *intl-plural-proto* *intl-listformat-proto* *intl-rtf-proto*
    *intl-numberformat-proto* *nf-legacy-symbol* *rounding-negative* *sharedarraybuffer-proto*
    *temporal-plaindatetime-proto* *symbol-match* *symbol-replace* *symbol-search* *symbol-split*
    *symbol-match-all* *regexp-ctor* *regexp-proto* *temporal-namespace* *temporal-tostringtag*
    *temporal-duration-proto* *temporal-zoneddatetime-proto* *temporal-plaindate-proto*
    *temporal-instant-proto* *temporal-plainmonthday-proto* *temporal-plainyearmonth-proto*
    *temporal-plaintime-proto* *typedarray-proto* *ta-proto-by-name* *ta-ctor-by-name*
    *entropy-source* *ta-types*
    ;; the compiler's counters, should one escape its own binding
    *scope-depth* *ctor-field-stmts*)
  "Every shuttle global a realm build or a running script STORES into.  A new one belongs here:
   test/threads (a realm built and a script run on a modus worker) fails without it.")

(defun %thread-state-value (sym)
  "SYM's starting value on a new thread: the caller's, except for what is mutated in place --
   the interned-string table (copied: its entries stay valid, new ones go in the copy) and the
   microtask queue (a fresh one)."
  (let ((v (symbol-value sym)))
    (cond ((eq sym '*mtq*) (cons nil nil))
          ((hash-table-p v)
           (let ((h (make-hash-table :test (hash-table-test v) :size (max 16 (hash-table-count v)))))
             (maphash (lambda (k x) (setf (gethash k h) x)) v)
             h))
          (t v))))

(defmacro with-thread-state (() &body body)
  "BODY with every global shuttle writes (*THREAD-STATE-VARS*) bound for this thread alone, so it
   can build realms and run scripts on a thread that may not store into shared memory (a modus
   worker).  Values start as the caller's; JS objects made inside stay inside."
  ;; The unbound ones (*CURRENT-REALM* has no global value) go LAST and get no value: PROGV binds
  ;; them for this thread too, unbound, so a SETF inside sets this thread's binding.
  (let ((bound (gensym "BOUND")))
    `(let ((,bound (remove-if-not #'boundp *thread-state-vars*)))
       (progv (append ,bound (remove-if #'boundp *thread-state-vars*))
           (mapcar #'%thread-state-value ,bound)
         ,@body))))

(export 'with-thread-state)
