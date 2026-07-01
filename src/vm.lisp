;;;; vm.lisp — the stack VM, environments, operator semantics, and the
;;;; function/closure machinery. JS functions and host (CL-backed) functions
;;;; both present as objects with [[Call]] — the seam weft calls across.
(in-package #:shuttle)

(defstruct (realm (:constructor %make-realm))
  object-proto function-proto array-proto
  string-proto number-proto boolean-proto symbol-proto
  symbol-registry                       ; string -> js-symbol (Symbol.for/keyFor)
  intrinsics                            ; plist: keyword -> js object (constructors etc.)
  global global-env)
(defvar *current-realm*)
(defun %obj-proto () (realm-object-proto *current-realm*))
(defun %fn-proto () (realm-function-proto *current-realm*))
(defun %arr-proto () (realm-array-proto *current-realm*))
(defun %intrinsic (key) (getf (realm-intrinsics *current-realm*) key))

;;; ---- ToObject: box a primitive into its wrapper object ----
(defun box-primitive (v)
  (let ((r *current-realm*))
    (cond
      ((stringp v)
       (let ((o (make-object :proto (realm-string-proto r) :class "String")))
         (setf (js-object-primitive o) v)
         ;; String exotic: character indices are own enumerable, non-writable,
         ;; non-configurable data properties.
         (dotimes (i (length v))
           (put o (princ-to-string i) (string (char v i))
                :enumerable t :writable nil :configurable nil))
         (put o "length" (float (length v) 1d0) :enumerable nil :writable nil :configurable nil)
         o))
      ((floatp v)
       (let ((o (make-object :proto (realm-number-proto r) :class "Number")))
         (setf (js-object-primitive o) v) o))
      ((or (eq v *true*) (eq v *false*))
       (let ((o (make-object :proto (realm-boolean-proto r) :class "Boolean")))
         (setf (js-object-primitive o) v) o))
      ((js-symbol-p v)
       (let ((o (make-object :proto (realm-symbol-proto r) :class "Symbol")))
         (setf (js-object-primitive o) v) o))
      (t (js-throw "Cannot box value")))))

;;; ---- environments ----
;;; A binding value of the TDZ sentinel means "declared but not yet initialized"
;;; (let/const temporal dead zone). CONSTS holds names that may not be reassigned.
(defvar *tdz* '#:tdz)                    ; unique uninitialized marker
(defstruct env vars parent consts)
(defun new-env (parent) (make-env :vars (make-hash-table :test 'equal) :parent parent))
(defun env-root (e) (loop while (env-parent e) do (setf e (env-parent e))) e)
(defun env-get (env name)
  "Return (values VALUE BOUND-P). BOUND-P nil means the name is not declared."
  (loop for e = env then (env-parent e) while e
        do (multiple-value-bind (v p) (gethash name (env-vars e)) (when p (return-from env-get (values v t)))))
  (values *undefined* nil))
(defun env-get-checked (env name)
  "Read a binding, throwing ReferenceError if not declared, or if still in TDZ."
  (multiple-value-bind (v p) (env-get env name)
    ;; lazily provide our minimal Promise global on first reference (a richer
    ;; builtins/promise.lisp would define it eagerly and win over this).
    (when (and (not p) (string= name "Promise") (boundp '*current-realm*) *current-realm*)
      (ensure-promise-global)
      (multiple-value-setq (v p) (env-get env name)))
    (cond ((not p) (js-throw (make-native-error "ReferenceError" (format nil "~a is not defined" name))))
          ((eq v *tdz*) (js-throw (make-native-error "ReferenceError"
                          (format nil "Cannot access '~a' before initialization" name))))
          (t v))))
(defun env-typeof (env name)
  (multiple-value-bind (v p) (env-get env name)
    (when (and (not p) (string= name "Promise") (boundp '*current-realm*) *current-realm*)
      (ensure-promise-global)
      (multiple-value-setq (v p) (env-get env name)))
    (cond ((not p) "undefined")
          ((eq v *tdz*) (js-throw (make-native-error "ReferenceError"
                          (format nil "Cannot access '~a' before initialization" name))))
          (t (js-typeof v)))))
(defun env-set (env name val)
  (loop for e = env then (env-parent e) while e
        do (when (nth-value 1 (gethash name (env-vars e)))
             (when (and (env-consts e) (member name (env-consts e) :test #'string=))
               (js-throw (make-native-error "TypeError" (format nil "Assignment to constant variable."))))
             (setf (gethash name (env-vars e)) val) (return-from env-set val)))
  (setf (gethash name (env-vars (env-root env))) val) val)              ; sloppy implicit global
(defun env-declare (env name val) (setf (gethash name (env-vars env)) val))
(defun env-declare-const (env name val) (setf (gethash name (env-vars env)) val)
  (pushnew name (env-consts env) :test #'string=))

;;; ---- object builders ----
(defun make-array-object (elems)
  (let ((o (make-object :proto (%arr-proto) :class "Array")))
    (loop for e in elems for i from 0 do (put o (princ-to-string i) e))
    ;; Array "length" is writable but non-enumerable and non-configurable.
    (put o "length" (float (length elems) 1d0)
         :enumerable nil :writable t :configurable nil)
    o))
(defun make-plain-object (pairs)
  (let ((o (make-object :proto (%obj-proto))))
    (loop for (k . v) in pairs do (put o (if (stringp k) k (to-string k)) v)) o))

(defun array-object-to-list (arr)
  "Read a dense array object's indexed elements 0..length-1 into a CL list."
  (let ((n (truncate (to-number (js-get arr "length")))))
    (loop for i from 0 below n collect (js-get arr (princ-to-string i)))))

(defun object-rest-copy (src taken)
  "Copy own enumerable string keys of SRC into a fresh object, excluding TAKEN."
  (let ((o (make-object :proto (%obj-proto))) (src (to-object src)))
    (when (js-object-p src)
      (dolist (k (js-own-keys src))
        (when (and (stringp k) (not (member k taken :test #'string=)))
          (let ((d (js-get-own-property src k)))
            (when (and d (prop-enumerable d))
              (put o k (js-get src k)))))))
    o))

(defun for-in-key-array (o)
  "Array of enumerable string keys of O and its prototype chain (deduped)."
  (if (js-object-p o)
      (let ((seen (make-hash-table :test 'equal)) (out '()))
        (loop for cur = o then (js-object-proto cur)
              while (js-object-p cur)
              do (dolist (k (js-own-keys cur))
                   (when (and (stringp k) (not (gethash k seen)))
                     (setf (gethash k seen) t)
                     (let ((d (js-get-own-property cur k)))
                       (when (and d (prop-enumerable d)) (push k out))))))
        (make-array-object (nreverse out)))
      (make-array-object '())))

;;; ---- iterator protocol (for-of, spread, Array.from) ----
(defvar *symbol-iterator* nil)          ; @@iterator well-known symbol (set at realm build)
(defun get-iterator (obj)
  (let ((o (to-object obj)))
    (let ((itf (and *symbol-iterator* (js-get o *symbol-iterator*))))
      (unless (js-callable-p itf)
        (js-throw (make-native-error "TypeError" (format nil "~a is not iterable" (ignore-errors (to-string obj))))))
      (let ((it (js-call itf o '())))
        (unless (js-object-p it) (js-throw (make-native-error "TypeError" "iterator is not an object")))
        it))))
(defun iterator-step (it)
  "Call it.next(); return the result record ({value,done})."
  (let ((next (js-get it "next")))
    (unless (js-callable-p next) (js-throw (make-native-error "TypeError" "iterator.next is not a function")))
    (let ((r (js-call next it '())))
      (unless (js-object-p r) (js-throw (make-native-error "TypeError" "iterator result is not an object")))
      r)))

(defun make-arguments-object (args)
  "A minimal (unmapped) arguments object: indexed elements + length + @@iterator."
  (let ((o (make-object :proto (%obj-proto) :class "Arguments")))
    (loop for a in args for i from 0 do (put o (princ-to-string i) a))
    (put o "length" (float (length args) 1d0) :enumerable nil)
    (when *symbol-iterator*
      (let ((av (realm-array-proto *current-realm*)))
        (put o *symbol-iterator* (js-get av *symbol-iterator*) :enumerable nil)))
    o))

(defun fn-home (fn) (getf (js-object-internal fn) :home))
(defun (setf fn-home) (v fn) (setf (getf (js-object-internal fn) :home) v))
(defun fn-super-ctor (fn) (getf (js-object-internal fn) :super-ctor))
(defun (setf fn-super-ctor) (v fn) (setf (getf (js-object-internal fn) :super-ctor) v))

(defun ordinary-bind-this (this)
  "OrdinaryCallBindThis for a NON-strict ordinary (:normal this-mode) function:
   undefined/null -> the realm global object; a primitive -> ToObject (boxed);
   an object passes through. (We don't track strict mode; sloppy is the default,
   matching the majority of non-strict test262 tests.)"
  (cond ((js-null-or-undef this)
         (if (boundp '*current-realm*) (realm-global (symbol-value '*current-realm*)) this))
        ((js-object-p this) this)
        (t (to-object this))))          ; box a primitive receiver

(defun make-js-function (code env &key kind lexical-this)
  "KIND: nil = ordinary function; :method = has [[HomeObject]] (super),
   :generator = a generator function; :class-base / :class-derived = a class ctor.
   LEXICAL-THIS: for an arrow (:lexical this-mode), the `this` captured at the
   arrow's DEFINITION site — the arrow ignores its caller's `this` and uses it."
  (let ((fn (make-object :proto (%fn-proto) :class "Function")))
    (put fn "length" (float (fn-declared-length (code-params code)) 1d0) :enumerable nil :writable nil)
    (put fn "name" (or (code-name code) "") :enumerable nil :writable nil :configurable t)
    (setf (js-object-call fn)
          ;; OrdinaryCallBindThis: :normal (ordinary/method) functions substitute
          ;; undefined/null -> globalThis and box a primitive receiver; :lexical
          ;; (arrow) functions use the this captured at their definition site.
          (macrolet ((bind (this) `(case (code-this-mode code)
                                     (:lexical lexical-this)          ; arrow: captured this
                                     (:strict ,this)                  ; strict: no substitution (undefined stays)
                                     (t (ordinary-bind-this ,this))))) ; sloppy: undefined/null -> global, primitive -> boxed
            (case kind
              (:generator (lambda (this args) (make-generator-object code env (bind this) args fn)))
              (:async (lambda (this args)
                        (let ((this (bind this)))
                          (handler-case (make-async-function-object code env this args fn)
                            (shuttle-error (e)
                              ;; a synchronous throw before the first await -> rejected promise
                              (let ((p (make-promise)))
                                (promise-settle p :rejected (shuttle-error-value e)) p))))))
              (:async-generator (lambda (this args) (make-async-generator-object code env (bind this) args fn)))
              (t (lambda (this args)
                   (let ((fenv (new-env env)))
                     (env-declare fenv "arguments" (make-arguments-object args))
                     (run code fenv (bind this) args fn)))))))
    ;; class constructors: only callable via `new`; the [[Construct]] initializes
    ;; the instance (derived ctors require super() to run the base first).
    (cond
      ((member kind '(:class-base :class-derived))
       ;; the real runner: super() and new both call this to run the ctor body.
       (setf (getf (js-object-internal fn) :ctor-run)
             (lambda (this args) (let ((fenv (new-env env)))
                                   (env-declare fenv "arguments" (make-arguments-object args))
                                   (run code fenv this args fn))))
       (setf (js-object-construct fn)
             (lambda (args new-target)
               (let* ((pp (js-get (or new-target fn) "prototype"))
                      (obj (make-object :proto (if (js-object-p pp) pp (%obj-proto)))))
                 (let ((r (funcall (getf (js-object-internal fn) :ctor-run) obj args)))
                   (if (js-object-p r) r obj)))))
       ;; class ctors are not plain-callable: throw on [[Call]]
       (setf (js-object-call fn)
             (lambda (this args) (declare (ignore this args))
               (js-throw (make-native-error "TypeError"
                          (format nil "Class constructor ~a cannot be invoked without 'new'"
                                  (or (code-name code) "")))))))
      ((member kind '(:async :async-generator)) nil)   ; async fns are not constructable
      ;; arrows and concise/accessor methods are not constructable: `new (()=>{})`
      ;; and `new ({m(){}}.m)` throw TypeError (no [[Construct]] / no .prototype).
      ((not (code-constructable code)) nil)
      (t
       (setf (js-object-construct fn)
             (lambda (args new-target) (declare (ignore new-target))
               (let* ((pp (js-get fn "prototype"))
                      (obj (make-object :proto (if (js-object-p pp) pp (%obj-proto)))))
                 (let ((r (funcall (js-object-call fn) obj args))) (if (js-object-p r) r obj)))))))
    ;; a fresh .prototype so `new` works and methods can be attached.
    ;; async (non-generator) functions and non-constructable fns (arrows/methods) don't get one.
    (unless (or (member kind '(:method :async)) (not (code-constructable code)))
      (let ((proto (make-object :proto (case kind
                                         (:generator (generator-prototype))
                                         (:async-generator (async-generator-prototype))
                                         (t (%obj-proto))))))
        (unless (member kind '(:generator :async-generator)) (put proto "constructor" fn :enumerable nil))
        (put fn "prototype" proto :enumerable nil
             :writable (not (member kind '(:generator :async-generator))))))
    fn))

(defun fn-declared-length (params)
  "The .length of a function: count leading params before the first default/rest."
  (let ((n 0))
    (dolist (p params n)
      (when (and (consp p) (member (car p) '(:default :rest))) (return n))
      (incf n))))

;;; ---- generators (thread-backed coroutines) ----
;;; A generator runs its body on a dedicated worker thread. At each `yield` the
;;; worker blocks on RESUME-SEM and the consumer thread proceeds; `.next(v)` hands
;;; V back and unblocks the worker. This gives true VM-frame suspend/resume without
;;; CPS-transforming the bytecode. Threads are cheap here (short-lived, gated).
(defstruct genstate
  thread
  (to-gen-sem (sb-thread:make-semaphore))     ; consumer -> generator (resume)
  (to-consumer-sem (sb-thread:make-semaphore)) ; generator -> consumer (yielded/done)
  sent                                        ; value passed into .next(v) / throw / return
  mode                                        ; :next :throw :return  (how to resume)
  yielded                                     ; value handed out at a yield
  (done nil)
  (started nil)
  (executing nil)                             ; t while resumed (re-entrant next/return/throw -> TypeError)
  error)                                      ; a shuttle-error to propagate to the consumer

(defvar *current-generator* nil)              ; the genstate the running thread belongs to
(defvar *generators-created* 0)               ; counter to periodically reclaim leaked threads
(defvar *live-generators* '())                ; suspended (non-done) genstates, newest first
(defparameter *max-live-generators* 300)      ; hard cap on concurrent worker threads

(defun terminate-generator (gs)
  "Force an abandoned suspended generator's worker to unwind and exit."
  (unless (genstate-done gs)
    (setf (genstate-done gs) t (genstate-mode gs) :terminate)
    (ignore-errors (sb-thread:signal-semaphore (genstate-to-gen-sem gs)))
    (let ((th (genstate-thread gs)))
      (when (and th (sb-thread:thread-alive-p th))
        (ignore-errors (sb-thread:join-thread th :timeout 1))))))

(defun terminate-all-generators ()
  "Force every live (suspended) generator's worker thread to unwind and exit.
   Called by the test harness between tests so abandoned generators — each
   holding a realm + a 2MB thread stack — can't accumulate into heap exhaustion."
  (when *live-generators*
    (dolist (gs *live-generators*) (ignore-errors (terminate-generator gs)))
    (setf *live-generators* '())))

(defun reap-generators ()
  "Drop finished generators from the registry; if still over the cap, forcibly
   terminate the oldest suspended workers (assumed abandoned by a prior test)."
  (setf *live-generators* (delete-if #'genstate-done *live-generators*))
  (when (> (length *live-generators*) *max-live-generators*)
    ;; oldest are at the tail; terminate down to half the cap
    (let* ((keep (floor *max-live-generators* 2))
           (rev (reverse *live-generators*))
           (kill (nthcdr keep rev)))
      (dolist (gs kill) (terminate-generator gs))
      (setf *live-generators* (delete-if #'genstate-done *live-generators*)))))

(define-condition generator-terminate (error) ())  ; unwinds an abandoned generator's thread

(defun gen-yield (value)
  "Called from inside a generator's worker thread at a `yield`. Hands VALUE to the
   consumer, blocks until resumed, and returns the sent value (or throws)."
  (let ((gs *current-generator*))
    (setf (genstate-yielded gs) value)
    (sb-thread:signal-semaphore (genstate-to-consumer-sem gs))
    (sb-thread:wait-on-semaphore (genstate-to-gen-sem gs))
    (case (genstate-mode gs)
      (:throw  (js-throw (genstate-sent gs)))
      (:return (throw 'generator-return (genstate-sent gs)))
      (:terminate (error 'generator-terminate))    ; abandoned: unwind the worker
      (t (genstate-sent gs)))))

(defvar *generator-proto-cache* nil)   ; alist (realm . %GeneratorPrototype%)
(defun generator-prototype ()
  "The shared %GeneratorPrototype% for the current realm (next/return/throw/@@it)."
  (let ((cell (assoc *current-realm* *generator-proto-cache*)))
    (if cell (cdr cell)
        (let ((gp (make-object :proto (or *iterator-prototype* (%obj-proto)))))
          (flet ((native (name fn) (let ((f (make-object :proto (%fn-proto) :class "Function")))
                                     (setf (js-object-call f) fn)
                                     (put f "name" name :enumerable nil :writable nil)
                                     (put gp name f :enumerable nil))))
            (native "next"   (lambda (this args) (generator-resume this :next (if args (car args) *undefined*))))
            (native "return" (lambda (this args) (generator-resume this :return (if args (car args) *undefined*))))
            (native "throw"  (lambda (this args) (generator-resume this :throw (if args (car args) *undefined*)))))
          (when *symbol-iterator*
            (let ((f (make-object :proto (%fn-proto) :class "Function")))
              (setf (js-object-call f) (lambda (this args) (declare (ignore args)) this))
              (put f "name" "[Symbol.iterator]" :enumerable nil :writable nil)
              (put gp *symbol-iterator* f :enumerable nil)))
          (push (cons *current-realm* gp) *generator-proto-cache*)
          gp))))

(defun instantiate-fn-env (code env this args fn)
  "Build the function environment for a split generator/async CODE and run its
   instantiation stream (param binding + hoisting) SYNCHRONOUSLY in the current
   thread. Returns the prepared environment. Errors here propagate to the CALLER."
  (let ((fenv (new-env env)))
    (env-declare fenv "arguments" (make-arguments-object args))
    (when (code-inst-instrs code)
      (%run (make-code :name (code-name code) :params (code-params code)
                       :instrs (code-inst-instrs code))
            fenv this args fn))
    fenv))

(defun make-generator-object (code env this args fn)
  "Create a generator object whose worker thread will run CODE. The object exposes
   next/return/throw and @@iterator (returns itself)."
  ;; keep leaked (abandoned, suspended) generator threads bounded (see reap).
  (incf *generators-created*)
  (when (zerop (mod *generators-created* 64)) (reap-generators))
  ;; FunctionDeclarationInstantiation runs SYNCHRONOUSLY here (before the generator
  ;; object exists): a throw in a default param / destructuring surfaces to the caller.
  (let ((fenv (instantiate-fn-env code env this args fn)))
   (let* ((gs (make-genstate))
         (gproto (let ((pp (js-get fn "prototype"))) (if (js-object-p pp) pp (generator-prototype))))
         (gobj (make-object :proto gproto :class "Generator"))
         (realm *current-realm*))
    (setf (getf (js-object-internal gobj) :genstate) gs)
    ;; the worker: waits for the first resume, then runs the body.
    (setf (genstate-thread gs)
          (sb-thread:make-thread
           (lambda ()
             (block worker
               (let ((*current-realm* realm) (*current-generator* gs)
                     (*steps* 0) (*run-depth* 1))
                 (sb-thread:wait-on-semaphore (genstate-to-gen-sem gs))
                 (handler-case
                     (progn
                       (when (eq (genstate-mode gs) :terminate) (return-from worker))
                       (let ((rv (catch 'generator-return
                                   (case (genstate-mode gs)
                                     (:throw (js-throw (genstate-sent gs)))
                                     (:return (genstate-sent gs))
                                     (t (run code fenv this args fn))))))
                         (setf (genstate-yielded gs) rv (genstate-done gs) t)))
                   (generator-terminate () (return-from worker))   ; abandoned: silent exit
                   (shuttle-error (e) (setf (genstate-error gs) e (genstate-done gs) t))
                   ;; ANY other serious condition (timeout, stack, host bug): mark done
                   ;; and surface as a JS error to the consumer — never let it quit the
                   ;; whole process (--disable-debugger would kill everything).
                   (serious-condition (e)
                     (setf (genstate-error gs)
                           (make-condition 'shuttle-error
                                           :value (make-native-error "Error"
                                                    (format nil "generator error: ~a" e)))
                           (genstate-done gs) t)))
                 (sb-thread:signal-semaphore (genstate-to-consumer-sem gs)))))
           :name "shuttle-generator"))
    (push gs *live-generators*)
    gobj)))

(defun generator-resume (gobj mode value)
  "Resume GOBJ's generator with MODE (:next/:throw/:return) and VALUE. Returns a
   result object {value, done}."
  (let ((gs (getf (js-object-internal gobj) :genstate)))
    (unless gs (js-throw (make-native-error "TypeError" "not a generator")))
    (when (genstate-done gs)
      ;; already finished: return/next -> {value: v, done:true}; throw -> throw
      (case mode
        (:throw (js-throw value))
        (:return (return-from generator-resume (iter-result value t)))
        (t (return-from generator-resume (iter-result *undefined* t)))))
    ;; re-entrant resume (e.g. the body calls its own .next/.return/.throw while
    ;; running) -> TypeError, per the "executing" generator state.
    (when (genstate-executing gs)
      (js-throw (make-native-error "TypeError" "Generator is already executing")))
    (setf (genstate-executing gs) t (genstate-mode gs) mode (genstate-sent gs) value)
    (sb-thread:signal-semaphore (genstate-to-gen-sem gs))
    (sb-thread:wait-on-semaphore (genstate-to-consumer-sem gs))
    (setf (genstate-executing gs) nil)
    (when (genstate-error gs)
      (let ((e (genstate-error gs))) (setf (genstate-error gs) nil) (error e)))
    (if (genstate-done gs)
        (iter-result (genstate-yielded gs) t)
        (iter-result (genstate-yielded gs) nil))))

(defun iter-result (value done)
  (let ((o (make-object :proto (%obj-proto))))
    (put o "value" value) (put o "done" (js-bool done)) o))

(defun yield-star-delegate (iterable)
  "yield* ITERABLE: drive the inner iterator, yielding each produced value and
   forwarding .next(sent) to it; return the iterator's final value."
  (let* ((it (get-iterator iterable))
         (next (js-get it "next"))
         (sent *undefined*))
    (loop
      (let ((r (js-call next it (list sent))))
        (unless (js-object-p r) (js-throw (make-native-error "TypeError" "iterator result is not an object")))
        (when (js-truthy (js-get r "done"))
          (return-from yield-star-delegate (js-get r "value")))
        (setf sent (gen-yield (js-get r "value")))))))

;;; ---- microtask queue ----
;;; A FIFO of thunks (CL closures). The top-level eval drains it after the script
;;; runs, so a resolved promise's reactions fire before the test's assertions read
;;; their side effects. There is no real event loop / timers here.
(defvar *symbol-to-string-tag* nil)   ; @@toStringTag (set at realm build if available)
(defvar *symbol-async-iterator* nil)  ; @@asyncIterator
(defvar *microtasks* nil)            ; a queue held as (head . tail) cons cells, or nil
(defvar *microtask-tail* nil)

(defun enqueue-microtask (thunk)
  (let ((cell (cons thunk nil)))
    (if *microtasks*
        (setf (cdr *microtask-tail*) cell *microtask-tail* cell)
        (setf *microtasks* cell *microtask-tail* cell))))

(defun drain-microtasks ()
  "Run queued microtasks to completion (each may enqueue more). Swallows JS
   throws from reactions (unhandled rejections have no observer here)."
  (loop while *microtasks* do
    (let ((thunk (car *microtasks*)))
      (setf *microtasks* (cdr *microtasks*))
      (unless *microtasks* (setf *microtask-tail* nil))
      (handler-case (funcall thunk)
        (shuttle-error () nil)
        (serious-condition () nil)))))

;;; ---- minimal Promise ----
;;; A promise object carries its state in :internal. States: :pending :fulfilled
;;; :rejected. Reactions are (on-fulfill . on-reject) CL-closure pairs queued while
;;; pending and flushed onto the microtask queue on settle.
(defvar *promise-proto-cache* nil)   ; alist (realm . %PromisePrototype%)
(defvar *promise-ctor-cache* nil)    ; alist (realm . Promise constructor)

(defun promisep (o)
  (and (js-object-p o) (member :promise-state (js-object-internal o))))
(defun promise-state (p) (getf (js-object-internal p) :promise-state))
(defun (setf promise-state) (v p) (setf (getf (js-object-internal p) :promise-state) v))
(defun promise-value (p) (getf (js-object-internal p) :promise-value))
(defun (setf promise-value) (v p) (setf (getf (js-object-internal p) :promise-value) v))
(defun promise-reactions (p) (getf (js-object-internal p) :promise-reactions))
(defun (setf promise-reactions) (v p) (setf (getf (js-object-internal p) :promise-reactions) v))

(defvar *promise-global-installed* '())   ; realms into which Promise has been installed
(defun ensure-promise-global ()
  "Install the Promise constructor as a global in the current realm (once). We own
   a minimal Promise here; a richer builtins/promise.lisp can supersede it later."
  (let ((realm *current-realm*))
    (unless (member realm *promise-global-installed*)
      (push realm *promise-global-installed*)
      (unless (nth-value 1 (env-get (realm-global-env realm) "Promise"))
        (install-promise-global realm)))))

(defun make-promise ()
  (ensure-promise-global)
  (let ((p (make-object :proto (promise-prototype) :class "Promise")))
    (setf (js-object-internal p)
          (list* :promise-state :pending :promise-value *undefined* :promise-reactions '()
                 (js-object-internal p)))
    p))

(defun promise-settle (p state value)
  "Transition a pending promise to :fulfilled/:rejected and schedule its reactions."
  (when (eq (promise-state p) :pending)
    (setf (promise-state p) state (promise-value p) value)
    (let ((reactions (nreverse (promise-reactions p))))
      (setf (promise-reactions p) '())
      (dolist (r reactions) (schedule-reaction p r)))))

(defun resolve-promise (p value)
  "Fulfill P with VALUE, but if VALUE is a thenable, adopt its state."
  (cond
    ((eq p value)
     (promise-settle p :rejected (make-native-error "TypeError" "Chaining cycle detected")))
    ((and (js-object-p value)
          (let ((then (ignore-errors (js-get value "then")))) (and (js-callable-p then) then)))
     (let ((then (js-get value "then")))
       ;; thenable: subscribe. Schedule the .then call as a microtask.
       (enqueue-microtask
        (lambda ()
          (let ((done nil))
            (flet ((res (this args) (declare (ignore this))
                     (unless done (setf done t) (resolve-promise p (if args (car args) *undefined*)))
                     *undefined*)
                   (rej (this args) (declare (ignore this))
                     (unless done (setf done t) (promise-settle p :rejected (if args (car args) *undefined*)))
                     *undefined*))
              (handler-case
                  (js-call then value (list (native-fn #'res) (native-fn #'rej)))
                (shuttle-error (e)
                  (unless done (setf done t) (promise-settle p :rejected (shuttle-error-value e))))))))) ))
    (t (promise-settle p :fulfilled value))))

(defun native-fn (fn &optional (len 1))
  "A bare callable JS object wrapping CL FN (this args) -> value."
  (let ((o (make-object :proto (%fn-proto) :class "Function")))
    (setf (js-object-call o) fn)
    (put o "length" (float len 1d0) :enumerable nil :writable nil :configurable t)
    (put o "name" "" :enumerable nil :writable nil :configurable t)
    o))

(defun schedule-reaction (p reaction)
  "Queue REACTION (on-fulfill . on-reject), each a CL closure of one arg, on the
   microtask queue against P's settled state."
  (destructuring-bind (on-fulfill . on-reject) reaction
    (let ((state (promise-state p)) (value (promise-value p)))
      (enqueue-microtask
       (lambda ()
         (if (eq state :fulfilled)
             (when on-fulfill (funcall on-fulfill value))
             (when on-reject  (funcall on-reject value))))))))

(defun promise-then (p on-fulfill on-reject)
  "Register CL-closure reactions (each (value)->_) on promise P. Returns nothing;
   used internally by the async driver and await."
  (let ((reaction (cons on-fulfill on-reject)))
    (if (eq (promise-state p) :pending)
        (push reaction (promise-reactions p))
        (schedule-reaction p reaction))))

(defun js-promise-resolve (value)
  "Promise.resolve(value): if VALUE is already a promise, return it; else a new
   fulfilled/adopting promise."
  (if (promisep value) value
      (let ((p (make-promise))) (resolve-promise p value) p)))

(defun promise-prototype ()
  (let ((cell (assoc *current-realm* *promise-proto-cache*)))
    (if cell (cdr cell)
        (let ((pp (make-object :proto (%obj-proto))))
          (flet ((native (name fn) (let ((f (make-object :proto (%fn-proto) :class "Function")))
                                     (setf (js-object-call f) fn)
                                     (put f "name" name :enumerable nil :writable nil :configurable t)
                                     (put pp name f :enumerable nil :configurable t :writable t))))
            (native "then" (lambda (this args)
                             (unless (promisep this)
                               (js-throw (make-native-error "TypeError" "Promise.prototype.then on non-promise")))
                             (let ((onf (and args (js-callable-p (car args)) (car args)))
                                   (onr (and (cdr args) (js-callable-p (cadr args)) (cadr args)))
                                   (result (make-promise)))
                               (promise-then this
                                 (lambda (v)
                                   (if onf
                                       (handler-case (resolve-promise result (js-call onf *undefined* (list v)))
                                         (shuttle-error (e) (promise-settle result :rejected (shuttle-error-value e))))
                                       (resolve-promise result v)))
                                 (lambda (v)
                                   (if onr
                                       (handler-case (resolve-promise result (js-call onr *undefined* (list v)))
                                         (shuttle-error (e) (promise-settle result :rejected (shuttle-error-value e))))
                                       (promise-settle result :rejected v))))
                               result)))
            (native "catch" (lambda (this args)
                              (let ((then (js-get this "then")))
                                (js-call then this (list *undefined* (if args (car args) *undefined*))))))
            (native "finally" (lambda (this args)
                                (let ((cb (and args (js-callable-p (car args)) (car args)))
                                      (then (js-get this "then")))
                                  (js-call then this
                                    (list (native-fn (lambda (this2 a) (declare (ignore this2))
                                                       (when cb (js-call cb *undefined* '()))
                                                       (if a (car a) *undefined*)))
                                          (native-fn (lambda (this2 a) (declare (ignore this2))
                                                       (when cb (js-call cb *undefined* '()))
                                                       (js-throw (if a (car a) *undefined*))))))))))
          (let ((tag (or *symbol-to-string-tag* (well-known-symbol "toStringTag"))))
            (when tag
              (put pp tag "Promise" :enumerable nil :writable nil :configurable t)))
          (push (cons *current-realm* pp) *promise-proto-cache*)
          pp))))

(defun install-promise-global (realm)
  "Install a minimal Promise constructor + statics into REALM's global. Idempotent
   caller (ensure-promise-global). Not installed if a builtins/promise.lisp already
   defined one."
  (let* ((*current-realm* realm)
         (proto (promise-prototype))
         (ctor (make-object :proto (%fn-proto) :class "Function")))
    (setf (js-object-call ctor)
          (lambda (this args) (declare (ignore this))
            (js-throw (make-native-error "TypeError" "Promise constructor requires new"))))
    (setf (js-object-construct ctor)
          (lambda (args new-target) (declare (ignore new-target))
            (let ((executor (if args (car args) *undefined*)))
              (unless (js-callable-p executor)
                (js-throw (make-native-error "TypeError" "Promise resolver is not a function")))
              (let ((p (make-promise)))
                (handler-case
                    (js-call executor *undefined*
                             (list (native-fn (lambda (th a) (declare (ignore th))
                                                (resolve-promise p (if a (car a) *undefined*)) *undefined*))
                                   (native-fn (lambda (th a) (declare (ignore th))
                                                (promise-settle p :rejected (if a (car a) *undefined*)) *undefined*))))
                  (shuttle-error (e) (promise-settle p :rejected (shuttle-error-value e))))
                p))))
    (put ctor "length" 1d0 :enumerable nil :writable nil :configurable t)
    (put ctor "name" "Promise" :enumerable nil :writable nil :configurable t)
    (put ctor "prototype" proto :enumerable nil :writable nil :configurable nil)
    (put proto "constructor" ctor :enumerable nil :writable t :configurable t)
    (flet ((static (name len fn)
             (let ((f (make-object :proto (%fn-proto) :class "Function")))
               (setf (js-object-call f) fn)
               (put f "name" name :enumerable nil :writable nil :configurable t)
               (put f "length" (float len 1d0) :enumerable nil :writable nil :configurable t)
               (put ctor name f :enumerable nil :writable t :configurable t))))
      (static "resolve" 1 (lambda (this args) (declare (ignore this))
                            (js-promise-resolve (if args (car args) *undefined*))))
      (static "reject" 1 (lambda (this args) (declare (ignore this))
                           (let ((p (make-promise)))
                             (promise-settle p :rejected (if args (car args) *undefined*)) p)))
      (static "all" 1 (lambda (this args) (declare (ignore this))
                        (promise-all (if args (car args) *undefined*) :all)))
      (static "allSettled" 1 (lambda (this args) (declare (ignore this))
                               (promise-all (if args (car args) *undefined*) :all-settled)))
      (static "race" 1 (lambda (this args) (declare (ignore this))
                         (promise-all (if args (car args) *undefined*) :race)))
      (static "any" 1 (lambda (this args) (declare (ignore this))
                        (promise-all (if args (car args) *undefined*) :any))))
    (define-global realm "Promise" ctor)
    ctor))

(defun promise-all (iterable mode)
  "Promise.all/allSettled/race/any over ITERABLE."
  (let* ((result (make-promise))
         (items (handler-case (iterable-to-list iterable)
                  (shuttle-error (e) (promise-settle result :rejected (shuttle-error-value e))
                    (return-from promise-all result))))
         (n (length items))
         (values (make-array n :initial-element *undefined*))
         (errors (make-array n :initial-element *undefined*))
         (remaining n))
    (when (zerop n)
      (case mode
        (:all (resolve-promise result (make-array-object '())))
        (:all-settled (resolve-promise result (make-array-object '())))
        (:any (promise-settle result :rejected (make-native-error "AggregateError" "All promises were rejected")))
        (:race nil))                        ; race over empty never settles
      (return-from promise-all result))
    (loop for item in items for i from 0 do
      (let ((idx i) (p (js-promise-resolve item)))
        (promise-then p
          (lambda (v)
            (case mode
              (:race (resolve-promise result v))
              (:any (resolve-promise result v))
              (:all (setf (aref values idx) v)
                    (when (zerop (decf remaining))
                      (resolve-promise result (make-array-object (coerce values 'list)))))
              (:all-settled
               (let ((o (make-object :proto (%obj-proto))))
                 (put o "status" "fulfilled") (put o "value" v) (setf (aref values idx) o))
               (when (zerop (decf remaining))
                 (resolve-promise result (make-array-object (coerce values 'list)))))))
          (lambda (e)
            (case mode
              (:race (promise-settle result :rejected e))
              (:all (promise-settle result :rejected e))
              (:any (setf (aref errors idx) e)
                    (when (zerop (decf remaining))
                      (promise-settle result :rejected (make-native-error "AggregateError" "All promises were rejected"))))
              (:all-settled
               (let ((o (make-object :proto (%obj-proto))))
                 (put o "status" "rejected") (put o "reason" e) (setf (aref values idx) o))
               (when (zerop (decf remaining))
                 (resolve-promise result (make-array-object (coerce values 'list))))))))))
    result))

(defun iterable-to-list (iterable)
  (let ((it (get-iterator iterable)) (out '()))
    (loop (let ((r (iterator-step it)))
            (when (js-truthy (js-get r "done")) (return))
            (push (js-get r "value") out)))
    (nreverse out)))

(defun well-known-symbol (name)
  "Look up a well-known symbol (e.g. \"asyncIterator\", \"toStringTag\") off the
   realm's Symbol constructor; nil if Symbol isn't installed."
  (multiple-value-bind (sym p) (env-get (realm-global-env *current-realm*) "Symbol")
    (when (and p (js-object-p sym))
      (let ((s (js-get sym name)))
        (when (js-symbol-p s) s)))))

(defun get-async-iterator (obj)
  "Get the async iterator of OBJ (@@asyncIterator), falling back to a sync
   iterator wrapped so its results present as {value,done}."
  (let ((o (to-object obj))
        (*symbol-async-iterator* (or *symbol-async-iterator* (well-known-symbol "asyncIterator"))))
    (let ((aif (and *symbol-async-iterator* (js-get o *symbol-async-iterator*))))
      (if (js-callable-p aif)
          (let ((it (js-call aif o '())))
            (unless (js-object-p it) (js-throw (make-native-error "TypeError" "async iterator is not an object")))
            it)
          ;; fall back to the sync iterator (its next() returns {value,done}; the
          ;; for-await loop awaits value/result which is fine for sync iterables)
          (get-iterator obj)))))

;;; ---- async functions ----
;;; An async function body runs on the SAME thread-coroutine machinery as a
;;; generator. `await x` is a suspension: the coroutine yields X to a driver, which
;;; resolves X as a promise and, when it settles, resumes the coroutine with the
;;; fulfilled value (or throws the rejection into it). The async call returns a
;;; Promise immediately; the body runs synchronously until the first await, then
;;; the remainder runs on microtasks.
(defstruct await-request value)   ; suspension marker: an `await`, vs. a plain yield
(defun async-await (value)
  "Called at an `await` inside an async coroutine worker. Hands VALUE out to the
   driver as an await request; resumes with the settled value or throws rejection."
  (gen-yield (make-await-request :value value)))

(defun make-async-function-object (code env this args fn)
  "Run an async function: create the coroutine, drive it, return the result Promise.
   Param binding runs synchronously; a throw there becomes a rejected promise (the
   make-js-function :async wrapper catches it)."
  (let* ((fenv (instantiate-fn-env code env this args fn))
         (gs (make-genstate))
         (result (make-promise))
         (realm *current-realm*))
    ;; the worker: like a generator, but there is no consumer calling .next — the
    ;; DRIVER pumps it. Each yield is an await request.
    (incf *generators-created*)
    (when (zerop (mod *generators-created* 64)) (reap-generators))
    (setf (genstate-thread gs)
          (sb-thread:make-thread
           (lambda ()
             (block worker
               (let ((*current-realm* realm) (*current-generator* gs) (*steps* 0) (*run-depth* 1))
                 (sb-thread:wait-on-semaphore (genstate-to-gen-sem gs))
                 (handler-case
                     (progn
                       (when (eq (genstate-mode gs) :terminate) (return-from worker))
                       (let ((rv (catch 'generator-return
                                   (run code fenv this args fn))))
                         (setf (genstate-yielded gs) rv (genstate-done gs) t)))
                   (generator-terminate () (return-from worker))
                   (shuttle-error (e) (setf (genstate-error gs) e (genstate-done gs) t))
                   (serious-condition (e)
                     (setf (genstate-error gs)
                           (make-condition 'shuttle-error
                                           :value (make-native-error "Error"
                                                    (format nil "async error: ~a" e)))
                           (genstate-done gs) t)))
                 (sb-thread:signal-semaphore (genstate-to-consumer-sem gs)))))
           :name "shuttle-async"))
    (push gs *live-generators*)
    ;; drive it: run to the first await/completion synchronously.
    (async-drive gs result :next *undefined*)
    result))

(defun async-drive (gs result mode value)
  "Resume the async coroutine GS with MODE/VALUE. If it awaits, subscribe to the
   awaited promise to resume later; if it completes, settle RESULT."
  (when (genstate-done gs)
    (return-from async-drive nil))
  (setf (genstate-mode gs) mode (genstate-sent gs) value)
  (sb-thread:signal-semaphore (genstate-to-gen-sem gs))
  (sb-thread:wait-on-semaphore (genstate-to-consumer-sem gs))
  (cond
    ((genstate-error gs)
     (let ((e (genstate-error gs))) (setf (genstate-error gs) nil)
       (promise-settle result :rejected (shuttle-error-value e))))
    ((genstate-done gs)
     (resolve-promise result (genstate-yielded gs)))
    (t
     ;; the coroutine awaited a value; wrap in a promise and subscribe to resume.
     (let* ((y (genstate-yielded gs))
            (awaited (js-promise-resolve (if (await-request-p y) (await-request-value y) y))))
       (promise-then awaited
         (lambda (v) (async-drive gs result :next v))
         (lambda (v) (async-drive gs result :throw v)))))))

;;; ---- async generators (minimal) ----
;;; An async generator's body yields values and awaits. Its next()/return()/throw()
;;; each return a Promise of {value,done}. We run the body on the coroutine and, per
;;; next(), pump until the next YIELD (resolving intervening awaits on the microtask
;;; queue), then resolve the promise with {value,done}.
(defun make-async-generator-object (code env this args fn)
  (incf *generators-created*)
  (when (zerop (mod *generators-created* 64)) (reap-generators))
  (let ((fenv (instantiate-fn-env code env this args fn)))   ; params bound synchronously
   (let* ((gs (make-genstate))
         (gproto (let ((pp (js-get fn "prototype"))) (if (js-object-p pp) pp (async-generator-prototype))))
         (gobj (make-object :proto gproto :class "AsyncGenerator"))
         (realm *current-realm*))
    (setf (getf (js-object-internal gobj) :genstate) gs)
    (setf (getf (js-object-internal gobj) :async-gen) t)
    (setf (genstate-thread gs)
          (sb-thread:make-thread
           (lambda ()
             (block worker
               (let ((*current-realm* realm) (*current-generator* gs) (*steps* 0) (*run-depth* 1))
                 (sb-thread:wait-on-semaphore (genstate-to-gen-sem gs))
                 (handler-case
                     (progn
                       (when (eq (genstate-mode gs) :terminate) (return-from worker))
                       (let ((rv (catch 'generator-return
                                   (case (genstate-mode gs)
                                     (:throw (js-throw (genstate-sent gs)))
                                     (:return (genstate-sent gs))
                                     (t (run code fenv this args fn))))))
                         (setf (genstate-yielded gs) rv (genstate-done gs) t)))
                   (generator-terminate () (return-from worker))
                   (shuttle-error (e) (setf (genstate-error gs) e (genstate-done gs) t))
                   (serious-condition (e)
                     (setf (genstate-error gs)
                           (make-condition 'shuttle-error
                                           :value (make-native-error "Error" (format nil "async generator error: ~a" e)))
                           (genstate-done gs) t)))
                 (sb-thread:signal-semaphore (genstate-to-consumer-sem gs)))))
           :name "shuttle-async-generator"))
    (push gs *live-generators*)
    gobj)))

(defun async-generator-step (gobj mode value)
  "next/return/throw on an async generator -> a Promise of {value,done}. Pumps the
   coroutine, resolving intervening awaits, until a yield or completion."
  (let ((gs (getf (js-object-internal gobj) :genstate))
        (result (make-promise)))
    (unless gs (promise-settle result :rejected (make-native-error "TypeError" "not an async generator"))
      (return-from async-generator-step result))
    (labels ((pump (m v)
               (when (genstate-done gs)
                 (case m
                   (:throw (promise-settle result :rejected v))
                   (t (resolve-promise result (iter-result (if (eq m :return) v *undefined*) t))))
                 (return-from pump))
               (setf (genstate-mode gs) m (genstate-sent gs) v)
               (sb-thread:signal-semaphore (genstate-to-gen-sem gs))
               (sb-thread:wait-on-semaphore (genstate-to-consumer-sem gs))
               (cond
                 ((genstate-error gs)
                  (let ((e (genstate-error gs))) (setf (genstate-error gs) nil)
                    (promise-settle result :rejected (shuttle-error-value e))))
                 ((genstate-done gs)
                  (resolve-promise result (iter-result (genstate-yielded gs) t)))
                 (t (let ((y (genstate-yielded gs)))
                      (if (await-request-p y)
                          ;; an await inside the async generator: settle then resume
                          (let ((awaited (js-promise-resolve (await-request-value y))))
                            (promise-then awaited
                              (lambda (rv) (pump :next rv))
                              (lambda (rv) (pump :throw rv))))
                          ;; a real yield: resolve the yielded value, then {value,done:false}
                          (let ((awaited (js-promise-resolve y)))
                            (promise-then awaited
                              (lambda (rv) (resolve-promise result (iter-result rv nil)))
                              (lambda (rv) (promise-settle result :rejected rv))))))))))
      (pump mode value))
    result))

(defvar *async-generator-proto-cache* nil)
(defun async-generator-prototype ()
  (let ((cell (assoc *current-realm* *async-generator-proto-cache*)))
    (if cell (cdr cell)
        (let ((gp (make-object :proto (%obj-proto))))
          (flet ((native (name fn) (let ((f (make-object :proto (%fn-proto) :class "Function")))
                                     (setf (js-object-call f) fn)
                                     (put f "name" name :enumerable nil :writable nil :configurable t)
                                     (put gp name f :enumerable nil :configurable t :writable t))))
            (native "next"   (lambda (this args) (async-generator-step this :next (if args (car args) *undefined*))))
            (native "return" (lambda (this args) (async-generator-step this :return (if args (car args) *undefined*))))
            (native "throw"  (lambda (this args) (async-generator-step this :throw (if args (car args) *undefined*)))))
          (let ((asit (or *symbol-async-iterator* (well-known-symbol "asyncIterator"))))
            (when asit
              (let ((f (make-object :proto (%fn-proto) :class "Function")))
                (setf (js-object-call f) (lambda (this args) (declare (ignore args)) this))
                (put f "name" "[Symbol.asyncIterator]" :enumerable nil :writable nil :configurable t)
                (put gp asit f :enumerable nil :configurable t))))
          (push (cons *current-realm* gp) *async-generator-proto-cache*)
          gp))))

;;; ---- classes ----
(defun build-class (ctor-code super derived env &optional cname)
  "Create the class: a constructor function + a prototype object. SUPER is the
   parent class value (undefined if none). Returns the constructor object."
  (let* ((super-present (not (eq super *undefined*)))
         (super-ctor (cond ((not super-present) nil)
                           ((eq super *null*) :null)
                           ((js-callable-p super) super)
                           (t (js-throw (make-native-error "TypeError" "Class extends value is not a constructor or null")))))
         (parent-proto (cond ((not super-present) (%obj-proto))
                             ((eq super *null*) *null*)
                             (t (let ((pp (js-get super "prototype")))
                                  (cond ((js-object-p pp) pp) ((eq pp *null*) *null*)
                                        (t (js-throw (make-native-error "TypeError" "Class extends prototype is not an object or null"))))))))
         (proto (make-object :proto parent-proto))
         (fn (make-js-function ctor-code env :kind (if derived :class-derived :class-base))))
    ;; wire prototype <-> constructor
    (put proto "constructor" fn :enumerable nil :writable t :configurable t)
    ;; replace the auto-created prototype with ours
    (js-define-own-property fn "prototype"
      (list :value proto :writable nil :enumerable nil :configurable nil))
    ;; constructor's [[Prototype]] chains to the parent constructor (static inherit)
    (when super-present
      (setf (js-object-proto fn) (if (eq super-ctor :null) (%fn-proto) super)))
    ;; the constructor's name is the class name (not "constructor")
    (js-define-own-property fn "name"
      (list :value (if cname cname "") :writable nil :enumerable nil :configurable t))
    ;; home object for super.* in the constructor = the prototype
    (setf (fn-home fn) proto)
    (setf (fn-super-ctor fn) (if (eq super-ctor :null) :null super-ctor))
    fn))

(defun run-super-ctor (super-ctor this args &optional new-target)
  "Execute super(...): run the parent class constructor's body on THIS.
   NEW-TARGET is the derived constructor currently running (for native bases whose
   [[Construct]] needs it). Returns the object to use as `this` (the base's
   [[Construct]] result, when it produces its own object)."
  (cond
    ((or (null super-ctor) (eq super-ctor :null))
     (js-throw (make-native-error "SyntaxError" "'super' keyword unexpected here")))
    (t
     ;; class ctors stash their raw runner under :ctor-run; native/builtin bases
     ;; expose [[Construct]] — invoke it (with the derived ctor as NewTarget) and
     ;; adopt its result as `this` (copying own props onto the pre-made instance
     ;; keeps the derived prototype chain the caller already installed).
     (let ((run-fn (getf (js-object-internal super-ctor) :ctor-run)))
       (cond
         (run-fn (funcall run-fn this args) this)
         ((js-object-construct super-ctor)
          (let ((r (funcall (js-object-construct super-ctor) args (or new-target super-ctor))))
            (if (js-object-p r)
                (progn
                  ;; adopt the base-created instance's own properties + internal
                  ;; slots + primitive onto THIS (which already carries the derived
                  ;; prototype the caller installed). Rebuild each own descriptor as
                  ;; a plist (js-get-own-property returns a PROP struct).
                  (dolist (k (js-own-keys r))
                    (let ((d (js-get-own-property r k)))
                      (when (prop-p d)
                        (js-define-own-property this k
                          (if (prop-accessor d)
                              (list :get (prop-get d) :set (prop-set d) :accessor t
                                    :enumerable (prop-enumerable d) :configurable (prop-configurable d))
                              (list :value (prop-value d) :writable (prop-writable d)
                                    :enumerable (prop-enumerable d) :configurable (prop-configurable d)))))))
                  (when (js-object-primitive r)
                    (setf (js-object-primitive this) (js-object-primitive r)))
                  (when (js-object-internal r)
                    (setf (js-object-internal this)
                          (append (js-object-internal r) (js-object-internal this))))
                  this)
                this)))
         (t
          (let ((c (js-object-call super-ctor)))
            (if c (progn (funcall c this args) this)
                (js-throw (make-native-error "TypeError" "super constructor is not callable"))))))))))

;;; ---- operators ----
(defun to-int32 (v)
  (let ((n (to-number v)))
    (if (or (js-nan-p n) (= n *inf*) (= n *-inf*)) 0
        (let ((m (mod (truncate n) #x100000000))) (if (>= m #x80000000) (- m #x100000000) m)))))

(defun js-mod (a b)
  (with-js-floats
    (let ((x (to-number a)) (y (to-number b)))
      (cond ((or (js-nan-p x) (js-nan-p y) (zerop y) (= (abs x) *inf*)) *nan*)
            ((= (abs y) *inf*) x) ((zerop x) x) (t (rem x y))))))

(defun js-relational (op a b)
  (let ((pa (to-primitive a :number)) (pb (to-primitive b :number)))
    (if (and (stringp pa) (stringp pb))
        (js-bool (funcall (cond ((string= op "<") #'string<) ((string= op ">") #'string>)
                                ((string= op "<=") #'string<=) (t #'string>=)) pa pb))
        (let ((x (to-number pa)) (y (to-number pb)))
          (if (or (js-nan-p x) (js-nan-p y)) *false*
              (js-bool (funcall (cond ((string= op "<") #'<) ((string= op ">") #'>)
                                      ((string= op "<=") #'<=) (t #'>=)) x y)))))))

(defun js-binop (op a b)
  (cond ((string= op "+") (js-add a b))
        ((string= op "-") (with-js-floats (- (to-number a) (to-number b))))
        ((string= op "*") (with-js-floats (* (to-number a) (to-number b))))
        ((string= op "/") (with-js-floats (/ (to-number a) (to-number b))))
        ((string= op "%") (js-mod a b))
        ((string= op "**") (with-js-floats (js-pow (to-number a) (to-number b))))
        ((string= op "<<") (let ((m (mod (logand (to-int32 a) #xFFFFFFFF) #x100000000))
                                 (s (logand (to-int32 b) 31)))
                             (let ((r (mod (ash m s) #x100000000)))
                               (float (if (>= r #x80000000) (- r #x100000000) r) 1d0))))
        ((string= op ">>") (float (ash (to-int32 a) (- (logand (to-int32 b) 31))) 1d0))
        ((string= op ">>>") (float (ash (to-uint32 a) (- (logand (to-int32 b) 31))) 1d0))
        ((string= op "===") (js-bool (js-strict-equal a b)))
        ((string= op "!==") (js-bool (not (js-strict-equal a b))))
        ((string= op "==") (js-bool (js-equal a b)))
        ((string= op "!=") (js-bool (not (js-equal a b))))
        ((member op '("<" ">" "<=" ">=") :test #'string=) (js-relational op a b))
        ((string= op "&") (float (logand (to-int32 a) (to-int32 b)) 1d0))
        ((string= op "|") (float (logior (to-int32 a) (to-int32 b)) 1d0))
        ((string= op "^") (float (logxor (to-int32 a) (to-int32 b)) 1d0))
        ((string= op "instanceof") (js-bool (js-instanceof a b)))
        ((string= op "in") (js-bool (and (js-object-p b) (js-has b (prop-key a)))))
        (t (js-throw (format nil "operator ~a not supported" op)))))

(defun js-instanceof (a b)
  (unless (js-callable-p b) (js-throw "Right-hand side of 'instanceof' is not callable"))
  (let ((proto (js-get b "prototype")))
    (and (js-object-p a)
         (loop for p = (js-get-proto a) then (js-get-proto p)
               while (js-object-p p) thereis (eq p proto)))))

(defun js-unop (op v)
  (cond ((string= op "!") (js-bool (not (js-truthy v))))
        ((string= op "-") (with-js-floats (- (to-number v))))
        ((string= op "+") (to-number v))
        ((string= op "~") (float (lognot (to-int32 v)) 1d0))
        ((string= op "void") *undefined*)
        ((string= op "typeof") (js-typeof v))
        (t (js-throw (format nil "unary ~a not supported" op)))))

;;; ---- the VM ----
(define-condition shuttle-timeout (error) ()   ; distinct from a JS throw
  (:report (lambda (c s) (declare (ignore c)) (format s "shuttle: instruction budget exceeded"))))
(declaim (type fixnum *steps* *max-steps*))
(defparameter *steps* 0) (defparameter *max-steps* 2000000)   ; per-run budget (guards infinite loops)

(defvar *run-depth* 0)    ; 0 = top-level script run; drain microtasks when it unwinds

(defun run (code env this &optional call-args fn-obj)
  (if (zerop *run-depth*)
      ;; outermost run of a script: run the body, then drain the microtask queue so
      ;; resolved-promise reactions (async .then) fire before the caller observes state.
      (let ((*run-depth* 1) (*microtasks* nil) (*microtask-tail* nil))
        (multiple-value-prog1 (%run code env this call-args fn-obj)
          (drain-microtasks)))
      (%run code env this call-args fn-obj)))

(defun %run (code env this &optional call-args fn-obj)
  (let ((instrs (code-instrs code)) (pc 0)
        (call-args (coerce call-args 'vector))
        (stack (make-array 64 :adjustable t :fill-pointer 0)) (completion *undefined*)
        (home (and fn-obj (fn-home fn-obj)))          ; [[HomeObject]] for super
        (super-ctor (and fn-obj (fn-super-ctor fn-obj)))
        (handlers '()))                      ; ((catch-pc . saved-sp) ...) for try/catch
    (macrolet ((push! (v) `(vector-push-extend ,v stack))
               (pop! () `(vector-pop stack))
               (peek! () `(aref stack (1- (fill-pointer stack)))))
      (loop
       (handler-case
        (loop
        (when (>= pc (length instrs)) (return-from %run completion))
        (when (>= (incf *steps*) *max-steps*) (error 'shuttle-timeout))
        (let* ((in (aref instrs pc)) (op (car in)) (a (cdr in)))
          (incf pc)
          (case op
            (:push-handler (push (list (first a) (fill-pointer stack) env) handlers))
            (:pop-handler (pop handlers))
            (:const (push! (first a)))
            (:get-var (push! (env-get-checked env (first a))))
            (:typeof-var (push! (env-typeof env (first a))))
            (:set-var (env-set env (first a) (peek!)))
            (:declare-var (env-declare env (first a) (pop!)))
            (:push-env (setf env (new-env env)))
            (:pop-env (setf env (env-parent env)))
            (:tdz-declare (env-declare env (first a) *tdz*))
            (:init-let (env-declare env (first a) (pop!)))
            (:init-const (env-declare-const env (first a) (pop!)))
            (:get-this (push! this))
            (:load-arg (let ((n (first a))) (push! (if (< n (length call-args)) (aref call-args n) *undefined*))))
            (:load-rest (let ((n (first a)))
                          (push! (make-array-object
                                  (loop for i from n below (length call-args) collect (aref call-args i))))))
            (:pop (pop!))
            (:dup (push! (peek!)))
            (:dup2 (let ((b (peek!)) (n (fill-pointer stack)))
                     (declare (ignore b))
                     (let ((x (aref stack (- n 2))) (y (aref stack (- n 1))))
                       (push! x) (push! y))))
            (:to-num (push! (to-number (pop!))))
            (:to-str (push! (to-string (pop!))))
            (:swap (let ((n (fill-pointer stack)))
                     (rotatef (aref stack (- n 1)) (aref stack (- n 2)))))
            (:rot3 (let ((n (fill-pointer stack)))   ; [a b c] -> [b c a]
                     (let ((a (aref stack (- n 3))))
                       (setf (aref stack (- n 3)) (aref stack (- n 2))
                             (aref stack (- n 2)) (aref stack (- n 1))
                             (aref stack (- n 1)) a))))
            (:nullish-short (let ((v (peek!)))   ; if top is null/undefined, jump to SHORT (leave it)
                              (when (or (eq v *null*) (eq v *undefined*)) (setf pc (first a)))))
            (:save-completion (setf completion (pop!)))
            (:bin (let ((b (pop!)) (x (pop!))) (push! (js-binop (first a) x b))))
            (:unary (push! (js-unop (first a) (pop!))))
            (:get-prop (let ((k (pop!)) (o (pop!))) (push! (js-get o k))))
            (:get-prop-c (push! (js-get (pop!) (first a))))
            (:set-prop (let ((v (pop!)) (k (pop!)) (o (pop!))) (js-set o k v) (push! v)))
            (:del-prop (let ((k (pop!)) (o (pop!)))
                         (push! (if (js-object-p o) (js-delete o k) *true*))))
            (:update-prop (let* ((delta (first a)) (prefix (second a))
                                 (k (pop!)) (o (pop!))
                                 (old (to-number (js-get o k)))
                                 (new (with-js-floats (+ old delta))))
                            (js-set o k new)
                            (push! (if prefix new old))))
            (:for-in-keys (push! (for-in-key-array (pop!))))
            (:get-iterator (push! (get-iterator (pop!))))
            (:iter-next (push! (iterator-step (pop!))))
            (:iter-rest (let ((it (pop!)) (out '()))
                          (loop (let ((r (iterator-step it)))
                                  (when (js-truthy (js-get r "done")) (return))
                                  (push (js-get r "value") out)))
                          (push! (make-array-object (nreverse out)))))
            (:object-rest (let ((src (pop!)) (taken (first a)))
                            (push! (object-rest-copy src taken))))
            (:call (let* ((args (loop repeat (first a) collect (pop!)))
                          (callee (pop!)) (thisv (pop!)))
                     (push! (js-call callee thisv (nreverse args)))))
            (:new (let* ((args (loop repeat (first a) collect (pop!))) (callee (pop!)))
                    (push! (js-construct callee (nreverse args)))))
            (:call-spread (let* ((argsarr (pop!)) (callee (pop!)) (thisv (pop!)))
                            (push! (js-call callee thisv (array-object-to-list argsarr)))))
            (:new-spread (let* ((argsarr (pop!)) (callee (pop!)))
                           (push! (js-construct callee (array-object-to-list argsarr)))))
            ;; LEXICAL-THIS = the enclosing frame's `this`, captured so an arrow
            ;; (:lexical this-mode) resolves `this` to its definition site.
            (:closure (push! (make-js-function (first a) env :lexical-this this)))
            (:genclosure (push! (make-js-function (first a) env :kind :generator :lexical-this this)))
            (:asyncclosure (push! (make-js-function (first a) env :kind :async :lexical-this this)))
            (:asyncgenclosure (push! (make-js-function (first a) env :kind :async-generator :lexical-this this)))
            (:yield (push! (gen-yield (pop!))))
            (:yield-star (push! (yield-star-delegate (pop!))))
            (:await (push! (async-await (pop!))))
            (:get-async-iterator (push! (get-async-iterator (pop!))))
            ;; ---- classes ----
            (:make-class (let* ((super (pop!)) (ctor-code (first a)) (derived (second a))
                                (cname (third a)))
                           (push! (build-class ctor-code super derived env cname))))
            (:class-method (let* ((fn (pop!)) (k (pop!)) (ctor (peek!))
                                  (kind (first a)) (static (second a))
                                  (target (if static ctor (js-get ctor "prototype"))))
                             (setf (fn-home fn) target)     ; [[HomeObject]] for super
                             (put fn "name" (if (stringp k) k (to-string k)) :enumerable nil :writable nil)
                             (case kind
                               (:get (js-define-own-property target (prop-key k)
                                       (list :get fn :accessor t :enumerable nil :configurable t)))
                               (:set (js-define-own-property target (prop-key k)
                                       (list :set fn :accessor t :enumerable nil :configurable t)))
                               (t (js-define-own-property target (prop-key k)
                                    (list :value fn :writable t :enumerable nil :configurable t))))))
            (:class-static-field (let* ((v (pop!)) (k (pop!)) (ctor (peek!)))
                                   (js-define-own-property ctor (prop-key k)
                                     (list :value v :writable t :enumerable t :configurable t))))
            (:super-get (let ((k (pop!)))
                          (let ((base (and (js-object-p home) (js-object-proto home))))
                            (push! (if (js-object-p base) (js-get base k this) *undefined*)))))
            (:super-get-method (let ((k (pop!)))
                                 (let ((base (and (js-object-p home) (js-object-proto home))))
                                   (push! this)            ; thisv
                                   (push! (if (js-object-p base) (js-get base k this) *undefined*)))))
            (:super-call (let ((args (nreverse (loop repeat (first a) collect (pop!)))))
                           (run-super-ctor super-ctor this args fn-obj) (push! this)))
            (:super-call-spread (let ((argsarr (pop!)))
                                  (run-super-ctor super-ctor this (array-object-to-list argsarr) fn-obj) (push! this)))
            (:array (push! (make-array-object (nreverse (loop repeat (first a) collect (pop!))))))
            (:object (push! (make-plain-object
                             (nreverse (loop repeat (first a) collect (let ((v (pop!)) (k (pop!))) (cons k v)))))))
            (:new-object (push! (make-object :proto (%obj-proto))))
            (:new-array (push! (make-array-object '())))
            (:def-prop (let ((v (pop!)) (k (pop!)))     ; obj key val -> obj
                         (js-define-own-property (peek!) (prop-key k)
                           (list :value v :writable t :enumerable t :configurable t))))
            (:def-getter (let ((fn (pop!)) (k (pop!)))  ; obj key fn -> obj
                           (js-define-own-property (peek!) (prop-key k)
                             (list :get fn :accessor t :enumerable t :configurable t))))
            (:def-setter (let ((fn (pop!)) (k (pop!)))
                           (js-define-own-property (peek!) (prop-key k)
                             (list :set fn :accessor t :enumerable t :configurable t))))
            (:set-proto (let ((pv (pop!)))              ; obj protoval -> obj
                          (when (or (js-object-p pv) (eq pv *null*))
                            (setf (js-object-proto (peek!)) pv))))
            (:def-spread (let ((src (pop!)))            ; obj src -> obj (copy own enumerable)
                           (let ((dst (peek!)))
                             (when (or (js-object-p src) (stringp src))
                               (let ((so (to-object src)))
                                 (dolist (k (js-own-keys so))
                                   (let ((d (js-get-own-property so k)))
                                     (when (and d (prop-enumerable d))
                                       (js-set dst k (js-get so k))))))))))
            (:array-spread (let ((iterable (pop!)) (idx (pop!)) (arr (pop!)))  ; arr idx iterable -> newidx
                             (let ((i (truncate (to-number idx))) (it (get-iterator iterable)))
                               (loop (let ((r (iterator-step it)))
                                       (when (js-truthy (js-get r "done")) (return))
                                       (js-set arr (princ-to-string i) (js-get r "value")) (incf i)))
                               (push! (float i 1d0)))))
            (:jmp (setf pc (first a)))
            (:jmp-if-false (unless (js-truthy (pop!)) (setf pc (first a))))
            (:jmp-if-true (when (js-truthy (pop!)) (setf pc (first a))))
            (:and-jmp (if (js-truthy (peek!)) (pop!) (setf pc (first a))))
            (:or-jmp (if (js-truthy (peek!)) (setf pc (first a)) (pop!)))
            (:nullish-jmp (let ((v (peek!)))    ; keep LHS if non-nullish, else eval RHS
                            (if (or (eq v *null*) (eq v *undefined*)) (pop!) (setf pc (first a)))))
            (:ret (return-from %run (pop!)))
            (:throw-op (js-throw (pop!)))
            (t (error "shuttle vm: bad op ~a" op)))))
        (shuttle-error (e)
          (if handlers
              (destructuring-bind (catch-pc saved-sp saved-env) (pop handlers)
                (setf (fill-pointer stack) saved-sp pc catch-pc env saved-env)  ; restore scope
                (vector-push-extend (shuttle-error-value e) stack))   ; thrown value -> catch param
              (error e))))))))
