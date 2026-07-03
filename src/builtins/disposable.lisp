;;;; builtins/disposable.lisp — DisposableStack + SuppressedError
;;;; (+ Symbol.dispose / Symbol.asyncDispose well-known symbols).
;;;; The explicit-resource-management object API. The `using` statement is a
;;;; separate parser feature (out of scope here).
(in-package #:shuttle)

;;; The two well-known symbols live in specials so methods below can reference
;;; them (they are created in install-disposable, which runs after the kernel).
(defvar *symbol-dispose* nil)
(defvar *symbol-async-dispose* nil)

;;; ---------------------------------------------------------------------------
;;; Helpers
;;; ---------------------------------------------------------------------------
(defun dstack-proto-from-newtarget (new-target default-ctor intrinsic-proto)
  "GetPrototypeFromConstructor: read NEW-TARGET.prototype; if not an object,
   fall back to INTRINSIC-PROTO. DEFAULT-CTOR is the active function object used
   when NEW-TARGET is undefined (a direct [[Call]]-free construction)."
  (let* ((nt (if (and new-target (js-object-p new-target)) new-target default-ctor))
         (pp (and nt (js-get nt "prototype"))))
    (if (js-object-p pp) pp intrinsic-proto)))

(defun get-dispose-method (v)
  "GetDisposeMethod(V, sync-dispose): GetMethod(V, @@dispose). Returns the method
   (callable) or *undefined* if the property is null/undefined. Throws TypeError
   if present but not callable."
  (let ((m (js-get v *symbol-dispose*)))
    (cond ((js-null-or-undef m) *undefined*)
          ((js-callable-p m) m)
          (t (js-throw (make-native-error "TypeError" "@@dispose is not a function"))))))

(defun disposable-state (this)
  "RequireInternalSlot(this, [[DisposableState]]) -> the internal plist cell, or
   TypeError. Returns the CONS whose car is the state keyword and cdr the stack."
  (unless (and (js-object-p this)
               (getf (js-object-internal this) :disposable-state))
    (js-throw (make-native-error "TypeError" "receiver has no [[DisposableState]] internal slot")))
  this)

;;; ---------------------------------------------------------------------------
;;; SuppressedError
;;; ---------------------------------------------------------------------------
(defun install-suppressed-error (realm)
  "SuppressedError(error, suppressed, message): an Error subtype whose instances
   carry own `error` and `suppressed` (and optional `message`) properties."
  (let* ((error-ctor (js-get (realm-global realm) "Error"))
         (error-proto (and (js-object-p error-ctor) (js-get error-ctor "prototype")))
         (proto (make-object :proto (if (js-object-p error-proto) error-proto (realm-object-proto realm))))
         (ctor (native-function realm "SuppressedError"
                 (lambda (this args)
                   (suppressed-error-init realm proto this nil args)) 3)))
    (def-value proto "name" "SuppressedError")
    (def-value proto "message" "")
    (def-value proto "constructor" ctor)
    (def-value ctor "prototype" proto :writable nil :configurable nil)
    ;; SuppressedError.__proto__ === Error
    (when (js-object-p error-ctor) (setf (js-object-proto ctor) error-ctor))
    (setf (js-object-construct ctor)
          (lambda (args new-target)
            (let ((o (make-object :proto (dstack-proto-from-newtarget new-target ctor proto) :class "Error")))
              (suppressed-error-init realm proto o t args))))
    (define-global realm "SuppressedError" ctor)
    ctor))

(defun suppressed-error-init (realm proto this construct-p args)
  "Shared body for [[Call]] and [[Construct]]. When CONSTRUCT-P, THIS is a fresh
   instance; on plain-call build one. Property order: message (if defined),
   error, suppressed."
  (declare (ignore construct-p realm))
  (let* ((err (arg 0 args)) (sup (arg 1 args)) (msg (arg 2 args))
         (o (if (js-object-p this) this (make-object :proto proto :class "Error"))))
    (unless (js-undefined-p msg)
      (put o "message" (to-string msg) :enumerable nil :writable t :configurable t))
    (put o "error" err :enumerable nil :writable t :configurable t)
    (put o "suppressed" sup :enumerable nil :writable t :configurable t)
    o))

(defun make-suppressed-error (realm err suppressed)
  "Build a SuppressedError from CL side (dispose aggregation)."
  (let ((ctor (js-get (realm-global realm) "SuppressedError")))
    (if (and (js-object-p ctor) (js-object-construct ctor))
        (js-construct ctor (list err suppressed *undefined*))
        (make-native-error "Error" "suppressed"))))

;;; ---------------------------------------------------------------------------
;;; DisposableStack
;;; ---------------------------------------------------------------------------
(defun make-disposable-stack (realm proto)
  "OrdinaryCreateFromConstructor for DisposableStack: pending state, empty stack."
  (let ((o (make-object :proto proto :class "Object")))
    ;; :disposable-state is a cons (STATE . STACK); STATE ∈ (:pending :disposed),
    ;; STACK is a CL list of dispose callbacks (each a JS callable), top-of-stack
    ;; = head (LIFO on dispose).
    (setf (getf (js-object-internal o) :disposable-state) (cons :pending '()))
    o))

(defun ds-cell (this) (getf (js-object-internal (disposable-state this)) :disposable-state))
(defun ds-disposed-p (this) (eq (car (ds-cell this)) :disposed))
(defun ds-push (this cb) (push cb (cdr (ds-cell this))))

(defun install-disposable (realm)
  ;; ---- well-known symbols ----
  (unless *symbol-dispose* (setf *symbol-dispose* (make-js-symbol "Symbol.dispose")))
  (unless *symbol-async-dispose* (setf *symbol-async-dispose* (make-js-symbol "Symbol.asyncDispose")))
  (let ((sym-ctor (js-get (realm-global realm) "Symbol")))
    (when (js-object-p sym-ctor)
      (def-value sym-ctor "dispose" *symbol-dispose* :writable nil :configurable nil)
      (def-value sym-ctor "asyncDispose" *symbol-async-dispose* :writable nil :configurable nil)))
  ;; ---- DisposableStack.prototype ----
  (let* ((proto (make-object :proto (realm-object-proto realm)))
         (ctor (native-function realm "DisposableStack"
                 (lambda (this args) (declare (ignore this args))
                   (js-throw (make-native-error "TypeError"
                              "Constructor DisposableStack requires 'new'"))) 0)))
    (setf (js-object-construct ctor)
          (lambda (args new-target) (declare (ignore args))
            (make-disposable-stack realm (dstack-proto-from-newtarget new-target ctor proto))))
    (def-value ctor "prototype" proto :writable nil :configurable nil)
    (def-value proto "constructor" ctor)

    ;; use(value)
    (def-method realm proto "use" 1 (this args)
      (disposable-state this)
      (when (ds-disposed-p this)
        (js-throw (make-native-error "ReferenceError" "DisposableStack already disposed")))
      (let ((v (arg 0 args)))
        (if (js-null-or-undef v)
            v
            (progn
              (unless (js-object-p v)
                (js-throw (make-native-error "TypeError" "value is not an object")))
              (let ((method (get-dispose-method v)))
                (when (js-undefined-p method)
                  (js-throw (make-native-error "TypeError" "value has no @@dispose method")))
                (ds-push this (lambda () (js-call method v '())))
                v)))))

    ;; adopt(value, onDispose)
    (def-method realm proto "adopt" 2 (this args)
      (disposable-state this)
      (when (ds-disposed-p this)
        (js-throw (make-native-error "ReferenceError" "DisposableStack already disposed")))
      (let ((v (arg 0 args)) (on-dispose (arg 1 args)))
        (unless (js-callable-p on-dispose)
          (js-throw (make-native-error "TypeError" "onDispose is not a function")))
        (ds-push this (lambda () (js-call on-dispose *undefined* (list v))))
        v))

    ;; defer(onDispose)
    (def-method realm proto "defer" 1 (this args)
      (disposable-state this)
      (when (ds-disposed-p this)
        (js-throw (make-native-error "ReferenceError" "DisposableStack already disposed")))
      (let ((on-dispose (arg 0 args)))
        (unless (js-callable-p on-dispose)
          (js-throw (make-native-error "TypeError" "onDispose is not a function")))
        (ds-push this (lambda () (js-call on-dispose *undefined* '())))
        *undefined*))

    ;; dispose()
    (let ((dispose-fn
            (native-function realm "dispose"
              (lambda (this args) (declare (ignore args))
                (disposable-state this)
                (unless (ds-disposed-p this)
                  (dispose-resources this))
                *undefined*) 0)))
      (put proto "dispose" dispose-fn :enumerable nil :writable t :configurable t)
      ;; [Symbol.dispose] === dispose (same function object)
      (put proto *symbol-dispose* dispose-fn :enumerable nil :writable t :configurable t))

    ;; move()
    (def-method realm proto "move" 0 (this args)
      (disposable-state this)
      (when (ds-disposed-p this)
        (js-throw (make-native-error "ReferenceError" "DisposableStack already disposed")))
      (let ((new-stack (make-disposable-stack realm proto)))
        ;; move resources (preserve order), then mark this disposed
        (setf (cdr (ds-cell new-stack)) (cdr (ds-cell this)))
        (setf (cdr (ds-cell this)) '())
        (setf (car (ds-cell this)) :disposed)
        new-stack))

    ;; disposed getter
    (def-getter realm proto "disposed"
      (lambda (this args) (declare (ignore args))
        (disposable-state this)
        (js-bool (ds-disposed-p this))))

    ;; @@toStringTag
    (put proto (symbol-tostringtag realm) "DisposableStack"
         :enumerable nil :writable nil :configurable t)

    (define-global realm "DisposableStack" ctor))
  ;; ---- minimal AsyncDisposableStack (async plumbing out of scope) ----
  ;; A distinct constructor with its own [[AsyncDisposableState]] slot so that
  ;; DisposableStack.prototype methods correctly reject an AsyncDisposableStack
  ;; receiver (RequireInternalSlot [[DisposableState]] fails). Full async method
  ;; behaviour (disposeAsync/await) is a separate feature.
  (let* ((proto (make-object :proto (realm-object-proto realm)))
         (ctor (native-function realm "AsyncDisposableStack"
                 (lambda (this args) (declare (ignore this args))
                   (js-throw (make-native-error "TypeError"
                              "Constructor AsyncDisposableStack requires 'new'"))) 0)))
    (setf (js-object-construct ctor)
          (lambda (args new-target) (declare (ignore args))
            (let ((o (make-object :proto (dstack-proto-from-newtarget new-target ctor proto) :class "Object")))
              (setf (getf (js-object-internal o) :async-disposable-state) (cons :pending '()))
              o)))
    (def-value ctor "prototype" proto :writable nil :configurable nil)
    (def-value proto "constructor" ctor)
    (put proto (symbol-tostringtag realm) "AsyncDisposableStack"
         :enumerable nil :writable nil :configurable t)
    (define-global realm "AsyncDisposableStack" ctor)))

(defun dispose-resources (this)
  "DisposeResources: mark disposed, run callbacks in LIFO order aggregating
   errors into a SuppressedError chain. THIS.[[DisposableState]] cell's stack is
   already head=top (LIFO)."
  (let ((realm (symbol-value '*current-realm*))
        (cell (ds-cell this))
        (completion :normal) (completion-value nil))
    (setf (car cell) :disposed)
    (let ((stack (cdr cell)))
      (setf (cdr cell) '())
      ;; stack is head=most-recently-pushed = first to run (LIFO): iterate as-is.
      (dolist (cb stack)
        (handler-case (funcall cb)
          (shuttle-error (e)
            (let ((thrown (shuttle-error-value e)))
              (if (eq completion :throw)
                  (setf completion-value (make-suppressed-error realm thrown completion-value))
                  (setf completion :throw completion-value thrown)))))))
    (when (eq completion :throw)
      (js-throw completion-value))))

(register-builtin-installer 'install-suppressed-error)
(register-builtin-installer 'install-disposable)
