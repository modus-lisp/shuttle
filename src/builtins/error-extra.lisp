;;;; builtins/error-extra.lisp — AggregateError + Error extras (cause option,
;;;; array-iteration.lisp for the group convention.
;;;;
;;;; The Error hierarchy (Error + the 6 NativeErrors) is built by the kernel
;;;; (realm.lisp install-errors). This installer runs AFTER the kernel, so it:
;;;;   - marks every error instance with an [[ErrorData]] internal slot by
;;;;     re-wrapping each ctor's [[Construct]] / [[Call]] (the slot is what
;;;;     Error.isError and the stack getter key off — NOT the prototype chain);
;;;;   - honours the `options.cause` argument (InstallErrorCause) on all ctors;
;;;;   - adds the AggregateError global constructor;
;;;;   - adds Error.isError and the Error.prototype.stack accessor pair.
(in-package #:shuttle)

;;; ---- internal helpers ------------------------------------------------------

(defun error-data-p (o)
  "True iff O is an object carrying the [[ErrorData]] internal slot."
  (and (js-object-p o)
       (getf (js-object-internal o) :error-data)))

(defun mark-error-data (o)
  "Attach the [[ErrorData]] internal slot to O (run-super-ctor copies internal
   slots onto the derived `this`, so subclass instances inherit it)."
  (setf (getf (js-object-internal o) :error-data) t)
  o)

(defun proto-from-constructor (new-target default-proto)
  "GetPrototypeFromConstructor: NEW-TARGET.prototype if it's an object, else the
   intrinsic DEFAULT-PROTO. Reads via js-get so Proxy `prototype` traps run."
  (if (js-object-p new-target)
      (let ((p (js-get new-target "prototype")))
        (if (js-object-p p) p default-proto))
      default-proto))

(defun install-error-cause (o options)
  "InstallErrorCause: if OPTIONS is an object with own/inherited \"cause\", set a
   non-enumerable data \"cause\" on O. HasProperty + Get can be abrupt (Proxy /
   accessor) — let them propagate."
  (when (and (js-object-p options) (js-truthy* (js-has options "cause")))
    (put o "cause" (js-get options "cause") :enumerable nil :writable t :configurable t)))

;;; ---- installer -------------------------------------------------------------

(defun install-error-extra (realm)
  (let* ((base-ctor  (js-get (realm-global realm) "Error"))
         (base-proto (js-get base-ctor "prototype")))
    (rewrap-error-constructors realm base-ctor base-proto)
    (install-aggregate-error realm base-ctor base-proto)
    (install-error-is-error realm base-ctor)
    (install-error-stack-accessor realm base-proto)
    (install-error-tostring-guard realm base-proto)))

;;; ---------------------------------------------------------------------------
;;; Re-wrap Error + the 6 NativeErrors: [[ErrorData]] slot + options.cause.
;;; ---------------------------------------------------------------------------
;;; The kernel ctors ignore the 2nd argument and don't tag instances. We wrap
;;; both [[Construct]] and [[Call]] to:
;;;   - resolve the instance prototype from NewTarget (GetPrototypeFromCtor),
;;;   - run the kernel body (message handling) on that instance,
;;;   - tag it [[ErrorData]] and InstallErrorCause(options).
;;; `Error()` / `TypeError()` called WITHOUT new also produce a fresh tagged
;;; ErrorData object (spec: NewTarget undefined -> newTarget = active function).
(defun rewrap-error-constructors (realm base-ctor base-proto)
  (dolist (name '("Error" "TypeError" "RangeError" "SyntaxError"
                  "ReferenceError" "EvalError" "URIError"))
    (let* ((ctor  (js-get (realm-global realm) name))
           (proto (js-get ctor "prototype"))
           (body  (js-object-call ctor)))     ; kernel (this args) -> message handling
      (declare (ignorable base-ctor base-proto))
      (flet ((build (args new-target)
               (let* ((p (proto-from-constructor new-target proto))
                      (o (mark-error-data (make-object :proto p :class "Error"))))
                 ;; kernel body sets "message" from arg0 (skipping undefined)
                 (funcall body o (list (arg 0 args)))
                 (install-error-cause o (arg 1 args))
                 o)))
        (setf (js-object-construct ctor)
              (lambda (args new-target) (build args (or new-target ctor))))
        ;; [[Call]]: Error(...) with no `new` still returns a fresh ErrorData obj
        (setf (js-object-call ctor)
              (lambda (this args) (declare (ignore this)) (build args ctor)))))))

;;; ---------------------------------------------------------------------------
;;; AggregateError(errors, message?, options?)
;;; ---------------------------------------------------------------------------
(defun install-aggregate-error (realm base-ctor base-proto)
  (let* ((proto (make-object :proto base-proto))
         (ctor  (native-function realm "AggregateError"
                  (lambda (this args) (declare (ignore this))
                    (funcall (js-object-construct
                              (js-get (realm-global realm) "AggregateError"))
                             args nil))
                  2)))
    (def-value proto "name" "AggregateError")
    (def-value proto "message" "")
    (def-value proto "constructor" ctor)
    (def-value ctor "prototype" proto :writable nil :configurable nil)
    (setf (js-object-proto ctor) base-ctor)   ; getPrototypeOf(AggregateError) === Error
    (setf (js-object-construct ctor)
          (lambda (args new-target)
            (let* ((nt (or new-target ctor))
                   (p  (proto-from-constructor nt proto))
                   (o  (mark-error-data (make-object :proto p :class "Error"))))
              ;; Argument evaluation order (order-of-args-evaluation.js):
              ;; ToString(message) is observed BEFORE the errors iterable is
              ;; consumed. Compute the message string first, then iterate errors,
              ;; then install cause. Only *set* the message prop when defined.
              (let ((msg (unless (js-undefined-p (arg 1 args)) (to-string (arg 1 args)))))
                (let ((errs (iterable-to-list (arg 0 args))))
                  (put o "errors" (make-array-object errs)
                       :enumerable nil :writable t :configurable t))
                (when msg (put o "message" msg :enumerable nil)))
              ;; InstallErrorCause(options)
              (install-error-cause o (arg 2 args))
              o)))
    (define-global realm "AggregateError" ctor)))

(defun iterable-to-list (items)
  "IterableToList(items) using the default @@iterator: consume to a CL list."
  (let ((it (get-iterator items)) (out '()))
    (loop (let ((r (iterator-step it)))
            (when (js-truthy (js-get r "done")) (return))
            (push (js-get r "value") out)))
    (nreverse out)))

;;; ---------------------------------------------------------------------------
;;; Error.isError(x)  (proposal) — true iff x carries [[ErrorData]].
;;; ---------------------------------------------------------------------------
(defun install-error-is-error (realm base-ctor)
  (def-method realm base-ctor "isError" 1 (this args)
    (js-bool (error-data-p (arg 0 args)))))

;;; ---------------------------------------------------------------------------
;;; Error.prototype.stack accessor (error-stack-accessor proposal).
;;;   get: this not object -> TypeError; no [[ErrorData]] -> undefined;
;;;        else an implementation-defined string.
;;;   set: this not object -> TypeError; v not a String -> TypeError;
;;;        SameValue(this, Error.prototype) -> TypeError; then
;;;        SetterThatIgnoresPrototypeProperties: own desc undefined ->
;;;        CreateDataProperty(w/e/c), else Set(this,"stack",v,throw).
;;; ---------------------------------------------------------------------------
(defun install-error-stack-accessor (realm base-proto)
  (let ((getter (native-function realm "get stack"
                  (lambda (this args) (declare (ignore args))
                    (unless (js-object-p this)
                      (js-throw (make-native-error "TypeError" "Error.prototype.stack getter called on non-object")))
                    (if (error-data-p this) "" *undefined*))
                  0))
        (setter (native-function realm "set stack"
                  (lambda (this args)
                    (unless (js-object-p this)
                      (js-throw (make-native-error "TypeError" "Error.prototype.stack setter called on non-object")))
                    (let ((v (arg 0 args)))
                      (unless (stringp v)
                        (js-throw (make-native-error "TypeError" "Error.prototype.stack value must be a string")))
                      (when (eq this base-proto)
                        (js-throw (make-native-error "TypeError" "Cannot set stack on Error.prototype")))
                      (if (js-get-own-property this "stack")
                          ;; existing own property: Set(this,"stack",v,throw)
                          (unless (js-truthy* (js-set this "stack" v this))
                            (js-throw (make-native-error "TypeError" "Cannot set stack")))
                          ;; no own property: CreateDataProperty w/e/c
                          (unless (js-define-own-property this "stack"
                                    (list :value v :writable t :enumerable t :configurable t))
                            (js-throw (make-native-error "TypeError" "Cannot create stack property"))))
                      *undefined*))
                  1)))
    (put-accessor base-proto "stack" :get getter :set setter
                  :enumerable nil :configurable t)))

;;; ---------------------------------------------------------------------------
;;; Error.prototype.toString receiver guard (invalid-receiver test): throw
;;; TypeError when `this` is not an object. Kernel's toString reads name/message
;;; off primitives without complaint; re-wrap it to add the object check while
;;; preserving the "name: message" formatting.
;;; ---------------------------------------------------------------------------
(defun install-error-tostring-guard (realm base-proto)
  (def-method realm base-proto "toString" 0 (this args)
    (unless (js-object-p this)
      (js-throw (make-native-error "TypeError" "Error.prototype.toString called on non-object")))
    (let* ((name (let ((n (js-get this "name"))) (if (js-undefined-p n) "Error" (to-string n))))
           (msg  (let ((m (js-get this "message"))) (if (js-undefined-p m) "" (to-string m)))))
      (cond ((string= name "") msg)
            ((string= msg "") name)
            (t (concatenate 'string name ": " msg))))))

(register-builtin-installer 'install-error-extra)
