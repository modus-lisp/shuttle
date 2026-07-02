;;;; builtins/function-extra.lisp — Function.prototype / Function ctor edge cases
;;;; (bind/call/apply/toString/name/length + @@hasInstance). Overrides the kernel
;;;; install-function-proto where needed (installers run after the kernel).
(in-package #:shuttle)

;;; ---------------------------------------------------------------------------
;;; %ThrowTypeError% — the single, shared, frozen thrower used for the
;;; restricted "caller"/"arguments" accessors on Function.prototype (and on
;;; bound functions, which inherit them). One object identity across the realm.
;;; ---------------------------------------------------------------------------
(defun %function-extra-thrower (realm)
  (or (getf (realm-intrinsics realm) :throw-type-error)
      (let ((f (native-function realm "" (lambda (this args)
                                           (declare (ignore this args))
                                           (js-throw (make-native-error "TypeError"
                                                       "'caller', 'callee', and 'arguments' properties may not be accessed")))
                                 0)))
        ;; %ThrowTypeError% is a frozen (non-extensible) function with a
        ;; non-configurable/non-writable "length" 0 and name "".
        (put f "length" 0d0 :enumerable nil :writable nil :configurable nil)
        (put f "name" "" :enumerable nil :writable nil :configurable nil)
        (setf (js-object-extensible f) nil)
        (setf (getf (realm-intrinsics realm) :throw-type-error) f)
        f)))

;;; OrdinaryHasInstance(C, O): spec 7.3.19 / 20.2.3.6.
(defun ordinary-has-instance (c o)
  (unless (js-callable-p c) (return-from ordinary-has-instance *false*))
  ;; [[BoundTargetFunction]]: our bound functions stash the target under
  ;; :bound-target in the internal plist (set by the bind override below).
  (let ((bt (and (js-object-internal c) (getf (js-object-internal c) :bound-target))))
    (when bt (return-from ordinary-has-instance (js-bool (ordinary-instance-of o bt)))))
  (unless (js-object-p o) (return-from ordinary-has-instance *false*))
  (let ((p (js-get c "prototype")))    ; may throw (poisoned prototype getter)
    (unless (js-object-p p)
      (js-throw (make-native-error "TypeError" "prototype is not an object")))
    (js-bool (loop for cur = (js-get-proto o) then (js-get-proto cur)
                   do (when (not (js-object-p cur)) (return nil))
                      (when (eq cur p) (return t))))))

(defun ordinary-instance-of (o c)
  "InstanceofOperator with the default @@hasInstance semantics."
  (js-truthy (ordinary-has-instance c o)))

(defun install-function-extra (realm)
  (let* ((fp (realm-function-proto realm))
         (glob (realm-global realm))
         (sym-hasinst (let ((s (ignore-errors (js-get (js-get glob "Symbol") "hasInstance"))))
                        (and (js-symbol-p s) s)))
         (thrower (%function-extra-thrower realm)))

    ;; ---- Function.prototype is itself a callable that returns undefined ----
    ;; ([[Class]] "Function" -> Object.prototype.toString gives "[object Function]").
    (unless (js-object-call fp)
      (setf (js-object-call fp) (lambda (this args) (declare (ignore this args)) *undefined*)))
    (setf (js-object-class fp) "Function")
    ;; length (0) then name ("") in that order, matching built-in property order.
    (unless (js-get-own-property fp "length")
      (put fp "length" 0d0 :enumerable nil :writable nil :configurable t))
    (unless (js-get-own-property fp "name")
      (put fp "name" "" :enumerable nil :writable nil :configurable t))

    ;; ---- restricted "caller"/"arguments" accessors (%ThrowTypeError%) ----
    (put-accessor fp "caller" :get thrower :set thrower :enumerable nil :configurable t)
    (put-accessor fp "arguments" :get thrower :set thrower :enumerable nil :configurable t)

    ;; ---- Function.prototype[@@hasInstance] ----
    (when sym-hasinst
      (let ((f (native-function realm "[Symbol.hasInstance]"
                 (lambda (this args) (ordinary-has-instance this (arg 0 args))) 1)))
        (put fp sym-hasinst f :enumerable nil :writable nil :configurable nil)))

    ;; ---- call: FunctionPrototypeCall (IsCallable check) ----
    (def-method realm fp "call" 1 (this args)
      (unless (js-callable-p this)
        (js-throw (make-native-error "TypeError" "Function.prototype.call called on non-callable")))
      (js-call this (arg 0 args) (rest args)))

    ;; ---- apply: IsCallable check + CreateListFromArrayLike (non-object throws) ----
    (def-method realm fp "apply" 2 (this args)
      (unless (js-callable-p this)
        (js-throw (make-native-error "TypeError" "Function.prototype.apply called on non-callable")))
      (let ((ta (arg 0 args)) (arr (arg 1 args)))
        (if (js-null-or-undef arr)
            (js-call this ta '())
            (progn
              (unless (js-object-p arr)
                (js-throw (make-native-error "TypeError" "CreateListFromArrayLike called on non-object")))
              (js-call this ta (array-like-to-list arr))))))

    ;; ---- toString: TypeError on non-callable this; native-code form otherwise ----
    (def-method realm fp "toString" 0 (this args)
      (unless (js-callable-p this)
        (js-throw (make-native-error "TypeError" "Function.prototype.toString called on non-callable")))
      ;; Prefer the original source text when the compiler retained it (user
      ;; functions); otherwise emit the native-code form.
      (let ((src (and (js-object-internal this) (getf (js-object-internal this) :source-text))))
        (if (stringp src)
            src
            (concatenate 'string "function "
                         (let ((n (js-get this "name"))) (if (stringp n) n ""))
                         "() { [native code] }"))))

    ;; ---- bind: SetFunctionName/Length, no own prototype, bound-target slot ----
    (def-method realm fp "bind" 1 (this args)
      (let ((target this) (bound-this (arg 0 args)) (bound-args (rest args)))
        (unless (js-callable-p target)
          (js-throw (make-native-error "TypeError" "Bind must be called on a function")))
        (let* ((nargs (length bound-args))
               ;; SetFunctionLength: only own numeric "length" counts.
               (has-len (and (js-get-own-property target "length") t))
               (tlen (if has-len (js-get target "length") *undefined*))
               (blen (if (and has-len (floatp tlen))
                         (cond ((js-nan-p tlen) 0d0)
                               ((= tlen *inf*) *inf*)
                               ((= tlen *-inf*) 0d0)
                               (t (max 0d0 (- (with-js-floats (ftruncate tlen)) nargs))))
                         0d0))
               (tname (let ((n (js-get target "name"))) (if (stringp n) n "")))
               (f (native-function realm (concatenate 'string "bound " tname)
                    (lambda (ignored-this call-args) (declare (ignore ignored-this))
                      (js-call target bound-this (append bound-args call-args)))
                    0)))
          ;; Record the bound target for OrdinaryHasInstance / bound-name/length.
          (setf (getf (js-object-internal f) :bound-target) target)
          (put f "length" blen :enumerable nil :writable nil :configurable t)
          ;; name already set to "bound <tname>" by native-function; ensure attrs.
          (put f "name" (concatenate 'string "bound " tname)
               :enumerable nil :writable nil :configurable t)
          ;; A bound function has NO own "prototype" (native-function adds none).
          (when (js-object-construct target)
            (setf (js-object-construct f)
                  (lambda (call-args new-target)
                    ;; If newTarget is the bound function itself, retarget to the
                    ;; bound target (spec 10.4.1.2 step 5).
                    (js-construct target (append bound-args call-args)
                                  (if (eq new-target f) target new-target)))))
          f)))))

(register-builtin-installer 'install-function-extra)
