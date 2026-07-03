;;;; builtins/bigint.lisp — the BigInt global (constructor + BigInt.prototype +
;;;; asIntN/asUintN). The bigint VALUE type is a CL integer (Numbers are always
;;;; double-float, so an integer is an unambiguous bigint); typeof/operators/
;;;; coercions live in the core files.
(in-package #:shuttle)

(defun number-to-bigint (n)
  "NumberToBigInt(N): N must be an integer-valued Number, else RangeError."
  (unless (floatp n) (js-throw (make-native-error "TypeError" "not a Number")))
  (when (or (js-nan-p n) (= n *inf*) (= n *-inf*) (/= n (with-js-floats (ftruncate n))))
    (js-throw (make-native-error "RangeError" "The number is not a safe integer")))
  (truncate n))

(defun this-bigint-value (this)
  "thisBigIntValue: a bigint primitive, or a BigInt wrapper object's primitive."
  (cond ((js-bigint-p this) this)
        ((and (js-object-p this) (js-bigint-p (js-object-primitive this))) (js-object-primitive this))
        (t (js-throw (make-native-error "TypeError" "not a BigInt")))))

(defun bigint-as-int-n (bits v)
  "BigInt.asIntN(bits, v): wrap V to a BITS-bit two's-complement signed integer."
  (if (zerop bits) 0
      (let ((m (mod v (ash 1 bits))))
        (if (>= m (ash 1 (1- bits))) (- m (ash 1 bits)) m))))

(defun bigint-as-uint-n (bits v)
  "BigInt.asUintN(bits, v): wrap V to a BITS-bit unsigned integer."
  (if (zerop bits) 0 (mod v (ash 1 bits))))

(defun install-bigint (realm)
  (let* ((*current-realm* realm)
         (obj-proto (%obj-proto))
         (proto (make-object :proto obj-proto :class "BigInt"))
         (ctor (native-function realm "BigInt"
                 (lambda (this args) (declare (ignore this))
                   ;; BigInt(value): a Number must be an integer (NumberToBigInt),
                   ;; else ToBigInt.
                   (let ((v (arg 0 args)))
                     (let ((prim (if (js-object-p v) (to-primitive v :number) v)))
                       (if (floatp prim) (number-to-bigint prim) (to-bigint prim)))))
                 1)))
    ;; not a constructor: `new BigInt()` -> TypeError
    (setf (js-object-construct ctor)
          (lambda (args new-target) (declare (ignore args new-target))
            (js-throw (make-native-error "TypeError" "BigInt is not a constructor"))))
    (def-value ctor "prototype" proto :writable nil :configurable nil)
    (def-value proto "constructor" ctor)
    (setf (getf (realm-intrinsics realm) :bigint-proto) proto)

    ;; ---- statics: asIntN / asUintN ----
    (def-method realm ctor "asIntN" 2 (this args)
      (let ((bits (to-index (arg 0 args))) (v (to-bigint (arg 1 args))))
        (bigint-as-int-n bits v)))
    (def-method realm ctor "asUintN" 2 (this args)
      (let ((bits (to-index (arg 0 args))) (v (to-bigint (arg 1 args))))
        (bigint-as-uint-n bits v)))

    ;; ---- prototype methods ----
    (def-method realm proto "toString" 0 (this args)
      (let ((b (this-bigint-value this)) (radix (arg 0 args)))
        (if (js-undefined-p radix)
            (bigint-to-string b 10)
            (let ((r (to-int-index radix)))
              (when (or (< r 2) (> r 36))
                (js-throw (make-native-error "RangeError" "toString() radix must be between 2 and 36")))
              (bigint-to-string b r)))))
    (def-method realm proto "toLocaleString" 0 (this args)
      (bigint-to-string (this-bigint-value this) 10))
    (def-method realm proto "valueOf" 0 (this args)
      (this-bigint-value this))

    ;; ---- @@toStringTag = "BigInt" ----
    (let ((tag (or *symbol-to-string-tag* (well-known-symbol "toStringTag"))))
      (when tag (put proto tag "BigInt" :enumerable nil :writable nil :configurable t)))

    (define-global realm "BigInt" ctor)
    ctor))

(register-builtin-installer 'install-bigint)
