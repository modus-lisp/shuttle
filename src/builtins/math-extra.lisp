;;;; builtins/math-extra.lisp — Math methods beyond the kernel set.
;;;; Kernel install-math already has abs/sqrt/sin/cos/tan/asin/acos/atan/exp/
;;;; sign/trunc/cbrt/floor/ceil/round/log/pow/atan2/hypot/max/min/random and the
;;;; constants. This file adds the rest. Get the Math object via
;;;;   (js-get (realm-global realm) "Math").
(in-package #:shuttle)

;;; Helpers: guard the domain edges test262 checks. All operate on doubles and
;;; keep NaN in → NaN out; sign/zero preservation handled per fn.

(defun %m-sinh (x)
  ;; ±0 → ±0, ±Inf → ±Inf, else sinh.
  (cond ((zerop x) x)
        ((= x *inf*) *inf*) ((= x *-inf*) *-inf*)
        (t (float (sinh x) 1d0))))

(defun %m-cosh (x)
  ;; cosh(±0)=1, cosh(±Inf)=+Inf.
  (cond ((= (abs x) *inf*) *inf*)
        (t (float (cosh x) 1d0))))

(defun %m-tanh (x)
  ;; ±0 → ±0, +Inf → 1, -Inf → -1.
  (cond ((zerop x) x)
        ((= x *inf*) 1d0) ((= x *-inf*) -1d0)
        (t (float (tanh x) 1d0))))

(defun %m-asinh (x)
  ;; ±0 → ±0, ±Inf → ±Inf.
  (cond ((zerop x) x)
        ((= x *inf*) *inf*) ((= x *-inf*) *-inf*)
        (t (float (asinh x) 1d0))))

(defun %m-acosh (x)
  ;; x < 1 → NaN, x = 1 → 0, +Inf → +Inf.
  (cond ((= x *inf*) *inf*)
        ((< x 1d0) *nan*)
        (t (float (acosh x) 1d0))))

(defun %m-atanh (x)
  ;; |x| > 1 → NaN, ±1 → ±Inf, ±0 → ±0.
  (cond ((zerop x) x)
        ((= x 1d0) *inf*) ((= x -1d0) *-inf*)
        ((> (abs x) 1d0) *nan*)
        (t (float (atanh x) 1d0))))

(defun %m-log2 (x)
  ;; x < 0 → NaN, ±0 → -Inf, +Inf → +Inf.
  (cond ((minusp x) *nan*)
        ((zerop x) *-inf*)
        ((= x *inf*) *inf*)
        (t (float (/ (log x) (log 2d0)) 1d0))))

(defun %m-log10 (x)
  (cond ((minusp x) *nan*)
        ((zerop x) *-inf*)
        ((= x *inf*) *inf*)
        (t ;; snap exact integer powers of 10 to their integer log (V8 parity):
           ;; the generic quotient rounds e.g. log10(1000) to 2.9999…96.
           (let ((r (float (/ (log x) (log 10d0)) 1d0)))
             (let ((rr (fround r)))
               (if (and (<= (abs (- r rr)) 1d-10)
                        (= x (expt 10d0 (truncate rr))))
                   rr
                   r))))))

(defun %m-log1p (x)
  ;; log(1+x): x < -1 → NaN, x = -1 → -Inf, ±0 → ±0, +Inf → +Inf.
  (cond ((zerop x) x)
        ((= x -1d0) *-inf*)
        ((< x -1d0) *nan*)
        ((= x *inf*) *inf*)
        (t (float (log (+ 1d0 x)) 1d0))))

(defun %m-expm1 (x)
  ;; exp(x)-1: ±0 → ±0, +Inf → +Inf, -Inf → -1.
  (cond ((zerop x) x)
        ((= x *inf*) *inf*) ((= x *-inf*) -1d0)
        (t (float (- (exp x) 1d0) 1d0))))

;;; ---- kernel overrides: domain / NaN / ±0 edges the kernel m1 macro misses ---

(defun %m-acos (x)
  ;; |x| > 1 → NaN (SBCL acos goes complex); acos(1)=+0, acos(-1)=π.
  (cond ((> (abs x) 1d0) *nan*)
        (t (float (acos x) 1d0))))

(defun %m-asin (x)
  ;; |x| > 1 → NaN; asin(±0)=±0.
  (cond ((zerop x) x)
        ((> (abs x) 1d0) *nan*)
        (t (float (asin x) 1d0))))

(defun %m-cbrt (x)
  ;; ±0 → ±0, ±Inf → ±Inf, negatives via -cbrt(|x|); NaN handled by caller.
  (cond ((zerop x) x)
        ((= x *inf*) *inf*) ((= x *-inf*) *-inf*)
        ((minusp x) (- (float (expt (- x) 1/3) 1d0)))
        (t (float (expt x 1/3) 1d0))))

;;; Round a double to IEEE-754 binary16 precision, returned as a double.
;;; Round-to-nearest, ties-to-even. ±0/±Inf/NaN pass through; overflow → ±Inf;
;;; subnormals and underflow handled exactly. SBCL has no native float16, so
;;; work on the exact rational value and re-quantise.
(defun %m-f16round (x)
  (cond
    ((js-nan-p x) *nan*)
    ((zerop x) x)                      ; ±0 preserved
    ((= x *inf*) *inf*) ((= x *-inf*) *-inf*)
    (t
     (let* ((neg (minusp x))
            (ax (abs x))
            ;; binary16: 5 exp bits (bias 15), 10 mantissa bits.
            ;; max finite = (2-2^-10)*2^15 = 65504; overflow → Inf.
            (max-f16 65504d0))
       (cond
         ((> ax max-f16)
          ;; round-half-to-even at the overflow boundary: values >= 65520 → Inf,
          ;; the halfway point 65520 rounds to Inf (even), below rounds to 65504.
          (if (>= ax 65520d0) (if neg *-inf* *inf*)
              (if neg (- max-f16) max-f16)))
         (t
          (let* ((r (rational ax))
                 ;; unbiased exponent e such that 2^e <= ax < 2^(e+1)
                 (e (floor (log ax 2d0))))
            ;; refine e exactly against the rational value
            (loop while (>= r (expt 2 (1+ e))) do (incf e))
            (loop while (< r (expt 2 e)) do (decf e))
            ;; smallest normal exponent for binary16 is -14; below that the
            ;; effective mantissa scale is fixed at 2^-24 (subnormal).
            (let* ((scale-exp (max (- e 10) -24))
                   (q (/ r (expt 2 scale-exp)))   ; value in units of 2^scale-exp
                   (fl (floor q))
                   (frac (- q fl))
                   ;; round half to even
                   (n (cond ((> frac 1/2) (1+ fl))
                            ((< frac 1/2) fl)
                            (t (if (evenp fl) fl (1+ fl)))))
                   (val (* n (expt 2 scale-exp)))
                   (d (float val 1d0)))
              (if neg (- d) d)))))))))

;;; Correctly-rounded conversion of an exact (possibly huge) rational to the
;;; nearest double, round-half-to-even. SBCL's (float rational 1d0) is NOT
;;; correctly rounded for some large magnitudes (off by 1 ULP), and overflows
;;; instead of yielding ±Inf — so do it by hand. Overflow past MAX_VALUE → ±Inf.
(defun %rational-to-double (r)
  (if (zerop r) 0d0
      (let* ((neg (minusp r))
             (a (abs r))
             ;; exponent e with 2^e <= a < 2^(e+1), found log-free via bit lengths
             ;; so values beyond MAX_VALUE don't overflow a float log estimate.
             (num (numerator a)) (den (denominator a))
             (e (- (integer-length num) (integer-length den) 1)))
        (loop while (>= a (expt 2 (1+ e))) do (incf e))
        (loop while (< a (expt 2 e)) do (decf e))
        ;; scale so the 53-bit mantissa integer lands in [2^52, 2^53)
        (let* ((se (- e 52))
               (q (/ a (expt 2 se)))
               (fl (floor q)) (fr (- q fl))
               (n (cond ((> fr 1/2) (1+ fl))
                        ((< fr 1/2) fl)
                        (t (if (evenp fl) fl (1+ fl)))))  ; ties → even
               (se2 se))
          (when (>= n (expt 2 53)) (setf n (ash n -1)) (incf se2))  ; carry
          (let ((d (handler-case (scale-float (coerce n 'double-float) se2)
                     (floating-point-overflow () *inf*)
                     (arithmetic-error () *inf*))))
            (if neg (- d) d))))))

;;; Math.sumPrecise(items): exact, correctly-rounded sum of an iterable of
;;; Numbers (TC39 proposal). Iterate with strict Number type-checking (no
;;; coercion — a non-Number throws TypeError and closes the iterator), classify
;;; Inf/NaN, then sum the finite values as exact rationals and round once.
(defun %sum-precise (realm items)
  (declare (ignore realm))
  (let ((it (get-iterator items))
        (has-pos-inf nil) (has-neg-inf nil) (has-nan nil)
        (sum 0)                  ; exact rational running sum of finite values
        (all-neg-zero t)         ; every element seen is -0 (⇒ result is -0)
        (count 0))
    ;; IteratorClose on abrupt: if the body throws, call it.return() (ignoring
    ;; any error it raises) then re-raise the original throw. Inlined rather than
    ;; using the %iter-close-on-abrupt macro (iterator.lisp loads after us).
    (handler-case
        (loop
          (let ((r (iterator-step it)))
            (when (js-truthy (js-get r "done")) (return))
            (let ((v (js-get r "value")))
              ;; strict: must already be a Number, no ToNumber coercion.
              (unless (floatp v)
                (js-throw (make-native-error "TypeError"
                            "Math.sumPrecise: iterable must contain only Numbers")))
              (incf count)
              (cond
                ((js-nan-p v) (setf has-nan t all-neg-zero nil))
                ((= v *inf*)  (setf has-pos-inf t all-neg-zero nil))
                ((= v *-inf*) (setf has-neg-inf t all-neg-zero nil))
                ((and (zerop v) (js-negative-zero-p v)) nil) ; -0: keep all-neg-zero
                (t (setf all-neg-zero nil)
                   (incf sum (rational v)))))))
      (shuttle-error (e)
        (let ((ret (and (js-object-p it) (js-get it "return"))))
          (when (and ret (not (js-null-or-undef ret)) (js-callable-p ret))
            (handler-case (js-call ret it '()) (shuttle-error () nil))))
        (error e)))
    (cond
      (has-nan *nan*)
      ((and has-pos-inf has-neg-inf) *nan*)
      (has-pos-inf *inf*)
      (has-neg-inf *-inf*)
      ((zerop count) -0d0)                 ; empty iterable → -0
      ((and (zerop sum) all-neg-zero) -0d0) ; only -0 values → -0
      ((zerop sum) 0d0)                    ; cancelled / had a +0 → +0
      ;; exact rational → correctly-rounded nearest double (±Inf on overflow).
      (t (%rational-to-double sum)))))

(defun install-math-extra (realm)
  (let ((math (js-get (realm-global realm) "Math")))
    (macrolet ((m1 (name fn)
                 `(def-method realm math ,name 1 (this args)
                    (with-js-floats
                      (let ((x (to-number (arg 0 args))))
                        (if (js-nan-p x) *nan* (,fn x)))))))
      (m1 "sinh" %m-sinh)   (m1 "cosh" %m-cosh)   (m1 "tanh" %m-tanh)
      (m1 "asinh" %m-asinh) (m1 "acosh" %m-acosh) (m1 "atanh" %m-atanh)
      (m1 "log2" %m-log2)   (m1 "log10" %m-log10)
      (m1 "log1p" %m-log1p) (m1 "expm1" %m-expm1)
      ;; kernel overrides — its plain (m1 name FN) has no domain/NaN/±0 guard,
      ;; so acos(2)/asin(2) went complex and cbrt lost ±0/±Inf.
      (m1 "acos" %m-acos) (m1 "asin" %m-asin) (m1 "cbrt" %m-cbrt))

    ;; -- Math.round: spec 21.3.2.28 (ties toward +Inf, preserve -0) ---------
    ;; The kernel's (ffloor (+ x 0.5)) gives +0 for -0 and for x in (-0.5,0],
    ;; and can overflow for huge x; both are observable.
    (def-method realm math "round" 1 (this args)
      (with-js-floats
        (let ((x (to-number (arg 0 args))))
          (cond
            ((or (js-nan-p x) (= (abs x) *inf*) (zerop x)) x)  ; NaN/±Inf/±0 → x
            ;; |x| >= 2^52: already an integer, no fractional part to round.
            ((>= (abs x) (expt 2d0 52)) x)
            ;; Round via floor + fractional part, NOT floor(x+0.5): the latter's
            ;; addition rounds 0.49999999999999994 up to 1.0 spuriously.
            (t (let* ((f (ffloor x))
                      (r (float (if (>= (- x f) 0.5d0) (+ f 1) f) 1d0)))
                 ;; x in (-0.5, 0) rounds to mathematical 0 but must be -0.
                 (if (and (zerop r) (minusp x)) -0d0 r)))))))

    ;; -- Math.atan2: NaN in either argument → NaN --------------------------
    ;; The kernel calls CL atan directly, which errors / mis-handles NaN.
    (def-method realm math "atan2" 2 (this args)
      (with-js-floats
        (let ((y (to-number (arg 0 args)))
              (x (to-number (arg 1 args))))
          (if (or (js-nan-p y) (js-nan-p x)) *nan*
              (float (atan y x) 1d0)))))

    ;; -- Math.hypot: Infinity dominates NaN; NaN otherwise -----------------
    ;; Spec: if any arg is ±Inf the result is +Inf even if another is NaN.
    ;; All args must be ToNumber-coerced (left→right) before the check.
    (def-method realm math "hypot" 2 (this args)
      (with-js-floats
        (let ((coerced (mapcar #'to-number args))
              (any-inf nil) (any-nan nil) (sum 0d0))
          (dolist (v coerced)
            (cond ((= (abs v) *inf*) (setf any-inf t))
                  ((js-nan-p v) (setf any-nan t))
                  (t (incf sum (* v v)))))
          (cond (any-inf *inf*)
                (any-nan *nan*)
                (t (float (sqrt sum) 1d0))))))

    ;; -- Math.max / Math.min: coerce ALL args before the NaN short-circuit --
    ;; Spec step 2 requires ToNumber on every element (observable via valueOf),
    ;; then the NaN check. The kernel returned early on the first NaN.
    (def-method realm math "max" 2 (this args)
      (with-js-floats
        (let ((coerced (mapcar #'to-number args)) (r *-inf*) (nan nil))
          (dolist (x coerced)
            (cond ((js-nan-p x) (setf nan t))
                  ((or (> x r) (and (zerop x) (zerop r) (js-negative-zero-p r)))
                   (setf r x))))
          (if nan *nan* r))))
    (def-method realm math "min" 2 (this args)
      (with-js-floats
        (let ((coerced (mapcar #'to-number args)) (r *inf*) (nan nil))
          (dolist (x coerced)
            (cond ((js-nan-p x) (setf nan t))
                  ((or (< x r) (and (zerop x) (zerop r) (js-negative-zero-p x)))
                   (setf r x))))
          (if nan *nan* r))))
    ;; clz32: count leading zeros of ToUint32(x), in 0..32 (0 → 32).
    (def-method realm math "clz32" 1 (this args)
      (with-js-floats
        (let ((n (to-uint32 (arg 0 args))))
          (float (- 32 (integer-length n)) 1d0))))
    ;; Math[@@toStringTag] = "Math" (writable:false, enumerable:false,
    ;; configurable:true). The kernel installs Math without it.
    (let ((tag (symbol-tostringtag realm)))
      (when (js-symbol-p tag)
        (put math tag "Math" :enumerable nil :writable nil :configurable t)))
    ;; sumPrecise: maximally-precise sum of an iterable of Numbers.
    (def-method realm math "sumPrecise" 1 (this args)
      (with-js-floats
        (%sum-precise realm (arg 0 args))))
    ;; f16round: round to nearest binary16, then widen back to double.
    (def-method realm math "f16round" 1 (this args)
      (with-js-floats
        (let ((x (to-number (arg 0 args))))
          (%m-f16round x))))
    ;; fround: round to nearest float32, then widen back to double.
    (def-method realm math "fround" 1 (this args)
      (with-js-floats
        (let ((x (to-number (arg 0 args))))
          (cond ((js-nan-p x) *nan*)
                ((zerop x) x)                       ; preserve ±0
                ((= (abs x) *inf*) x)
                (t (float (float x 1f0) 1d0))))))
    ;; imul: ToInt32(a) * ToInt32(b), truncated to a signed 32-bit int.
    (def-method realm math "imul" 2 (this args)
      (with-js-floats
        (let* ((a (to-int32 (arg 0 args)))
               (b (to-int32 (arg 1 args)))
               (p (mod (* a b) #x100000000)))
          (float (if (>= p #x80000000) (- p #x100000000) p) 1d0))))))

(register-builtin-installer 'install-math-extra)
