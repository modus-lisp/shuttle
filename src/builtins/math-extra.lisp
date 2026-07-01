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
      (m1 "log1p" %m-log1p) (m1 "expm1" %m-expm1))
    ;; clz32: count leading zeros of ToUint32(x), in 0..32 (0 → 32).
    (def-method realm math "clz32" 1 (this args)
      (with-js-floats
        (let ((n (to-uint32 (arg 0 args))))
          (float (- 32 (integer-length n)) 1d0))))
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
