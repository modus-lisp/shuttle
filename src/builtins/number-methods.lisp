;;;; builtins/number-methods.lisp — Number.prototype methods beyond the kernel.
;;;; Kernel install-number has valueOf/toString/toFixed + the statics/constants.
;;;; This file adds toPrecision/toExponential/toLocaleString and hardens edges.
;;;; Number.prototype = (realm-number-proto realm).
(in-package #:shuttle)

;;; --- Significant-digit extraction via exact rationals ---------------------
;;; For a positive finite double X and an integer P>=1, return (values DIGITS E)
;;; where DIGITS is a P-character decimal string of significant digits and E is
;;; the base-10 exponent such that the represented value is
;;;   d1.d2d3...dP × 10^E  (i.e. n × 10^(E-P+1) with n = the integer DIGITS).
;;; Rounding is round-half-away-from-zero (ties toward the larger magnitude, per
;;; the ECMAScript "n × 10^(e-f) is larger" tie rule).
(defun %sig-digits (x p)
  (let* ((r (rational x))
         ;; e = floor(log10(x)), refined exactly (log gives only an estimate).
         (e (floor (log x 10d0))))
    (loop while (>= r (expt 10 (1+ e))) do (incf e))
    (loop while (< r (expt 10 e)) do (decf e))
    (flet ((round-scaled (ee)
             ;; round r/10^(ee-p+1) half-up (away from zero) to nearest integer
             (let* ((q (/ r (expt 10 (- ee (1- p)))))
                    (fl (floor q)))
               (if (>= (- q fl) 1/2) (1+ fl) fl))))
      (let ((n (round-scaled e)))
        ;; Rounding at the boundary can push n up to 10^p (e.g. 9.99→10); carry.
        (when (>= n (expt 10 p))
          (incf e) (setf n (round-scaled e)))
        (values (format nil "~d" n) e)))))

;;; Assemble exponential-notation output from a significant-digit string and its
;;; base-10 exponent E: "d1.d2..dP" with the fractional part present only when
;;; more than one digit, then "e", the sign of E, and |E|.
(defun %exp-string (digits e)
  (let ((frac (if (> (length digits) 1)
                  (concatenate 'string "." (subseq digits 1))
                  "")))
    (format nil "~a~ae~a~d"
            (subseq digits 0 1) frac (if (minusp e) "-" "+") (abs e))))

(defun install-number-methods (realm)
  (let ((np (realm-number-proto realm)))
    (declare (ignorable np))
    ;; %Number.prototype% has [[NumberData]] = +0, but the kernel object leaves
    ;; its primitive NIL, so this-number would reject it. Treat that receiver as
    ;; +0 (any other non-Number still throws through this-number).
    (flet ((this-num (this)
             (if (and (eq this np) (null (js-object-primitive this)))
                 0d0
                 (this-number this))))

    ;; -- Number.prototype.toExponential(fractionDigits) --------------------
    (def-method realm np "toExponential" 1 (this args)
      (let* ((x (this-num this))
             (fd (arg 0 args))
             (fd-undef (js-undefined-p fd))
             ;; ToIntegerOrInfinity(fractionDigits) is evaluated (and may throw)
             ;; even when x is NaN/Infinity — do it before the value checks.
             (f (if fd-undef 0d0 (to-integer-or-infinity fd))))
        (cond
          ((js-nan-p x) "NaN")
          ((= x *inf*) "Infinity")
          ((= x *-inf*) "-Infinity")
          (t
           (let ((s "") (ax x))
             ;; sign: prepend "-" only for a genuinely negative (non -0) value
             (when (< x 0) (setf s "-") (setf ax (- x)))
             (cond
               ((zerop ax)
                ;; x = 0: f+1 zeros, exponent 0. (undefined fd → single "0")
                (let* ((fi (if fd-undef 0 (truncate f)))
                       (mant (if (zerop fi) "0"
                                 (concatenate 'string "0."
                                              (make-string fi :initial-element #\0)))))
                  (concatenate 'string s mant "e+0")))
               (t
                (when (and (not fd-undef)
                           (or (< f 0) (> f 100)))
                  (js-throw (make-native-error "RangeError"
                              "toExponential() argument must be between 0 and 100")))
                (if fd-undef
                    ;; undefined: shortest unique representation in e-notation.
                    (multiple-value-bind (mant exp) (%shortest-exp ax)
                      (concatenate 'string s (%exp-string mant exp)))
                    (with-js-floats
                      (multiple-value-bind (digits e) (%sig-digits ax (1+ (truncate f)))
                        (concatenate 'string s (%exp-string digits e))))))))))))

    ;; -- Number.prototype.toPrecision(precision) ---------------------------
    (def-method realm np "toPrecision" 1 (this args)
      (let* ((x (this-num this))
             (pr (arg 0 args)))
        (if (js-undefined-p pr)
            (number-to-string x)
            (let ((p (to-integer-or-infinity pr)))  ; evaluated before NaN check
              (cond
                ((js-nan-p x) "NaN")
                ((= x *inf*) "Infinity")
                ((= x *-inf*) "-Infinity")
                (t
                 (when (or (js-nan-p p) (< p 1) (> p 100))
                   (js-throw (make-native-error "RangeError"
                               "toPrecision() argument must be between 1 and 100")))
                 (let ((pp (truncate p)) (s "") (ax x))
                   (when (< x 0) (setf s "-") (setf ax (- x)))
                   (cond
                     ((zerop ax)
                      ;; p zeros; if p>1 place decimal after first
                      (let ((mant (if (= pp 1) "0"
                                      (concatenate 'string "0."
                                                   (make-string (1- pp) :initial-element #\0)))))
                        (concatenate 'string s mant)))
                     (t
                      (with-js-floats
                        (multiple-value-bind (digits e) (%sig-digits ax pp)
                          (concatenate 'string s
                                       (%precision-format digits e pp)))))))))))))

    ;; -- Number.prototype.toLocaleString() ---------------------------------
    ;; Simple, spec-permitted fallback: delegate to the default toString.
    (def-method realm np "toLocaleString" 0 (this args)
      (declare (ignore args))
      (number-to-string (this-num this))))))

;;; Given P significant DIGITS and base-10 exponent E, render per the
;;; toPrecision spec: exponential when e < -6 or e >= p, else positional.
(defun %precision-format (digits e p)
  (cond
    ((or (< e -6) (>= e p))
     (%exp-string digits e))
    ((>= e (1- p))
     ;; integer: e = p-1, no fractional digits, pad if needed (shouldn't).
     (concatenate 'string digits (make-string (- e (1- p)) :initial-element #\0)))
    ((>= e 0)
     ;; e+1 integer digits, then a '.', then the rest.
     (concatenate 'string (subseq digits 0 (1+ e)) "." (subseq digits (1+ e))))
    (t
     ;; e < 0 (but >= -6): "0." then -(e+1) zeros then all digits.
     (concatenate 'string "0." (make-string (- (1+ e)) :initial-element #\0) digits))))

;;; Shortest unique exponential mantissa+exponent for a positive finite double.
;;; Reuses SBCL's shortest round-tripping printer (same source as dtoa), then
;;; normalises to (values DIGIT-STRING E) with no trailing zeros.
(defun %shortest-exp (x)
  (let* ((s (let ((*read-default-float-format* 'double-float)) (prin1-to-string x)))
         (epos (position #\e s))
         (mant (if epos (subseq s 0 epos) s))
         (exp (if epos (parse-integer s :start (1+ epos)) 0))
         (dot (position #\. mant))
         (int-len (if dot dot (length mant)))
         (raw (remove #\. mant))
         ;; strip leading zeros, tracking their effect on the exponent
         (lead (or (position-if (lambda (c) (char/= c #\0)) raw) (1- (length raw))))
         (sig (string-right-trim "0" (subseq raw lead))))
    (when (string= sig "") (setf sig "0"))
    ;; value = raw × 10^(exp - (len(raw)-int-len)); first significant digit is at
    ;; position `lead`, so its power-of-ten is (int-len - 1 - lead) + exp.
    (values sig (+ (- int-len 1 lead) exp))))

(register-builtin-installer 'install-number-methods)
