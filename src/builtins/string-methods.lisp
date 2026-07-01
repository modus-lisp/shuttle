;;;; builtins/string-methods.lisp — String.prototype/String methods beyond the
;;;; kernel (NON-regex only). Kernel install-string already has a broad set (see
;;;; realm.lisp). This file adds the remaining non-regex methods.
;;;; String.prototype = (realm-string-proto realm); the String ctor via
;;;;   (js-get (realm-global realm) "String").
;;;;
;;;; Convention mirrors the kernel's install-string `sm` macrolet: each proto
;;;; method does require-object-coercible on `this` then binds s = (to-string this).
;;;; def-method's body is a lambda; use (block tag ...) to return from the method.
;;;; Statics go on the String constructor (a non-enumerable/writable/configurable
;;;; def-method), reached via (js-get (realm-global realm) "String").
(in-package #:shuttle)

;;; --- surrogate helpers (UTF-16 code-unit predicates on CL chars) -------------
;;; SBCL chars span the full 0..#x10FFFF range, so a CL string CAN hold lone
;;; surrogate code units. NOTE: the current lexer does not decode \uXXXX / \xXX
;;; escapes (see src/lex.lisp — the escape case falls through to the literal
;;; char), so JS source like '\uD83D' yields "uD83D" rather than a lone
;;; surrogate. isWellFormed/toWellFormed are implemented correctly against real
;;; surrogate chars regardless; the test262 cases that construct lone surrogates
;;; via \u escapes therefore can't reach this layer with actual surrogates.
(declaim (inline lead-surrogate-p trail-surrogate-p surrogate-p))
(defun lead-surrogate-p (cc)  (<= #xD800 cc #xDBFF))
(defun trail-surrogate-p (cc) (<= #xDC00 cc #xDFFF))
(defun surrogate-p (cc)       (<= #xD800 cc #xDFFF))

(defun string-well-formed-p (s)
  "IsStringWellFormedUnicode: no unpaired UTF-16 surrogate code units."
  (let ((n (length s)) (i 0))
    (loop while (< i n) do
      (let ((cc (char-code (char s i))))
        (cond ((lead-surrogate-p cc)
               (if (and (< (1+ i) n) (trail-surrogate-p (char-code (char s (1+ i)))))
                   (incf i 2)          ; valid pair
                   (return-from string-well-formed-p nil)))
              ((trail-surrogate-p cc)  ; lone trailing surrogate
               (return-from string-well-formed-p nil))
              (t (incf i)))))
    t))

(defun string-to-well-formed (s)
  "Replace each unpaired surrogate code unit with U+FFFD."
  (let ((n (length s)) (i 0) (out (make-string-output-stream)))
    (loop while (< i n) do
      (let* ((ch (char s i)) (cc (char-code ch)))
        (cond ((lead-surrogate-p cc)
               (if (and (< (1+ i) n) (trail-surrogate-p (char-code (char s (1+ i)))))
                   (progn (write-char ch out) (write-char (char s (1+ i)) out) (incf i 2))
                   (progn (write-char #\Replacement_Character out) (incf i))))
              ((trail-surrogate-p cc)
               (write-char #\Replacement_Character out) (incf i))
              (t (write-char ch out) (incf i)))))
    (get-output-stream-string out)))

(defun install-string-methods (realm)
  (let ((sp (realm-string-proto realm)))
    (macrolet ((sm (name len (s args) &body body)
                 `(def-method realm sp ,name ,len (this ,args)
                    (require-object-coercible this)
                    (let ((,s (to-string this))) (declare (ignorable ,s)) ,@body))))

      ;; String.prototype.localeCompare(that) — code-point comparison, -1/0/1.
      (sm "localeCompare" 1 (s args)
        (let ((that (to-string (arg 0 args))))
          (cond ((string< s that) -1d0)
                ((string> s that) 1d0)
                (t 0d0))))

      ;; String.prototype.normalize([form]) — validate form; pass-through.
      ;; Full NFC/NFD/NFKC/NFKD would need the Unicode canonical/compatibility
      ;; decomposition + canonical composition data (UnicodeData.txt / CCC /
      ;; composition-exclusions); we do argument validation only, which is
      ;; correct for already-normalized (e.g. ASCII/BMP-no-composition) input.
      (sm "normalize" 0 (s args)
        (let ((farg (arg 0 args)))
          (let ((form (if (js-undefined-p farg) "NFC" (to-string farg))))
            (unless (member form '("NFC" "NFD" "NFKC" "NFKD") :test #'string=)
              (js-throw (make-native-error "RangeError"
                          "The normalization form should be one of NFC, NFD, NFKC, NFKD.")))
            s)))

      ;; String.prototype.isWellFormed() — boolean.
      (sm "isWellFormed" 0 (s args)
        (declare (ignore args))
        (js-bool (string-well-formed-p s)))

      ;; String.prototype.toWellFormed() — lone surrogates -> U+FFFD.
      (sm "toWellFormed" 0 (s args)
        (declare (ignore args))
        (string-to-well-formed s)))

    ;; --- statics on the String constructor ------------------------------------
    (let ((ctor (js-get (realm-global realm) "String")))

      ;; String.fromCodePoint(...codePoints)
      (def-method realm ctor "fromCodePoint" 1 (this args)
        (declare (ignore this))
        (let ((out (make-string-output-stream)))
          (dolist (a args)
            (let ((n (to-number a)))
              (when (or (js-nan-p n) (/= n (ftruncate n)) (< n 0) (> n #x10FFFF))
                (js-throw (make-native-error "RangeError"
                            (format nil "Invalid code point ~a" (to-string a)))))
              (let ((cp (truncate n)))
                (if (<= cp #xFFFF)
                    (write-char (code-char cp) out)
                    ;; astral: encode as a UTF-16 surrogate pair
                    (let ((v (- cp #x10000)))
                      (write-char (code-char (+ #xD800 (ash v -10))) out)
                      (write-char (code-char (+ #xDC00 (logand v #x3FF))) out))))))
          (get-output-stream-string out)))

      ;; String.raw(template, ...substitutions)
      (def-method realm ctor "raw" 1 (this args)
        (declare (ignore this))
        (let* ((template (arg 0 args))
               (cooked (to-object template))               ; ? ToObject(template) — throws for null/undefined
               (raw (to-object (js-get cooked "raw")))     ; ? ToObject(cooked.raw)
               (lit-count (truncate (to-length (js-get raw "length")))))
          (if (<= lit-count 0)
              ""
              (let ((out (make-string-output-stream))
                    (subs (if (cdr args) (cdr args) '())))
                (dotimes (i lit-count)
                  (write-string (to-string (js-get raw (princ-to-string i))) out)
                  (when (< i (1- lit-count))
                    (let ((sub (nth i subs)))
                      (when sub   ; substitutions run out -> undefined -> nothing appended
                        (write-string (to-string sub) out)))))
                (get-output-stream-string out))))))))

(register-builtin-installer 'install-string-methods)
