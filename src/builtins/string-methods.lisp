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

;;; --- ES whitespace / line-terminator set (WhiteSpace + LineTerminator) -------
;;; The kernel's +js-ws+ (value.lisp) omits several Unicode Zs code points
;;; (U+1680, U+2000..U+200A, U+202F, U+205F, U+3000). trim/trimStart/trimEnd
;;; below use this fuller set and OVERRIDE the kernel installers.
(defparameter +str-ws-chars+
  (mapcar #'code-char
          '(#x0009 #x000A #x000B #x000C #x000D #x0020 #x00A0 #x1680
            #x2000 #x2001 #x2002 #x2003 #x2004 #x2005 #x2006 #x2007
            #x2008 #x2009 #x200A #x2028 #x2029 #x202F #x205F #x3000
            #xFEFF)))

(defun str-integer-or-inf (v)
  "ToIntegerOrInfinity as an exact CL rational/keyword: real number, :+inf, :-inf.
   Unlike to-int-index (realm.lisp) this preserves +/-Infinity so callers can
   clamp against length correctly."
  (let ((n (to-number v)))
    (cond ((js-nan-p n) 0)
          ((= n *inf*) :+inf)
          ((= n *-inf*) :-inf)
          (t (truncate n)))))

(defun str-clamp-pos (v len)
  "min(max(ToIntegerOrInfinity(v),0),len) -> a CL fixnum in [0,len]."
  (let ((n (str-integer-or-inf v)))
    (cond ((eq n :+inf) len)
          ((eq n :-inf) 0)
          ((< n 0) 0)
          ((> n len) len)
          (t n))))

(defun str-is-regexp-p (v)
  "IsRegExp: object whose @@match is truthy (or undefined @@match + RegExp exotic)."
  (and (js-object-p v)
       (let ((m (and (boundp '*symbol-match*) (symbol-value '*symbol-match*)
                     (js-get v (symbol-value '*symbol-match*)))))
         (if (or (null m) (js-undefined-p m))
             (and (fboundp 'regexp-object-p) (funcall 'regexp-object-p v))
             (js-truthy m)))))

(defun str-reject-regexp (v method)
  (when (str-is-regexp-p v)
    (js-throw (make-native-error "TypeError"
                (format nil "First argument to String.prototype.~a must not be a regular expression" method)))))

(defun install-string-methods (realm)
  (let ((sp (realm-string-proto realm)))
    ;; String.prototype is a String exotic object with [[StringData]] = "".
    ;; The kernel makes it a plain object; set its primitive so toString/valueOf
    ;; (and ToPrimitive via ==) treat it as the empty string.
    (unless (stringp (js-object-primitive sp))
      (setf (js-object-primitive sp) ""))
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
        (string-to-well-formed s))

      ;; --- OVERRIDES of kernel methods (installers run after install-string) ---

      ;; trim/trimStart/trimEnd — kernel's +js-ws+ misses several Zs code points.
      (sm "trim" 0 (s args) (declare (ignore args)) (string-trim +str-ws-chars+ s))
      (sm "trimStart" 0 (s args) (declare (ignore args)) (string-left-trim +str-ws-chars+ s))
      (sm "trimEnd" 0 (s args) (declare (ignore args)) (string-right-trim +str-ws-chars+ s))

      ;; indexOf — kernel clamps +Infinity position to 0; must clamp to len.
      ;; Order: ToString(this) [sm], ToString(search), ToIntegerOrInfinity(pos).
      (sm "indexOf" 1 (s args)
        (let* ((sub (to-string (arg 0 args)))
               (len (length s))
               (from (str-clamp-pos (arg 1 args) len))
               (p (search sub s :start2 (min from len))))
          (if p (float p 1d0) -1d0)))

      ;; lastIndexOf — kernel ignores position; per spec ToNumber(position) must
      ;; run (and can throw) between ToString(search) and the search itself.
      (sm "lastIndexOf" 1 (s args)
        (let* ((sub (to-string (arg 0 args)))
               (len (length s))
               (numpos (to-number (arg 1 args)))     ; ? ToNumber(position)
               (end (cond ((js-nan-p numpos) len)     ; NaN -> +Infinity -> len
                          ((= numpos *inf*) len)
                          ((= numpos *-inf*) 0)
                          (t (min (max (truncate numpos) 0) len))))
               ;; search may start at index end (inclusive), so end2 = end+sublen
               (limit (min len (+ end (length sub))))
               (p (search sub s :from-end t :end2 limit)))
          (if p (float p 1d0) -1d0)))

      ;; includes — kernel ignores position and doesn't reject RegExp arg.
      (sm "includes" 1 (s args)
        (str-reject-regexp (arg 0 args) "includes")
        (let* ((sub (to-string (arg 0 args)))
               (len (length s))
               (start (str-clamp-pos (arg 1 args) len)))
          (js-bool (search sub s :start2 start))))

      ;; startsWith — reject RegExp arg; ToIntegerOrInfinity for position.
      (sm "startsWith" 1 (s args)
        (str-reject-regexp (arg 0 args) "startsWith")
        (let* ((sub (to-string (arg 0 args)))
               (len (length s))
               (pos (str-clamp-pos (arg 1 args) len)))
          (js-bool (and (<= (+ pos (length sub)) len)
                        (string= sub s :start2 pos :end2 (+ pos (length sub)))))))

      ;; endsWith — reject RegExp arg; clamp endPosition to [0,len].
      (sm "endsWith" 1 (s args)
        (str-reject-regexp (arg 0 args) "endsWith")
        (let* ((sub (to-string (arg 0 args)))
               (len (length s))
               (end (if (js-undefined-p (arg 1 args)) len (str-clamp-pos (arg 1 args) len)))
               (start (- end (length sub))))
          (js-bool (and (>= start 0)
                        (string= sub s :start2 start :end2 end)))))

      ;; slice — kernel's clamp-index collapses +/-Infinity to 0.
      (sm "slice" 2 (s args)
        (let* ((len (length s))
               (from (let ((n (str-integer-or-inf (arg 0 args))))
                       (cond ((eq n :+inf) len) ((eq n :-inf) 0)
                             ((< n 0) (max (+ len n) 0)) (t (min n len)))))
               (to (if (js-undefined-p (arg 1 args)) len
                       (let ((n (str-integer-or-inf (arg 1 args))))
                         (cond ((eq n :+inf) len) ((eq n :-inf) 0)
                               ((< n 0) (max (+ len n) 0)) (t (min n len)))))))
          (if (< from to) (subseq s from to) "")))

      ;; substring — kernel's to-int-index collapses +Infinity to 0.
      (sm "substring" 2 (s args)
        (let* ((len (length s))
               (a (let ((n (str-integer-or-inf (arg 0 args))))
                    (cond ((eq n :+inf) len) ((eq n :-inf) 0) (t (min (max n 0) len)))))
               (b (if (js-undefined-p (arg 1 args)) len
                      (let ((n (str-integer-or-inf (arg 1 args))))
                        (cond ((eq n :+inf) len) ((eq n :-inf) 0) (t (min (max n 0) len)))))))
          (subseq s (min a b) (max a b))))

      ;; codePointAt — kernel returns the raw code unit; must decode surrogate
      ;; pairs and return undefined for out-of-range position.
      (sm "codePointAt" 1 (s args)
        (let* ((len (length s))
               (n (str-integer-or-inf (arg 0 args))))
          (if (or (eq n :-inf) (and (integerp n) (< n 0))
                  (eq n :+inf) (and (integerp n) (>= n len)))
              *undefined*
              (let ((cc (char-code (char s n))))
                (if (and (lead-surrogate-p cc) (< (1+ n) len)
                         (trail-surrogate-p (char-code (char s (1+ n)))))
                    (let ((tc (char-code (char s (1+ n)))))
                      (float (+ #x10000 (ash (- cc #xD800) 10) (- tc #xDC00)) 1d0))
                    (float cc 1d0))))))

      ;; repeat — kernel uses to-int-index (drops +Infinity to 0); +Infinity and
      ;; negative counts must throw RangeError.
      (sm "repeat" 1 (s args)
        (let ((n (str-integer-or-inf (arg 0 args))))
          (when (or (eq n :+inf) (eq n :-inf) (and (integerp n) (< n 0)))
            (js-throw (make-native-error "RangeError" "Invalid count value")))
          (with-output-to-string (o) (dotimes (i n) (write-string s o))))))

    ;; --- toString / valueOf: must be String or String box, else TypeError. ---
    ;; (kernel's this-string coerces numbers/booleans instead of throwing.)
    (flet ((str-this-value (this what)
             (cond ((stringp this) this)
                   ((and (js-object-p this) (stringp (js-object-primitive this)))
                    (js-object-primitive this))
                   (t (js-throw (make-native-error "TypeError"
                                  (format nil "String.prototype.~a requires that 'this' be a String" what)))))))
      (def-method realm sp "toString" 0 (this args) (declare (ignore args)) (str-this-value this "toString"))
      (def-method realm sp "valueOf" 0 (this args) (declare (ignore args)) (str-this-value this "valueOf")))

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
