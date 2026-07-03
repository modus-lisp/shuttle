;;;; builtins/intl-plural-list-relative.lisp — Intl.PluralRules + Intl.ListFormat
;;;; + Intl.RelativeTimeFormat. Built ON the intl-core kernel
;;;; (canonicalize-locale-list / resolve-locale / get-option / coerce-options /
;;;; intl-register / intl-proto-from-newtarget / +numbering-system-digits+).
;;;;
;;;; DUPLICATION NOTE: SetNumberFormatDigitOptions is shared machinery with
;;;; Intl.NumberFormat (intl-numberformat.lisp). That file may load later, was a stub at
;;;; build time, so a locally-minimal digit-options reader + a small number
;;;; formatter (grouping + fraction parts) live HERE, prefixed `plr-`. When
;;;; NumberFormat lands its exports these should be de-duplicated.
(in-package #:shuttle)

;;; ===========================================================================
;;; Shared helpers
;;; ===========================================================================
(defun plr-supported-locales-of (locales options)
  "SupportedLocalesOf (lookup matcher): filter canonical LOCALES down to those
   with an available best-fit prefix. OPTIONS.localeMatcher is validated."
  (let ((requested (canonicalize-locale-list locales))
        (opts (plr-coerce-options options)))
    (get-option opts "localeMatcher" :string '("lookup" "best fit") "best fit")
    (let ((available (intl-available-locales)) (out '()))
      (dolist (req requested)
        (let* ((lid (parse-unicode-locale-id req))
               (base (and lid (base-name-string lid)))
               (match (and base (best-available-locale available (%lc base)))))
          (when match (push req out))))
      (let ((arr (make-array-object (nreverse out))))
        ;; SupportedLocalesOf returns a frozen-ish array; test262 checks it is an
        ;; Array — the plain array-object suffices for the corpus here.
        arr))))

(defun plr-object-p (this slot type-name)
  "RequireInternalSlot: read SLOT off THIS's internal plist or TypeError."
  (let ((v (if (js-object-p this)
               (getf (js-object-internal this) slot 'none)
               'none)))
    (when (eq v 'none)
      (js-throw (make-native-error "TypeError" (format nil "receiver is not an ~a" type-name))))
    v))

(defun plr-make-object (realm proto class)
  (declare (ignore realm))
  (make-object :proto proto :class class))

(defun plr-coerce-options (v)
  "CoerceOptionsToObject/GetOptionsObject: undefined -> a NULL-prototype object
   (so monkey-patched Object.prototype doesn't leak defaults); else ToObject."
  (if (js-undefined-p v)
      (make-object :proto *null* :class "Object")
      (to-object v)))

(defun plr-get-options-object (v)
  "GetOptionsObject: undefined -> null-proto object; an Object -> itself; any other
   primitive -> TypeError. (ListFormat & RelativeTimeFormat use this stricter form;
   PluralRules uses CoerceOptionsToObject which coerces primitives.)"
  (cond ((js-undefined-p v) (make-object :proto *null* :class "Object"))
        ((js-object-p v) v)
        (t (js-throw (make-native-error "TypeError" "options must be an object or undefined")))))

(defun plr-canon-locale (loc)
  "The kernel's resolve-locale lowercases its data-locale (e.g. en-us). Re-apply
   canonical case (en-US) for the resolved [[Locale]] string."
  (handler-case (canonicalize-language-tag loc) (error () loc)))

;;; ===========================================================================
;;; Number formatting (locally-minimal; grouping + fixed fraction digits)
;;; ===========================================================================
(defun plr-number-string (n min-frac max-frac)
  "Format non-negative real N (already |value|) to a decimal string with grouping
   applied to the integer part and MIN-FRAC..MAX-FRAC fraction digits (half-even).
   Returns the plain string; grouping uses ','."
  (multiple-value-bind (int-str frac-str) (plr-number-parts n min-frac max-frac)
    (if (plusp (length frac-str))
        (concatenate 'string (plr-group int-str) "." frac-str)
        (plr-group int-str))))

(defun plr-number-parts (n min-frac max-frac)
  "Return (values integer-digit-string fraction-digit-string) for non-negative N.
   No grouping applied to integer here. Rounds to MAX-FRAC fraction digits
   (half-even) then trims to at least MIN-FRAC."
  (let* ((scale (expt 10 max-frac))
         (scaled (* (rational n) scale))
         (rounded (%round-half-to-even (numerator scaled) (denominator scaled)))
         ;; rounded is integer count of (10^-max-frac) units
         (int-part (floor rounded scale))
         (frac-part (- rounded (* int-part scale)))
         (int-str (format nil "~d" int-part))
         (frac-full (if (plusp max-frac)
                        (format nil "~v,'0d" max-frac frac-part)
                        "")))
    ;; trim trailing zeros down to min-frac
    (let ((len (length frac-full)))
      (loop while (and (> len min-frac)
                       (char= (char frac-full (1- len)) #\0))
            do (decf len))
      (values int-str (subseq frac-full 0 len)))))

(defun plr-group (int-str)
  "Insert ',' every 3 digits from the right of a plain integer digit string."
  (let* ((len (length int-str)) (out '()) (cnt 0))
    (loop for i from (1- len) downto 0 do
      (push (char int-str i) out)
      (incf cnt)
      (when (and (zerop (mod cnt 3)) (> i 0))
        (push #\, out)))
    (coerce out 'string)))

(defun plr-digits-for-nu (nu)
  "Return the 10-char digit string for numbering system NU, or latn's."
  (or (cdr (assoc nu +numbering-system-digits+ :test #'string=))
      "0123456789"))

(defun plr-translate-digits (s nu)
  "Replace ASCII 0-9 in S with NU's digits (keeps , and .)."
  (let ((digits (plr-digits-for-nu nu)))
    (if (string= nu "latn")
        s
        (map 'string (lambda (c)
                       (if (char<= #\0 c #\9)
                           (char digits (- (char-code c) (char-code #\0)))
                           c))
             s))))

;;; Build parts: given an integer-string (grouped, latn) and a fraction string,
;;; produce a list of (type . value) with grouping and fraction split, applying
;;; NU digit translation to numeric characters.
(defun plr-number-to-parts (int-str frac-str nu)
  "INT-STR grouped w/ ',', FRAC-STR plain digits. Returns list of (keyword . str)
   parts: (:integer d)/(:group ,)/(:decimal .)/(:fraction d). Digits translated."
  (let ((parts '()) (buf '()))
    (flet ((flush ()
             (when buf
               (push (cons :integer (plr-translate-digits (coerce (nreverse buf) 'string) nu)) parts)
               (setf buf '()))))
      (loop for c across int-str do
        (cond ((char= c #\,)
               (flush)
               (push (cons :group (plr-translate-digits "," nu)) parts))
              (t (push c buf))))
      (flush))
    (when (plusp (length frac-str))
      (push (cons :decimal (plr-translate-digits "." nu)) parts)
      (push (cons :fraction (plr-translate-digits frac-str nu)) parts))
    (nreverse parts)))

;;; ===========================================================================
;;; SetNumberFormatDigitOptions (locally-minimal)
;;; ===========================================================================
(defstruct (plr-digits (:constructor make-plr-digits))
  (min-int 1)
  (min-frac 0)
  (max-frac 3)
  (min-sig nil)
  (max-sig nil)
  (rounding-priority "auto")
  (rounding-increment 1)
  (rounding-mode "halfExpand")
  (trailing-zero-display "auto")
  (round-type :fraction))          ; :significant-digits | :fraction | :morePrecision | :lessPrecision

(defun plr-set-digit-options (opts min-frac-default max-frac-default notation)
  "SetNumberFormatDigitOptions. Reads the digit keys in spec order from OPTS.
   Returns a plr-digits. NOTATION affects fraction defaults for compact (we keep
   it simple: mxfd default depends on notation only via the passed defaults)."
  (let* ((mnid (get-number-option opts "minimumIntegerDigits" 1 21 1))
         (mnfd-raw (js-get opts "minimumFractionDigits"))
         (mxfd-raw (js-get opts "maximumFractionDigits"))
         (mnsd-raw (js-get opts "minimumSignificantDigits"))
         (mxsd-raw (js-get opts "maximumSignificantDigits"))
         (rounding-increment (get-number-option opts "roundingIncrement" 1 5000 1))
         (rounding-mode (get-option opts "roundingMode" :string
                          '("ceil" "floor" "expand" "trunc" "halfCeil" "halfFloor"
                            "halfExpand" "halfTrunc" "halfEven") "halfExpand"))
         (rounding-priority (get-option opts "roundingPriority" :string
                              '("auto" "morePrecision" "lessPrecision") "auto"))
         (trailing-zero-display (get-option opts "trailingZeroDisplay" :string
                                  '("auto" "stripIfInteger") "auto"))
         (d (make-plr-digits :min-int mnid
                             :rounding-increment (truncate rounding-increment)
                             :rounding-mode rounding-mode
                             :rounding-priority rounding-priority
                             :trailing-zero-display trailing-zero-display)))
    (declare (ignore notation))
    (let* ((has-sd (or (not (js-undefined-p mnsd-raw)) (not (js-undefined-p mxsd-raw))))
           (has-fd (or (not (js-undefined-p mnfd-raw)) (not (js-undefined-p mxfd-raw)))))
      ;; significant-digit values
      (when (not (js-undefined-p mnsd-raw))
        (setf (plr-digits-min-sig d) (default-number-option mnsd-raw 1 21 1)))
      (when (not (js-undefined-p mxsd-raw))
        (setf (plr-digits-max-sig d) (default-number-option mxsd-raw
                                       (or (plr-digits-min-sig d) 1) 21 21)))
      ;; fraction-digit values
      (let ((mnfd nil) (mxfd nil))
        (when (not (js-undefined-p mnfd-raw))
          (setf mnfd (default-number-option mnfd-raw 0 100 0)))
        (when (not (js-undefined-p mxfd-raw))
          (setf mxfd (default-number-option mxfd-raw 0 100 nil)))
        (cond
          ((and (string= rounding-priority "auto") has-sd)
           (setf (plr-digits-round-type d) :significant-digits)
           (unless (plr-digits-min-sig d) (setf (plr-digits-min-sig d) 1))
           (unless (plr-digits-max-sig d) (setf (plr-digits-max-sig d) 21)))
          (t
           (setf (plr-digits-round-type d)
                 (cond ((string= rounding-priority "morePrecision") :morePrecision)
                       ((string= rounding-priority "lessPrecision") :lessPrecision)
                       (t :fraction)))
           ;; resolve fraction defaults
           (cond
             (has-fd
              (setf (plr-digits-min-frac d) (or mnfd 0))
              (setf (plr-digits-max-frac d)
                    (cond (mxfd (max mxfd (plr-digits-min-frac d)))
                          (t (max max-frac-default (plr-digits-min-frac d))))))
             (t
              (setf (plr-digits-min-frac d) min-frac-default)
              (setf (plr-digits-max-frac d) max-frac-default)))
           (when (or (string= rounding-priority "morePrecision")
                     (string= rounding-priority "lessPrecision"))
             (unless (plr-digits-min-sig d) (setf (plr-digits-min-sig d) 1))
             (unless (plr-digits-max-sig d) (setf (plr-digits-max-sig d) 21))))))
      d)))

;;; ===========================================================================
;;; PLURAL SELECTION (English CLDR rules)
;;; ===========================================================================
(defun plr-plural-operands (n min-frac max-frac)
  "Compute the CLDR plural operands (values-of-record) for absolute number N with
   the resolved fraction-digit range. Returns (values i v f n-abs) where
   i=integer digits, v=count of visible fraction digits, f=visible frac as int."
  (multiple-value-bind (int-str frac-str) (plr-number-parts (abs n) min-frac max-frac)
    (let* ((i (parse-integer int-str))
           (v (length frac-str))
           (f (if (plusp v) (parse-integer frac-str) 0)))
      (values i v f))))

(defun plr-select-en (type n digits)
  "English plural category for absolute number N. TYPE is \"cardinal\" or
   \"ordinal\"."
  (multiple-value-bind (i v f) (plr-plural-operands n (plr-digits-min-frac digits)
                                                    (plr-digits-max-frac digits))
    (declare (ignore f))
    (if (string= type "ordinal")
        ;; en ordinal: n%10==1 && n%100!=11 -> one; n%10==2 && n%100!=12 -> two;
        ;; n%10==3 && n%100!=13 -> few; else other. (integer n only; frac -> other)
        (if (plusp v)
            "other"
            (let ((mod10 (mod i 10)) (mod100 (mod i 100)))
              (cond ((and (= mod10 1) (/= mod100 11)) "one")
                    ((and (= mod10 2) (/= mod100 12)) "two")
                    ((and (= mod10 3) (/= mod100 13)) "few")
                    (t "other"))))
        ;; en cardinal: i==1 && v==0 -> one, else other
        (if (and (= i 1) (= v 0)) "one" "other"))))

(defun plr-categories-en (type)
  (if (string= type "ordinal")
      (list "few" "one" "other" "two")     ; sorted: few, one, other, two
      (list "one" "other")))

;;; ===========================================================================
;;; install-intl_plural_list_relative
;;; ===========================================================================
(defvar *intl-plural-proto* nil)
(defvar *intl-listformat-proto* nil)
(defvar *intl-rtf-proto* nil)

(defun install-intl_plural_list_relative (realm)
  (install-intl-pluralrules realm)
  (install-intl-listformat realm)
  (install-intl-relativetimeformat realm))

;;; ---------------------------------------------------------------------------
;;; Intl.PluralRules
;;; ---------------------------------------------------------------------------
(defun install-intl-pluralrules (realm)
  (let* ((op (realm-object-proto realm))
         (proto (make-object :proto op :class "Object"))
         (ctor (native-function realm "PluralRules"
                 (lambda (this args) (declare (ignore this args))
                   (js-throw (make-native-error "TypeError" "Constructor PluralRules requires 'new'")))
                 0)))
    (setf *intl-plural-proto* proto)
    (setf (js-object-construct ctor)
          (lambda (args nt)
            (when (js-undefined-p nt)
              (js-throw (make-native-error "TypeError" "Intl.PluralRules requires new")))
            (let* ((locales (arg 0 args))
                   (options-arg (arg 1 args))
                   (requested (canonicalize-locale-list locales))
                   (opts (plr-coerce-options options-arg)))
              ;; option read order: localeMatcher, type, notation, compactDisplay,
              ;; then SetNumberFormatDigitOptions.
              (get-option opts "localeMatcher" :string '("lookup" "best fit") "best fit")
              (let* ((type (get-option opts "type" :string '("cardinal" "ordinal") "cardinal"))
                     (notation (get-option opts "notation" :string
                                 '("standard" "scientific" "engineering" "compact") "standard"))
                     (compact-display (get-option opts "compactDisplay" :string
                                        '("short" "long") "short"))
                     (max-frac-default (if (string= notation "compact") 0 3))
                     (digits (plr-set-digit-options opts 0 max-frac-default notation))
                     (resolved (resolve-locale requested '() '()))
                     (locale (plr-canon-locale (getf resolved :locale)))
                     (obj (make-object :proto (proto-from-newtarget nt proto) :class "Object")))
                (setf (getf (js-object-internal obj) :plr-type) type
                      (getf (js-object-internal obj) :plr-notation) notation
                      (getf (js-object-internal obj) :plr-compact-display) compact-display
                      (getf (js-object-internal obj) :plr-digits) digits
                      (getf (js-object-internal obj) :plr-locale) locale)
                obj))))
    (def-value ctor "prototype" proto :writable nil :configurable nil)
    (def-value proto "constructor" ctor)
    ;; select
    (def-method realm proto "select" 1 (this args)
      (let* ((state (plr-object-p this :plr-type "Intl.PluralRules"))
             (digits (getf (js-object-internal this) :plr-digits))
             (n (to-number (arg 0 args))))
        (if (or (js-nan-p n) (and (floatp n) (or (= n *inf*) (= n *-inf*))))
            "other"
            (plr-select-en state (abs n) digits))))
    ;; selectRange
    (def-method realm proto "selectRange" 2 (this args)
      (let ((state (plr-object-p this :plr-type "Intl.PluralRules")))
        (declare (ignore state))
        (let ((xv (arg 0 args)) (yv (arg 1 args)))
          (when (or (js-undefined-p xv) (js-undefined-p yv))
            (js-throw (make-native-error "TypeError" "selectRange requires two arguments")))
          (let ((x (to-number xv)) (y (to-number yv)))
            (when (or (js-nan-p x) (js-nan-p y))
              (js-throw (make-native-error "RangeError" "selectRange arguments must be numbers")))
            ;; en: PluralRuleSelectRange(start,end) -> "other" for all en cases.
            "other"))))
    ;; resolvedOptions
    (def-method realm proto "resolvedOptions" 0 (this args)
      (let* ((state (plr-object-p this :plr-type "Intl.PluralRules"))
             (internal (js-object-internal this))
             (digits (getf internal :plr-digits))
             (notation (getf internal :plr-notation))
             (locale (getf internal :plr-locale))
             (o (make-object :proto (realm-object-proto realm) :class "Object")))
        (put o "locale" locale)
        (put o "type" state)
        (put o "notation" notation)
        (put o "minimumIntegerDigits" (float (plr-digits-min-int digits) 1d0))
        (cond
          ((eq (plr-digits-round-type digits) :significant-digits)
           (put o "minimumSignificantDigits" (float (plr-digits-min-sig digits) 1d0))
           (put o "maximumSignificantDigits" (float (plr-digits-max-sig digits) 1d0)))
          (t
           (put o "minimumFractionDigits" (float (plr-digits-min-frac digits) 1d0))
           (put o "maximumFractionDigits" (float (plr-digits-max-frac digits) 1d0))
           (when (plr-digits-min-sig digits)
             (put o "minimumSignificantDigits" (float (plr-digits-min-sig digits) 1d0))
             (put o "maximumSignificantDigits" (float (plr-digits-max-sig digits) 1d0)))))
        (when (string= notation "compact")
          (put o "compactDisplay" (getf internal :plr-compact-display)))
        (put o "pluralCategories"
             (make-array-object (plr-categories-en state)))
        (put o "roundingIncrement" (float (plr-digits-rounding-increment digits) 1d0))
        (put o "roundingMode" (plr-digits-rounding-mode digits))
        (put o "roundingPriority" (plr-digits-rounding-priority digits))
        (put o "trailingZeroDisplay" (plr-digits-trailing-zero-display digits))
        o))
    ;; supportedLocalesOf (ctor static)
    (put ctor "supportedLocalesOf"
         (native-function realm "supportedLocalesOf"
           (lambda (this args) (declare (ignore this))
             (plr-supported-locales-of (arg 0 args) (arg 1 args))) 1)
         :enumerable nil :writable t :configurable t)
    (put proto (symbol-tostringtag realm) "Intl.PluralRules"
         :enumerable nil :writable nil :configurable t)
    (intl-register realm "PluralRules" ctor)
    ctor))

;;; ---------------------------------------------------------------------------
;;; Intl.ListFormat
;;; ---------------------------------------------------------------------------
(defun lf-string-list-from-iterable (iterable)
  "StringListFromIterable: undefined -> (); else iterate, TypeError on non-string
   element (closing the iterator)."
  (if (js-undefined-p iterable)
      '()
      (let ((it (get-iterator iterable)) (out '()))
        (loop
          (let* ((res (iterator-step it))
                 (done (js-truthy (js-get res "done"))))
            (when done (return))
            (let ((val (js-get res "value")))
              (unless (stringp val)
                (iterator-close it)
                (js-throw (make-native-error "TypeError" "list element must be a string")))
              (push val out))))
        (nreverse out))))

(defun lf-pattern (type style)
  "Return (values pair start middle end) literal separators for en. PAIR is the
   2-element joiner; START/MIDDLE/END for lists of 3+: item START item MIDDLE ...
   END item — but en uses uniform START=MIDDLE=', ' and END depends on type."
  ;; Returns (values two-sep before-last-sep normal-sep)
  ;;   len2:  a <two-sep> b
  ;;   len3+: a <normal-sep> b <before-last-sep> c
  (cond
    ((string= type "unit")
     (if (string= style "narrow")
         (values " " " " " ")
         (values ", " ", " ", ")))
    ((string= type "disjunction")
     (cond ((string= style "narrow") (values " or " ", or " ", "))
           ((string= style "short")  (values " or " ", or " ", "))
           (t                        (values " or " ", or " ", "))))
    (t ;; conjunction
     (cond ((string= style "narrow") (values " & " ", & " ", "))
           ((string= style "short")  (values " & " ", & " ", "))
           (t                        (values " and " ", and " ", "))))))

(defun lf-format-parts (list type style)
  "Return a list of (:element . str) / (:literal . str) parts for LIST in en."
  (let ((n (length list)))
    (multiple-value-bind (two-sep before-last normal) (lf-pattern type style)
      (cond
        ((= n 0) '())
        ((= n 1) (list (cons :element (first list))))
        ((= n 2) (list (cons :element (first list))
                       (cons :literal two-sep)
                       (cons :element (second list))))
        (t
         (let ((parts '()))
           (loop for i from 0 for item in list do
             (when (> i 0)
               (push (cons :literal (if (= i (1- n)) before-last normal)) parts))
             (push (cons :element item) parts))
           (nreverse parts)))))))

(defun install-intl-listformat (realm)
  (let* ((op (realm-object-proto realm))
         (proto (make-object :proto op :class "Object"))
         (ctor (native-function realm "ListFormat"
                 (lambda (this args) (declare (ignore this args))
                   (js-throw (make-native-error "TypeError" "Constructor ListFormat requires 'new'")))
                 0)))
    (setf *intl-listformat-proto* proto)
    (setf (js-object-construct ctor)
          (lambda (args nt)
            (when (js-undefined-p nt)
              (js-throw (make-native-error "TypeError" "Intl.ListFormat requires new")))
            (let* ((locales (arg 0 args))
                   (options-arg (arg 1 args))
                   (requested (canonicalize-locale-list locales))
                   (opts (plr-get-options-object options-arg)))
              (get-option opts "localeMatcher" :string '("lookup" "best fit") "best fit")
              (let* ((type (get-option opts "type" :string
                             '("conjunction" "disjunction" "unit") "conjunction"))
                     (style (get-option opts "style" :string '("long" "short" "narrow") "long"))
                     (resolved (resolve-locale requested '() '()))
                     (locale (plr-canon-locale (getf resolved :locale)))
                     (obj (make-object :proto (proto-from-newtarget nt proto) :class "Object")))
                (setf (getf (js-object-internal obj) :lf-type) type
                      (getf (js-object-internal obj) :lf-style) style
                      (getf (js-object-internal obj) :lf-locale) locale)
                obj))))
    (def-value ctor "prototype" proto :writable nil :configurable nil)
    (def-value proto "constructor" ctor)
    (def-method realm proto "format" 1 (this args)
      (let* ((state (plr-object-p this :lf-type "Intl.ListFormat"))
             (internal (js-object-internal this))
             (style (getf internal :lf-style))
             (list (lf-string-list-from-iterable (arg 0 args)))
             (parts (lf-format-parts list state style)))
        (with-output-to-string (s)
          (dolist (p parts) (write-string (cdr p) s)))))
    (def-method realm proto "formatToParts" 1 (this args)
      (let* ((state (plr-object-p this :lf-type "Intl.ListFormat"))
             (internal (js-object-internal this))
             (style (getf internal :lf-style))
             (list (lf-string-list-from-iterable (arg 0 args)))
             (parts (lf-format-parts list state style)))
        (make-array-object
         (mapcar (lambda (p)
                   (let ((o (make-object :proto (realm-object-proto realm) :class "Object")))
                     (put o "type" (if (eq (car p) :element) "element" "literal"))
                     (put o "value" (cdr p))
                     o))
                 parts))))
    (def-method realm proto "resolvedOptions" 0 (this args)
      (let* ((state (plr-object-p this :lf-type "Intl.ListFormat"))
             (internal (js-object-internal this))
             (o (make-object :proto (realm-object-proto realm) :class "Object")))
        (put o "locale" (getf internal :lf-locale))
        (put o "type" state)
        (put o "style" (getf internal :lf-style))
        o))
    (put ctor "supportedLocalesOf"
         (native-function realm "supportedLocalesOf"
           (lambda (this args) (declare (ignore this))
             (plr-supported-locales-of (arg 0 args) (arg 1 args))) 1)
         :enumerable nil :writable t :configurable t)
    (put proto (symbol-tostringtag realm) "Intl.ListFormat"
         :enumerable nil :writable nil :configurable t)
    (intl-register realm "ListFormat" ctor)
    ctor))

;;; ---------------------------------------------------------------------------
;;; Intl.RelativeTimeFormat
;;; ---------------------------------------------------------------------------
(defparameter +rtf-units+
  '(("second" . :second) ("seconds" . :second)
    ("minute" . :minute) ("minutes" . :minute)
    ("hour" . :hour) ("hours" . :hour)
    ("day" . :day) ("days" . :day)
    ("week" . :week) ("weeks" . :week)
    ("month" . :month) ("months" . :month)
    ("quarter" . :quarter) ("quarters" . :quarter)
    ("year" . :year) ("years" . :year)))

;;; en short/narrow unit words: (unit . (singular plural)); plural=singular if 1.
(defparameter +rtf-long-units+
  '((:second "second" "seconds") (:minute "minute" "minutes") (:hour "hour" "hours")
    (:day "day" "days") (:week "week" "weeks") (:month "month" "months")
    (:quarter "quarter" "quarters") (:year "year" "years")))
(defparameter +rtf-short-units+
  '((:second "sec." "sec.") (:minute "min." "min.") (:hour "hr." "hr.")
    (:day "day" "days") (:week "wk." "wk.") (:month "mo." "mo.")
    (:quarter "qtr." "qtrs.") (:year "yr." "yr.")))
;; narrow == short in CLDR en for these units.
(defparameter +rtf-narrow-units+ +rtf-short-units+)

;;; numeric:"auto" exception phrases: (unit . (past-1 zero future-1)) or NIL.
(defparameter +rtf-auto-exceptions+
  '((:year "last year" "this year" "next year")
    (:quarter "last quarter" "this quarter" "next quarter")
    (:month "last month" "this month" "next month")
    (:week "last week" "this week" "next week")
    (:day "yesterday" "today" "tomorrow")
    (:hour nil "this hour" nil)
    (:minute nil "this minute" nil)
    (:second nil "now" nil)))

(defun rtf-unit-word (unit style plural-p)
  (let* ((tbl (cond ((string= style "short") +rtf-short-units+)
                    ((string= style "narrow") +rtf-narrow-units+)
                    (t +rtf-long-units+)))
         (row (cdr (assoc unit tbl))))
    (if plural-p (second row) (first row))))

(defun rtf-negative-zero-p (n)
  (and (floatp n) (zerop n) (minusp (float-sign n))))

(defun rtf-format-number (n digits nu)
  "Format |n| with grouping+fraction to a plain (translated) string."
  (multiple-value-bind (int-str frac-str) (plr-number-parts (abs n)
                                            (plr-digits-min-frac digits)
                                            (plr-digits-max-frac digits))
    (let ((grouped (plr-group int-str)))
      (if (plusp (length frac-str))
          (plr-translate-digits (concatenate 'string grouped "." frac-str) nu)
          (plr-translate-digits grouped nu)))))

(defun rtf-parts-for (n digits nu)
  "Return list of number (:integer/:group/:decimal/:fraction . str) parts for |n|."
  (multiple-value-bind (int-str frac-str) (plr-number-parts (abs n)
                                            (plr-digits-min-frac digits)
                                            (plr-digits-max-frac digits))
    (plr-number-to-parts (plr-group int-str) frac-str nu)))

(defun rtf-compute (state internal n unit)
  "Return (values kind past-p n number-str phrase). KIND is :literal (auto
   exception) or :numeric. For :numeric, past-p, number-str usable; phrase nil.
   For :literal, phrase is the single literal string."
  (let* ((style (getf internal :rtf-style))
         (numeric (getf internal :rtf-numeric))
         (digits (getf internal :rtf-digits))
         (nu (getf internal :rtf-nu))
         (neg-zero (rtf-negative-zero-p n))
         (past-p (or (minusp n) neg-zero))
         (int-n (if (and (floatp n) (= n (fround n))) (round n) nil)))
    (declare (ignore state))
    ;; numeric:auto exceptions apply only when value is exactly -1, 0, or 1.
    (when (string= numeric "auto")
      (let ((ex (cdr (assoc unit +rtf-auto-exceptions+))))
        (when (and ex int-n)
          (let ((phrase (cond ((zerop n) (second ex))       ; 0 or -0 -> zero phrase
                              ((= int-n 1) (third ex))
                              ((= int-n -1) (first ex))
                              (t nil))))
            (when phrase
              (return-from rtf-compute (values :literal past-p n nil phrase)))))))
    ;; numeric form
    (let* ((num-str (rtf-format-number n digits nu))
           ;; plural: |n| == 1 -> singular, else plural (en cardinal rule)
           (plural-p (not (and int-n (= (abs int-n) 1)))))
      (values :numeric past-p n num-str (rtf-unit-word unit style plural-p) digits nu))))

(defun install-intl-relativetimeformat (realm)
  (let* ((op (realm-object-proto realm))
         (proto (make-object :proto op :class "Object"))
         (ctor (native-function realm "RelativeTimeFormat"
                 (lambda (this args) (declare (ignore this args))
                   (js-throw (make-native-error "TypeError" "Constructor RelativeTimeFormat requires 'new'")))
                 0)))
    (setf *intl-rtf-proto* proto)
    (setf (js-object-construct ctor)
          (lambda (args nt)
            (when (js-undefined-p nt)
              (js-throw (make-native-error "TypeError" "Intl.RelativeTimeFormat requires new")))
            (let* ((locales (arg 0 args))
                   (options-arg (arg 1 args))
                   (requested (canonicalize-locale-list locales))
                   (opts (plr-coerce-options options-arg)))
              ;; read order: localeMatcher, numberingSystem, style, numeric
              (get-option opts "localeMatcher" :string '("lookup" "best fit") "best fit")
              (let* ((nu-opt (rtf-read-numbering-system opts))
                     (style (get-option opts "style" :string '("long" "short" "narrow") "long"))
                     (numeric (get-option opts "numeric" :string '("always" "auto") "always"))
                     ;; NOTE: don't pass "nu" as a relevant-extension-key to the
                     ;; kernel's resolve-locale — it mishandles keyword values with
                     ;; types (string= on a list). Extract -u-nu- ourselves.
                     (resolved (resolve-locale requested '() '()))
                     (base-locale (plr-canon-locale (getf resolved :data-locale)))
                     ;; determine numbering system: option overrides -u-nu-.
                     (nu-ext (rtf-extract-nu (getf resolved :data-locale) requested))
                     (nu (cond ((and nu-opt (rtf-nu-supported-p nu-opt)) nu-opt)
                               ((and nu-ext (stringp nu-ext) (plusp (length nu-ext))
                                     (rtf-nu-supported-p nu-ext)) nu-ext)
                               (t "latn")))
                     (locale (if (string= nu "latn")
                                 base-locale
                                 (format nil "~a-u-nu-~a" base-locale nu)))
                     (digits (make-plr-digits :min-int 1 :min-frac 0 :max-frac 3))
                     (obj (make-object :proto (proto-from-newtarget nt proto) :class "Object")))
                (setf (getf (js-object-internal obj) :rtf-style) style
                      (getf (js-object-internal obj) :rtf-numeric) numeric
                      (getf (js-object-internal obj) :rtf-nu) nu
                      (getf (js-object-internal obj) :rtf-digits) digits
                      (getf (js-object-internal obj) :rtf-locale) locale)
                obj))))
    (def-value ctor "prototype" proto :writable nil :configurable nil)
    (def-value proto "constructor" ctor)
    (def-method realm proto "format" 2 (this args)
      (let* ((state (plr-object-p this :rtf-style "Intl.RelativeTimeFormat"))
             (internal (js-object-internal this))
             (value (to-number (arg 0 args)))
             (unit (rtf-validate-unit (arg 1 args))))
        (when (or (js-nan-p value) (= value *inf*) (= value *-inf*))
          (js-throw (make-native-error "RangeError" "value must be finite")))
        (multiple-value-bind (kind past-p n num-str word) (rtf-compute state internal value unit)
          (declare (ignore n))
          (if (eq kind :literal)
              word
              (if past-p
                  (format nil "~a ~a ago" num-str word)
                  (format nil "in ~a ~a" num-str word))))))
    (def-method realm proto "formatToParts" 2 (this args)
      (let* ((state (plr-object-p this :rtf-style "Intl.RelativeTimeFormat"))
             (internal (js-object-internal this))
             (value (to-number (arg 0 args)))
             (unit (rtf-validate-unit (arg 1 args))))
        (when (or (js-nan-p value) (= value *inf*) (= value *-inf*))
          (js-throw (make-native-error "RangeError" "value must be finite")))
        (multiple-value-bind (kind past-p n num-str word digits nu)
            (rtf-compute state internal value unit)
          (declare (ignore num-str))
          (rtf-make-parts realm kind past-p n word unit digits nu internal))))
    (def-method realm proto "resolvedOptions" 0 (this args)
      (let* ((state (plr-object-p this :rtf-style "Intl.RelativeTimeFormat"))
             (internal (js-object-internal this))
             (o (make-object :proto (realm-object-proto realm) :class "Object")))
        (put o "locale" (getf internal :rtf-locale))
        (put o "style" state)
        (put o "numeric" (getf internal :rtf-numeric))
        (put o "numberingSystem" (getf internal :rtf-nu))
        o))
    (put ctor "supportedLocalesOf"
         (native-function realm "supportedLocalesOf"
           (lambda (this args) (declare (ignore this))
             (plr-supported-locales-of (arg 0 args) (arg 1 args))) 1)
         :enumerable nil :writable t :configurable t)
    (put proto (symbol-tostringtag realm) "Intl.RelativeTimeFormat"
         :enumerable nil :writable nil :configurable t)
    (intl-register realm "RelativeTimeFormat" ctor)
    ctor))

(defun rtf-read-numbering-system (opts)
  "GetOption(numberingSystem) then validate as a type sequence (or NIL)."
  (let ((v (js-get opts "numberingSystem")))
    (if (js-undefined-p v)
        nil
        (let ((s (to-string v)))
          ;; well-formed: (3-8 alnum)(-3-8 alnum)*
          (let ((parts (split-dash s)))
            (unless (and parts (every (lambda (p) (and (<= 3 (length p) 8) (%all #'%alnum-p p))) parts))
              (js-throw (make-native-error "RangeError" "invalid numberingSystem"))))
          (%lc s)))))

(defun rtf-extract-nu (data-locale requested)
  "Find the requested tag whose base-name best-matches DATA-LOCALE and return its
   -u-nu- value string, or NIL. (Mirrors ResolveLocale's extension pickup without
   the kernel's list-vs-string bug.)"
  (let ((available (intl-available-locales)))
    (dolist (req requested)
      (let* ((lid (parse-unicode-locale-id req))
             (base (and lid (base-name-string lid)))
             (match (and base (best-available-locale available (%lc base)))))
        (when (and match (string-equal match data-locale))
          (let* ((uentry (assoc #\u (locale-id-extensions lid)))
                 (kw (and uentry (assoc "nu" (getf (cdr uentry) :keywords) :test #'string=))))
            (return-from rtf-extract-nu
              (when kw (format nil "~{~a~^-~}" (cdr kw))))))))
    nil))

(defun rtf-nu-supported-p (nu)
  (or (assoc nu +numbering-system-digits+ :test #'string=)
      (member nu +numbering-system-digit-names+ :test #'string=)))

(defun rtf-validate-unit (v)
  "Validate the unit argument: must be a String naming a singular/plural unit, or
   RangeError. A Symbol -> TypeError (via to-string)."
  (let ((s (to-string v)))
    (let ((u (cdr (assoc s +rtf-units+ :test #'string=))))
      (unless u
        (js-throw (make-native-error "RangeError" (format nil "invalid unit: ~a" s))))
      u)))

(defun rtf-make-parts (realm kind past-p n word unit digits nu internal)
  (declare (ignore internal))
  (let* ((unit-str (string-downcase (symbol-name unit)))
         (parts '()))
    (flet ((lit (v) (let ((o (make-object :proto (realm-object-proto realm) :class "Object")))
                      (put o "type" "literal") (put o "value" v) o))
           (num (type v) (let ((o (make-object :proto (realm-object-proto realm) :class "Object")))
                           (put o "type" type) (put o "value" v) (put o "unit" unit-str) o)))
      (if (eq kind :literal)
          (setf parts (list (lit word)))
          (let ((number-parts (rtf-parts-for n digits nu)))
            (if past-p
                (progn
                  (dolist (p number-parts)
                    (push (num (string-downcase (symbol-name (car p))) (cdr p)) parts))
                  (setf parts (nreverse parts))
                  (setf parts (append parts (list (lit (format nil " ~a ago" word))))))
                (progn
                  (push (lit "in ") parts)
                  (dolist (p number-parts)
                    (push (num (string-downcase (symbol-name (car p))) (cdr p)) parts))
                  (setf parts (nreverse parts))
                  (setf parts (append parts (list (lit (format nil " ~a" word)))))))))
      (make-array-object parts))))

(register-builtin-installer 'install-intl_plural_list_relative)
