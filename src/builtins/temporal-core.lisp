;;;; builtins/temporal-core.lisp — shared Temporal kernel.
;;;;
;;;; This file is the FOUNDATION for the whole Temporal namespace. Instant,
;;;; PlainTime (this round) and the later PlainDate/PlainDateTime/
;;;; Duration/ZonedDateTime/PlainYearMonth/PlainMonthDay all build ON the
;;;; abstractions here. Everything is EXACT: epoch values are CL integers
;;;; (nanoseconds), rounding runs over CL rationals, ISO fields are plain
;;;; integers. JS-visible BigInt == CL integer (js-bigint-p is integerp), so an
;;;; epochNanoseconds getter simply returns the CL integer.
;;;;
;;;; ---------------------------------------------------------------------------
;;;; KERNEL API (call these from the type files — grouped by concern):
;;;;
;;;;  Namespace / registration
;;;;    (temporal-namespace realm)            -> the global `Temporal` object
;;;;    (temporal-register realm name ctor)   -> hang Name on Temporal (non-enum)
;;;;    (temporal-tag realm)                  -> the @@toStringTag symbol (or str)
;;;;    (temporal-brand o slot)               -> stamp internal slot (keyword)
;;;;    (temporal-slot this slot)             -> read slot or TypeError (branding)
;;;;    (proto-from-newtarget nt default)     -> GetPrototypeFromConstructor
;;;;
;;;;  ISO date/time records (structs)
;;;;    (make-iso-date y m d) / iso-date-year/-month/-day
;;;;    (make-iso-time h m s ms us ns) + accessors iso-time-hour ... -nanosecond
;;;;    (iso-date->epoch-days iso) / (epoch-days->iso-date days)
;;;;    (days-in-month y m) (iso-days-in-year y) (leap-year-p y)
;;;;    (iso-day-of-week iso) (balance-time h m s ms us ns) -> (values days time)
;;;;
;;;;  Epoch conversions
;;;;    (iso-datetime->epoch-ns date time)    -> integer ns (UTC)
;;;;    (epoch-ns->iso-datetime ns)           -> (values iso-date iso-time)
;;;;    (valid-epoch-ns-p ns)                 -> within +/-8.64e21
;;;;    +ns-min+ +ns-max+  +ns-per-*+ constants
;;;;
;;;;  Parser (ISO 8601 Temporal grammar) — every from(string) shares these:
;;;;    (parse-temporal-instant s)   -> (values epoch-ns) | RangeError
;;;;    (parse-iso-datetime s kind)  -> plist (:year..:nanosecond :offset :z ...)
;;;;    (parse-temporal-time s)      -> iso-time | RangeError
;;;;    (parse-temporal-duration s)  -> duration plist | RangeError
;;;;
;;;;  Formatter
;;;;    (format-iso-time time precision) (format-fractional ns digits)
;;;;    (format-offset-ns ns)  (format-iso-date-string y m d)
;;;;
;;;;  Rounding engine (exact, over rationals)
;;;;    (round-to-increment x increment mode) -> integer  (9 modes)
;;;;    (validate-rounding-increment inc max inclusive)
;;;;  Modes are keywords: :ceil :floor :expand :trunc :half-ceil :half-floor
;;;;    :half-expand :half-trunc :half-even
;;;;
;;;;  Options readers (SPEC-ORDERED, observable gets — read keys alphabetically)
;;;;    (get-options-object v)
;;;;    (get-temporal-overflow options)            -> :constrain | :reject
;;;;    (get-rounding-mode options default)        -> mode keyword
;;;;    (get-rounding-increment options)           -> integer
;;;;    (get-fractional-second-digits options)     -> :auto | 0..9
;;;;    (get-temporal-unit options key kind default allowed) -> unit keyword
;;;;    (get-difference-settings op options ...)   -> (values smallest largest inc mode)
;;;;
;;;;  Duration helpers
;;;;    (to-temporal-duration-record v)   -> duration plist (string|bag|instance)
;;;;    duration plist keys: :years :months :weeks :days :hours :minutes
;;;;      :seconds :milliseconds :microseconds :nanoseconds
;;;;    (duration-time-ns d) -> total ns of the time part (h..ns), exact integer
;;;;
;;;;  Time zones (UTC + fixed offsets only, per corpus)
;;;;    (parse-time-zone-offset s) -> offset-ns | nil
;;;;    (offset-ns-for-zone z)     -> integer (0 for "UTC")
;;;; ---------------------------------------------------------------------------
(in-package #:shuttle)

;;; ===========================================================================
;;; Constants
;;; ===========================================================================
(defconstant +ns-per-us+  1000)
(defconstant +ns-per-ms+  1000000)
(defconstant +ns-per-s+   1000000000)
(defconstant +ns-per-min+ 60000000000)
(defconstant +ns-per-hour+ 3600000000000)
(defconstant +ns-per-day+ 86400000000000)
;; Instant range: +/- 8.64e21 ns == 10^8 days from the epoch.
(defconstant +ns-min+ -8640000000000000000000)
(defconstant +ns-max+  8640000000000000000000)
;; ISO year range for datetime values: RejectDateTimeRange uses +/-10^8 days
;; from the epoch, which corresponds to years -271821..275760.
(defconstant +iso-year-min+ -271821)
(defconstant +iso-year-max+  275760)

;;; ===========================================================================
;;; ISO records
;;; ===========================================================================
(defstruct (iso-date (:constructor make-iso-date (year month day)))
  year month day)

(defstruct (iso-time (:constructor make-iso-time (hour minute second millisecond microsecond nanosecond)))
  hour minute second millisecond microsecond nanosecond)

;;; ===========================================================================
;;; Integer calendar arithmetic (iso8601). Ported to EXACT integers from the
;;; float64 algorithms in date.lisp — never call those (they lose precision at
;;; the extremes Temporal exercises).
;;; ===========================================================================
(defun leap-year-p (year)
  (and (zerop (mod year 4))
       (or (not (zerop (mod year 100)))
           (zerop (mod year 400)))))

(defun iso-days-in-year (year) (if (leap-year-p year) 366 365))

(defun days-in-month (year month)
  "MONTH is 1..12."
  (case month
    ((1 3 5 7 8 10 12) 31)
    ((4 6 9 11) 30)
    (2 (if (leap-year-p year) 29 28))
    (t 30)))

(defun days-before-year (year)
  "Number of days from the epoch (1970-01-01 == day 0) to YEAR-01-01, exact."
  ;; Mirror date.lisp DayFromYear but as an exact integer function.
  (+ (* 365 (- year 1970))
     (floor (- year 1969) 4)
     (- (floor (- year 1901) 100))
     (floor (- year 1601) 400)))

(defparameter +cumulative-days+ #(0 31 59 90 120 151 181 212 243 273 304 334))

(defun iso-date->epoch-days (iso)
  "Days from the epoch to ISO (year month day). Exact."
  (let* ((y (iso-date-year iso)) (m (iso-date-month iso)) (d (iso-date-day iso))
         (leap (if (and (>= m 3) (leap-year-p y)) 1 0)))
    (+ (days-before-year y)
       (aref +cumulative-days+ (1- m))
       leap
       (1- d))))

(defun epoch-days->iso-date (days)
  "Inverse of iso-date->epoch-days: DAYS since epoch -> (iso-date y m d)."
  ;; Find the year by stepping from an estimate.
  (let ((year (+ 1970 (floor days 366))))
    (loop while (> (days-before-year (1+ year)) days) do (decf year))
    (loop while (<= (days-before-year (1+ year)) days) do (incf year))
    (let ((doy (- days (days-before-year year)))  ; 0-based day of year
          (month 1))
      (loop for dim = (days-in-month year month)
            while (>= doy dim)
            do (decf doy dim) (incf month))
      (make-iso-date year month (1+ doy)))))

(defun iso-day-of-week (iso)
  "1 (Monday) .. 7 (Sunday), per ISO-8601."
  (let ((d (mod (+ (iso-date->epoch-days iso) 3) 7)))  ; 1970-01-01 is a Thursday
    (1+ d)))

;;; ===========================================================================
;;; Time balancing
;;; ===========================================================================
(defun balance-time (hour minute second ms us ns)
  "Normalize a (possibly out-of-range / carrying) time into a canonical
   iso-time plus a day-carry. Returns (values day-carry iso-time). All inputs
   are integers (may be negative)."
  (let* ((total-ns (+ ns
                      (* us +ns-per-us+)
                      (* ms +ns-per-ms+)
                      (* second +ns-per-s+)
                      (* minute +ns-per-min+)
                      (* hour +ns-per-hour+)))
         (day (floor total-ns +ns-per-day+))
         (rem (- total-ns (* day +ns-per-day+))))
    (multiple-value-bind (h r1) (floor rem +ns-per-hour+)
      (multiple-value-bind (mi r2) (floor r1 +ns-per-min+)
        (multiple-value-bind (s r3) (floor r2 +ns-per-s+)
          (multiple-value-bind (mss r4) (floor r3 +ns-per-ms+)
            (multiple-value-bind (uss nss) (floor r4 +ns-per-us+)
              (values day (make-iso-time h mi s mss uss nss)))))))))

;;; ===========================================================================
;;; Epoch <-> ISO datetime
;;; ===========================================================================
(defun iso-datetime->epoch-ns (date time)
  "UTC epoch nanoseconds for an ISO date + time. Exact integer."
  (+ (* (iso-date->epoch-days date) +ns-per-day+)
     (* (iso-time-hour time) +ns-per-hour+)
     (* (iso-time-minute time) +ns-per-min+)
     (* (iso-time-second time) +ns-per-s+)
     (* (iso-time-millisecond time) +ns-per-ms+)
     (* (iso-time-microsecond time) +ns-per-us+)
     (iso-time-nanosecond time)))

(defun epoch-ns->iso-datetime (ns)
  "Inverse: split epoch NS into (values iso-date iso-time)."
  (multiple-value-bind (days rem) (floor ns +ns-per-day+)
    (multiple-value-bind (carry time) (balance-time 0 0 0 0 0 rem)
      (values (epoch-days->iso-date (+ days carry)) time))))

(defun valid-epoch-ns-p (ns) (<= +ns-min+ ns +ns-max+))

(defun iso-datetime-in-range-p (date)
  "IsValidISODate + range: the datetime (date at midnight) fits within the
   instant range extended by one day either side (per ISODateTimeWithinLimits)."
  (let ((days (iso-date->epoch-days date)))
    (<= (- (floor +ns-min+ +ns-per-day+) 1) days
        (+ (floor +ns-max+ +ns-per-day+) 1))))

;;; ===========================================================================
;;; Rounding engine — exact, over CL rationals. All 9 modes.
;;; ===========================================================================
(defun apply-rounding-mode (quotient mode)
  "QUOTIENT is a CL rational. Return the integer nearest per MODE. FL is the
   floor and CE=FL+1 the ceiling; the value lies FRAC above FL (0<=FRAC<1). The
   two candidates are always FL and CE; the mode picks between them. For the
   half-* modes only the exact tie (FRAC=1/2) is mode-dependent."
  (multiple-value-bind (fl frac) (floor quotient)
    (if (zerop frac)
        fl
        (let ((ce (1+ fl))
              (pos (plusp quotient)))
          (ecase mode
            (:ceil  ce)
            (:floor fl)
            (:expand (if pos ce fl))   ; away from zero
            (:trunc  (if pos fl ce))   ; toward zero
            ;; nearest: FRAC>1/2 -> CE, FRAC<1/2 -> FL, tie broken by mode.
            (:half-ceil   (cond ((> frac 1/2) ce) ((< frac 1/2) fl) (t ce)))
            (:half-floor  (cond ((> frac 1/2) ce) ((< frac 1/2) fl) (t fl)))
            (:half-expand (cond ((> frac 1/2) ce) ((< frac 1/2) fl) (t (if pos ce fl))))
            (:half-trunc  (cond ((> frac 1/2) ce) ((< frac 1/2) fl) (t (if pos fl ce))))
            (:half-even   (cond ((> frac 1/2) ce) ((< frac 1/2) fl) (t (if (evenp fl) fl ce)))))))))

(defun round-to-increment (x increment mode)
  "RoundNumberToIncrement: round X (an exact integer/rational) to the nearest
   multiple of INCREMENT (positive integer) per MODE; return that integer multiple."
  (* increment (apply-rounding-mode (/ x increment) mode)))

(defun round-to-increment-as-if-positive (x increment mode)
  "RoundNumberToIncrementAsIfPositive: round X to a multiple of INCREMENT as
   though X were positive — i.e. 'ceil'/'expand' always mean toward +infinity and
   'floor'/'trunc' toward -infinity, regardless of X's actual sign. Used by
   Instant.round (spec: the sign is NOT reapplied to flip the rounding
   direction). Half-modes map halfExpand->halfCeil, halfTrunc->halfFloor."
  (let ((m (ecase mode
             (:ceil :ceil) (:expand :ceil)
             (:floor :floor) (:trunc :floor)
             (:half-ceil :half-ceil) (:half-expand :half-ceil)
             (:half-floor :half-floor) (:half-trunc :half-floor)
             (:half-even :half-even))))
    (round-to-increment x increment m)))

(defun validate-rounding-increment (increment max inclusive)
  "ValidateTemporalRoundingIncrement: INCREMENT must be an integer in
   [1, MAX) (or [1, MAX] when INCLUSIVE); RangeError otherwise."
  (let ((lim (if inclusive max (1- max))))
    (when (or (< increment 1) (> increment lim))
      (js-throw (make-native-error "RangeError" "rounding increment out of range")))
    increment))

;;; ===========================================================================
;;; Options object + observable readers (spec order = ALPHABETICAL by key)
;;; ===========================================================================
(defun get-options-object (v)
  "GetOptionsObject: undefined -> a fresh null options carrier (we use NIL);
   an object is returned as-is; anything else -> TypeError."
  (cond ((js-undefined-p v) nil)
        ((js-object-p v) v)
        (t (js-throw (make-native-error "TypeError" "options must be an object or undefined")))))

(defun %opt-get (options key)
  "Get OPTIONS[key] (undefined when OPTIONS is the empty NIL carrier)."
  (if options (js-get options key) *undefined*))

(defun get-option-string (options key allowed default)
  "GetOption(options, key, string, ALLOWED, DEFAULT). ALLOWED is a list of
   (jsname . keyword). Reads options[key]; if undefined uses DEFAULT (a keyword
   or :required). ToString'd then matched (observable: get + toString + call)."
  (let ((v (%opt-get options key)))
    (if (js-undefined-p v)
        (if (eq default :required)
            (js-throw (make-native-error "RangeError" "required option missing"))
            default)
        (let* ((s (to-string v))
               (hit (assoc s allowed :test #'string=)))
          (if hit (cdr hit)
              (js-throw (make-native-error "RangeError"
                          (format nil "invalid value for option ~a" key))))))))

(defun get-temporal-overflow (options)
  "ToTemporalOverflow: 'constrain' (default) | 'reject'."
  (get-option-string options "overflow"
                     '(("constrain" . :constrain) ("reject" . :reject))
                     :constrain))

(defparameter +rounding-modes+
  '(("ceil" . :ceil) ("floor" . :floor) ("expand" . :expand) ("trunc" . :trunc)
    ("halfCeil" . :half-ceil) ("halfFloor" . :half-floor)
    ("halfExpand" . :half-expand) ("halfTrunc" . :half-trunc)
    ("halfEven" . :half-even)))

(defun get-rounding-mode (options default)
  "GetRoundingModeOption. DEFAULT is a mode keyword."
  (get-option-string options "roundingMode" +rounding-modes+ default))

(defun negate-rounding-mode (mode)
  "NegateRoundingMode: ceil<->floor, halfCeil<->halfFloor; expand/trunc/halfExpand/
   halfTrunc/halfEven unchanged."
  (case mode
    (:ceil :floor) (:floor :ceil)
    (:half-ceil :half-floor) (:half-floor :half-ceil)
    (t mode)))

(defun get-rounding-increment (options)
  "GetRoundingIncrementOption: reads options.roundingIncrement, ToNumber,
   must be a finite integer >= 1 (default 1). Observable via valueOf."
  (let ((v (%opt-get options "roundingIncrement")))
    (if (js-undefined-p v)
        1
        (let ((n (to-number v)))
          (when (or (js-nan-p n) (= n *inf*) (= n *-inf*))
            (js-throw (make-native-error "RangeError" "roundingIncrement must be finite")))
          ;; truncate(n) — a non-integer is truncated toward zero, not rejected.
          (let ((iv (truncate (with-js-floats (ftruncate n)))))
            (when (or (< iv 1) (> iv 1000000000))
              (js-throw (make-native-error "RangeError" "roundingIncrement out of range")))
            iv)))))

(defun get-fractional-second-digits (options)
  "GetTemporalFractionalSecondDigitsOption: 'auto' (default) or an integer 0..9.
   ToNumber is NOT applied to 'auto'; a number is floored and range-checked."
  (let ((v (%opt-get options "fractionalSecondDigits")))
    (cond ((js-undefined-p v) :auto)
          ((not (floatp v))
           ;; Not a Number: ToString and require "auto".
           (let ((s (to-string v)))
             (if (string= s "auto") :auto
                 (js-throw (make-native-error "RangeError" "fractionalSecondDigits must be 'auto' or 0-9")))))
          (t
           (when (or (js-nan-p v) (= v *inf*) (= v *-inf*))
             (js-throw (make-native-error "RangeError" "fractionalSecondDigits out of range")))
           (let ((i (truncate (with-js-floats (ffloor v)))))
             (when (or (< i 0) (> i 9))
               (js-throw (make-native-error "RangeError" "fractionalSecondDigits out of range")))
             i)))))

;;; Temporal unit tables. Each entry: (jsname singular plural . keyword-unit)
;;; We accept both singular and plural spellings for all units.
(defparameter +temporal-units+
  ;; (keyword  singular  plural)
  '((:year        "year"        "years")
    (:month       "month"       "months")
    (:week        "week"        "weeks")
    (:day         "day"         "days")
    (:hour        "hour"        "hours")
    (:minute      "minute"      "minutes")
    (:second      "second"      "seconds")
    (:millisecond "millisecond" "milliseconds")
    (:microsecond "microsecond" "microseconds")
    (:nanosecond  "nanosecond"  "nanoseconds")))

(defun unit-alist (allowed &optional extra)
  "Build a (string . keyword) alist for the ALLOWED unit keywords (both
   spellings). EXTRA is extra (string . keyword) pairs (e.g. 'auto')."
  (let ((out (copy-list extra)))
    (dolist (u +temporal-units+ (nreverse out))
      (when (member (first u) allowed)
        (push (cons (second u) (first u)) out)
        (push (cons (third u) (first u)) out)))))

(defun get-temporal-unit (options key kind default allowed &optional extra)
  "GetTemporalUnitValuedOption. KEY = property key. DEFAULT is a unit keyword,
   NIL (meaning undefined->NIL result), or :required. ALLOWED = list of unit
   keywords accepted. EXTRA = extra (string . keyword) pairs (e.g. auto).
   Observable: get + toString + call."
  (declare (ignore kind))
  (let ((v (%opt-get options key))
        (table (unit-alist allowed extra)))
    (if (js-undefined-p v)
        (cond ((eq default :required)
               (js-throw (make-native-error "RangeError" (format nil "~a is required" key))))
              ((null default) nil)
              (t default))
        (let* ((s (to-string v))
               (hit (assoc s table :test #'string=)))
          (cond (hit (cdr hit))
                (t (js-throw (make-native-error "RangeError"
                               (format nil "invalid unit for ~a" key)))))))))

;;; ===========================================================================
;;; Time-zone offset parsing / formatting (UTC + fixed offsets only)
;;; ===========================================================================
(defun parse-offset-string (s &optional (start 0) (end (length s)))
  "Parse a UTC offset at S[START:END]: +-HH, +-HH:MM, +-HHMM, +-HH:MM:SS[.f],
   +-HHMMSS[.f]. Returns (values offset-ns next-index) or NIL. Sub-minute
   precision is allowed (offsets can carry seconds + fractional seconds)."
  (when (>= start end) (return-from parse-offset-string nil))
  (let ((sign (case (char s start) (#\+ 1) (#\- -1) (t nil))))
    (unless sign (return-from parse-offset-string nil))
    (let ((i (1+ start)))
      (flet ((two () (when (and (<= (+ i 2) end)
                                (digit-char-p (char s i)) (digit-char-p (char s (1+ i))))
                       (prog1 (+ (* 10 (digit-char-p (char s i))) (digit-char-p (char s (1+ i))))
                         (incf i 2)))))
        (let ((hh (two)))
          (unless hh (return-from parse-offset-string nil))
          (let ((mm 0) (ss 0) (frac-ns 0) (colon nil) (sub-minute-form nil))
            (when (and (< i end) (char= (char s i) #\:)) (incf i) (setf colon t))
            (let ((m (two))) (when m (setf mm m)))
            ;; Separator usage must be consistent: if minutes used a colon, the
            ;; seconds separator must be a colon too (and vice versa).
            (let ((sep (and (< i end) (char= (char s i) #\:))))
              (cond (sep (unless colon (return-from parse-offset-string nil)) (incf i)
                         (let ((sec (two))) (when sec (setf ss sec sub-minute-form t))))
                    ((and (not colon) (< i end) (digit-char-p (char s i)))
                     (let ((sec (two))) (when sec (setf ss sec sub-minute-form t))))))
            (when (and (< i end) (member (char s i) '(#\. #\,)))
              (incf i) (setf sub-minute-form t)
              (let ((digs 0) (val 0))
                (loop while (and (< i end) (digit-char-p (char s i)) (< digs 9))
                      do (setf val (+ (* val 10) (digit-char-p (char s i)))) (incf i) (incf digs))
                (when (zerop digs) (return-from parse-offset-string nil))
                (setf frac-ns (* val (expt 10 (- 9 digs))))))
            (when (or (> hh 23) (> mm 59) (> ss 59))
              (return-from parse-offset-string nil))
            ;; Third value: whether the offset FORM carried a seconds/fractional
            ;; component (sub-minute precision) — an offset time-zone identifier
            ;; must NOT (even if the value is minute-aligned, e.g. -07:00:00).
            (values (* sign (+ (* hh +ns-per-hour+) (* mm +ns-per-min+)
                               (* ss +ns-per-s+) frac-ns))
                    i sub-minute-form)))))))

(defun format-offset-ns (ns)
  "Format an offset in nanoseconds as +HH:MM (or with :SS[.fff] when sub-minute)."
  (let* ((sign (if (< ns 0) "-" "+"))
         (a (abs ns))
         (h (floor a +ns-per-hour+))
         (m (floor (mod a +ns-per-hour+) +ns-per-min+))
         (s (floor (mod a +ns-per-min+) +ns-per-s+))
         (sub (mod a +ns-per-s+)))
    (cond ((and (zerop s) (zerop sub))
           (format nil "~a~2,'0d:~2,'0d" sign h m))
          ((zerop sub)
           (format nil "~a~2,'0d:~2,'0d:~2,'0d" sign h m s))
          (t (format nil "~a~2,'0d:~2,'0d:~2,'0d.~a" sign h m s
                     (string-right-trim "0" (format nil "~9,'0d" sub)))))))

(defun offset-is-minute-precision-p (ns)
  "T if NS is an exact multiple of a minute (no sub-minute part)."
  (zerop (mod ns +ns-per-min+)))

;;; ===========================================================================
;;; ISO 8601 Temporal grammar parser
;;; ===========================================================================
;;; We parse into a plist. Keys: :year :month :day :hour :minute :second
;;; :millisecond :microsecond :nanosecond :offset (ns integer or NIL) :z (bool)
;;; :offset-present (bool) :calendar (string or NIL) :time-present (bool)
;;; :date-present (bool).

(defstruct pstate str pos len)

(defun p-peek (p &optional (k 0))
  (let ((i (+ (pstate-pos p) k)))
    (when (< i (pstate-len p)) (char (pstate-str p) i))))

(defun p-eof (p) (>= (pstate-pos p) (pstate-len p)))

(defun p-digit (p)
  (let ((c (p-peek p)))
    (when (and c (digit-char-p c))
      (incf (pstate-pos p))
      (digit-char-p c))))

(defun p-ndigits (p n)
  "Read exactly N digits -> integer, or NIL (rewinding on failure)."
  (let ((save (pstate-pos p)) (v 0))
    (dotimes (i n)
      (let ((d (p-digit p)))
        (unless d (setf (pstate-pos p) save) (return-from p-ndigits nil))
        (setf v (+ (* v 10) d))))
    v))

(defun p-char (p ch)
  (let ((c (p-peek p)))
    (when (and c (char-equal c ch)) (incf (pstate-pos p)) t)))

(defun p-fail () (js-throw (make-native-error "RangeError" "invalid ISO 8601 / Temporal string")))

(defun parse-date-part (p)
  "Parse a calendar date (year[-]month[-]day) into (values y m d). Supports
   extended sign+6-digit years. Signals via NIL on non-date."
  (let ((save (pstate-pos p)) (year nil))
    (let ((sign (case (p-peek p) (#\+ 1) (#\- -1) (t nil))))
      (if sign
          (progn (incf (pstate-pos p))
                 (let ((y (p-ndigits p 6)))
                   (unless y (setf (pstate-pos p) save) (return-from parse-date-part nil))
                   (when (and (= sign -1) (zerop y))
                     (p-fail))     ; -000000 is invalid
                   (setf year (* sign y))))
          (let ((y (p-ndigits p 4)))
            (unless y (return-from parse-date-part nil))
            (setf year y))))
    ;; month
    (let ((dash (p-char p #\-)))
      (let ((m (p-ndigits p 2)))
        (unless m (setf (pstate-pos p) save) (return-from parse-date-part nil))
        ;; day
        (when dash (unless (p-char p #\-) (setf (pstate-pos p) save) (return-from parse-date-part nil)))
        (let ((d (p-ndigits p 2)))
          (unless d (setf (pstate-pos p) save) (return-from parse-date-part nil))
          (values year m d))))))

(defun parse-time-part (p)
  "Parse a time HH[:MM[:SS[.fff]]] -> plist (:hour :minute :second :ms :us :ns)
   or NIL. Fractional seconds up to 9 digits -> ns."
  (let ((save (pstate-pos p)))
    (let ((hh (p-ndigits p 2)))
      (unless hh (return-from parse-time-part nil))
      (let ((mm 0) (ss 0) (ns-frac 0) (colon nil) (has-seconds nil))
        (when (p-char p #\:) (setf colon t))
        (let ((m (p-ndigits p 2)))
          (cond (m (setf mm m)
                   (if colon
                       (when (p-char p #\:)
                         (let ((s (p-ndigits p 2)))
                           (when s (setf ss s has-seconds t))))
                       (let ((s (p-ndigits p 2)))
                         (when s (setf ss s has-seconds t)))))
                (colon (setf (pstate-pos p) save) (return-from parse-time-part nil))))
        ;; fractional seconds — only permitted after a seconds component.
        (when (and (member (p-peek p) '(#\. #\,)) (not has-seconds))
          (setf (pstate-pos p) save) (return-from parse-time-part nil))
        (when (member (p-peek p) '(#\. #\,))
          (incf (pstate-pos p))
          (let ((digs 0) (val 0))
            (loop while (and (p-peek p) (digit-char-p (p-peek p)) (< digs 9))
                  do (setf val (+ (* val 10) (digit-char-p (p-peek p)))) (incf (pstate-pos p)) (incf digs))
            (when (zerop digs) (setf (pstate-pos p) save) (return-from parse-time-part nil))
            (setf ns-frac (* val (expt 10 (- 9 digs))))))
        ;; Leap second: a seconds value of 60 is accepted and clamped to 59.
        (when (= ss 60) (setf ss 59))
        (when (or (> hh 23) (> mm 59) (> ss 59))
          (p-fail))
        (multiple-value-bind (msv rem) (floor ns-frac +ns-per-ms+)
          (multiple-value-bind (usv nsv) (floor rem +ns-per-us+)
            (list :hour hh :minute mm :second ss :ms msv :us usv :ns nsv)))))))

(defun parse-annotations (p)
  "Parse zero or more [...] annotations. Returns (values calendar-id critical)
   where CALENDAR-ID is the first [u-ca=VALUE] value (string) or NIL, and
   CRITICAL is T if any calendar annotation carried the '!' critical flag.
   Handles the critical flag and time-zone annotations. A critical unknown
   annotation is a RangeError; a non-critical unknown one is ignored."
  (let ((calendar nil) (tz-count 0) (cal-count 0) (cal-critical nil))
    (flet ((valid-akey (s)     ; annotation key: [a-z_][a-z0-9_-]*
             (and (plusp (length s))
                  (or (char<= #\a (char s 0) #\z) (char= (char s 0) #\_))
                  (every (lambda (c) (or (char<= #\a c #\z) (digit-char-p c)
                                         (char= c #\-) (char= c #\_))) s)
                  (not (char= (char s (1- (length s))) #\-))))
           (valid-aval (s)     ; annotation value: alnum + hyphen groups
             (and (plusp (length s))
                  (every (lambda (c) (or (alpha-char-p c) (digit-char-p c) (char= c #\-))) s))))
      (loop while (p-char p #\[) do
        (let ((critical (p-char p #\!))
              (start (pstate-pos p)))
          (loop until (or (p-eof p) (char= (p-peek p) #\])) do (incf (pstate-pos p)))
          (let ((content (subseq (pstate-str p) start (pstate-pos p))))
            (unless (p-char p #\]) (p-fail))
            (let ((eq (position #\= content)))
              (cond
                (eq
                 ;; key=value annotation.
                 (let ((k (subseq content 0 eq)) (v (subseq content (1+ eq))))
                   (unless (and (valid-akey k) (valid-aval v)) (p-fail))
                   (cond
                     ((string= k "u-ca")
                      (incf cal-count)
                      (when critical (setf cal-critical t))
                      (when (and (> cal-count 1) cal-critical) (p-fail))
                      (when (null calendar) (setf calendar v)))
                     (t
                      ;; Unknown key=value annotation: critical -> RangeError,
                      ;; else ignored.
                      (when critical (p-fail))))))
                (t
                 ;; Bare annotation = a time-zone annotation (e.g. [UTC], [+01:00],
                 ;; [NotATimeZone]). At most one is allowed. An offset-form TZ
                 ;; annotation must be MINUTE precision — a sub-minute offset (any
                 ;; seconds and/or fractional-seconds component, e.g. [-07:00:01]
                 ;; or [-07:00:00.5]) is NOT a valid time-zone identifier.
                 (incf tz-count)
                 (when (> tz-count 1) (p-fail))
                 (when (and (plusp (length content))
                            (member (char content 0) '(#\+ #\-)))
                   (multiple-value-bind (off nx sub)
                       (parse-offset-string content 0 (length content))
                     (when (and off (= nx (length content)) sub)
                       (p-fail)))))))))))
    (values calendar cal-critical)))

(defun parse-iso-datetime (s kind)
  "Parse a Temporal date/datetime string. KIND selects the accepted shape:
     :instant   requires a time + (Z or numeric offset).
     :datetime  date, optional time, optional offset/annotations.
     :time      a time (possibly with a leading date or a bare T).
   Returns a plist with keys :year :month :day :hour :minute :second :ms :us :ns
   :offset (ns|nil) :z (bool) :offset-present (bool) :time-present (bool)."
  (let* ((p (make-pstate :str s :pos 0 :len (length s)))
         (year nil) (month 1) (day 1) (t-designator nil)
         (time nil) (offset nil) (z nil) (offset-present nil) (offset-sub-minute nil)
         (date-present nil) (time-present nil) (calendar nil) (calendar-critical nil))
    ;; Optional leading date.
    (when (and (not (eq kind :time))
               (member (p-peek p) '(#\+ #\-) :test #'eql))
      ;; extended-year date required
      (multiple-value-bind (y m d) (parse-date-part p)
        (unless y (p-fail))
        (setf year y month m day d date-present t)))
    (unless date-present
      (multiple-value-bind (y m d) (parse-date-part p)
        (when y (setf year y month m day d date-present t))))
    ;; Date/time separator or bare time.
    (cond
      (date-present
       (when (member (p-peek p) '(#\T #\t #\Space))
         (incf (pstate-pos p))
         (let ((tm (parse-time-part p)))
           (unless tm (p-fail))
           (setf time tm time-present t))))
      ((eq kind :time)
       ;; No date: a bare time (optionally with a leading T designator).
       (when (member (p-peek p) '(#\T #\t))
         (incf (pstate-pos p)) (setf t-designator t))
       (let ((tm (parse-time-part p)))
         (unless tm (p-fail))
         (setf time tm time-present t)))
      (t
       ;; :instant / :datetime with no calendar date -> not valid.
       (p-fail)))
    ;; UTC designator or numeric offset (only after a time).
    (when time-present
      (cond
        ((member (p-peek p) '(#\Z #\z))
         (incf (pstate-pos p)) (setf z t offset 0 offset-present t))
        ((member (p-peek p) '(#\+ #\-) :test #'eql)
         (multiple-value-bind (off nx sub) (parse-offset-string s (pstate-pos p))
           (unless off (p-fail))
           (setf offset off offset-present t offset-sub-minute sub (pstate-pos p) nx)))))
    ;; Annotations — surface the [u-ca=...] calendar id (+ its critical flag).
    (multiple-value-bind (cal cal-critical) (parse-annotations p)
      (setf calendar cal calendar-critical cal-critical))
    ;; Must be fully consumed.
    (unless (p-eof p) (p-fail))
    ;; KIND-specific requirements.
    (when (and (eq kind :instant) (not offset-present)) (p-fail))
    (when (and (eq kind :instant) (not time-present)) (p-fail))
    ;; An instant/datetime requires a full calendar date (year+month+day).
    (when (and (member kind '(:instant :datetime)) (or (null year) (not date-present)))
      (p-fail))
    (list :year (or year 0) :month month :day day
          :hour (if time (getf time :hour) 0)
          :minute (if time (getf time :minute) 0)
          :second (if time (getf time :second) 0)
          :ms (if time (getf time :ms) 0)
          :us (if time (getf time :us) 0)
          :ns (if time (getf time :ns) 0)
          :offset offset :z z :offset-present offset-present
          :offset-sub-minute offset-sub-minute
          :calendar calendar :calendar-critical calendar-critical
          :time-present time-present :date-present date-present
          :t-designator t-designator)))

(defun date-shaped-ambiguous-p (s)
  "T if S (a bare time candidate with no T designator) could ALSO be read as a
   valid reduced calendar-date string, making it ambiguous per the Temporal
   grammar: it then requires a T prefix to be a PlainTime. Covers the reduced
   date productions YYYY-MM, YYYYMM, MMDD, MM-DD (plus optional annotations),
   as exercised by plainTimeStringsAmbiguous/Unambiguous."
  (let* ((br (or (position #\[ s) (length s)))
         (core (subseq s 0 br))
         (rest (subseq s br)))
    (flet ((digits-p (a b) (and (<= b (length core))
                                (loop for i from a below b always (digit-char-p (char core i)))))
           (ann-ok () (handler-case
                          (let ((p (make-pstate :str rest :pos 0 :len (length rest))))
                            (parse-annotations p) (p-eof p))
                        (shuttle-error () nil))))
      (and (ann-ok)
           (cond
             ;; YYYY-MM (4-2 with dash)
             ((and (= (length core) 7) (char= (char core 4) #\-) (digits-p 0 4) (digits-p 5 7))
              (<= 1 (parse-integer core :start 5 :end 7) 12))
             ;; YYYYMM (6 digits) — the last two are a month (01..12)
             ((and (= (length core) 6) (digits-p 0 6))
              (<= 1 (parse-integer core :start 4 :end 6) 12))
             ;; MMDD (4 digits): valid month 01..12 and day valid for a leap-safe month
             ((and (= (length core) 4) (digits-p 0 4))
              (let ((mm (parse-integer core :start 0 :end 2))
                    (dd (parse-integer core :start 2 :end 4)))
                (and (<= 1 mm 12) (<= 1 dd (days-in-month 2000 mm)))))
             ;; MM-DD (2-2 with dash)
             ((and (= (length core) 5) (char= (char core 2) #\-) (digits-p 0 2) (digits-p 3 5))
              (let ((mm (parse-integer core :start 0 :end 2))
                    (dd (parse-integer core :start 3 :end 5)))
                (and (<= 1 mm 12) (<= 1 dd (days-in-month 2000 mm)))))
             (t nil))))))

(defun parse-temporal-instant (s)
  "Parse an Instant string -> exact epoch ns. RangeError on malformed or
   out-of-range."
  (let* ((s (string-trim '(#\Space #\Tab #\Newline #\Return) s))
         (r (parse-iso-datetime s :instant))
         (date (make-iso-date (getf r :year) (getf r :month) (getf r :day)))
         (time (make-iso-time (getf r :hour) (getf r :minute) (getf r :second)
                              (getf r :ms) (getf r :us) (getf r :ns))))
    (unless (valid-iso-date-p date) (p-fail))
    (let* ((offset (or (getf r :offset) 0))
           (ns (- (iso-datetime->epoch-ns date time) offset)))
      (unless (valid-epoch-ns-p ns)
        (js-throw (make-native-error "RangeError" "Instant out of range")))
      ns)))

(defun valid-iso-date-p (date)
  (let ((y (iso-date-year date)) (m (iso-date-month date)) (d (iso-date-day date)))
    (and (<= 1 m 12) (<= 1 d (days-in-month y m)))))

(defun parse-temporal-time (s)
  "Parse a PlainTime string -> iso-time. Accepts time-only and datetime forms
   but NOT a UTC designator (Z) — a wall-clock time has no zone. RangeError on
   malformed."
  ;; Ambiguity: a bare (no-T, no leading date) string that could also be read as
  ;; a reduced calendar date requires a T prefix to be a PlainTime.
  (when (and (plusp (length s))
             (not (member (char s 0) '(#\T #\t)))
             (date-shaped-ambiguous-p s))
    (p-fail))
  (let ((r (parse-iso-datetime s :time)))
    (unless (getf r :time-present) (p-fail))
    ;; A UTC designator makes the string a zoned instant, not a wall-clock time.
    (when (getf r :z) (p-fail))
    (make-iso-time (getf r :hour) (getf r :minute) (getf r :second)
                   (getf r :ms) (getf r :us) (getf r :ns))))

;;; ===========================================================================
;;; Duration parsing / records
;;; ===========================================================================
(defparameter +duration-fields+
  '(:years :months :weeks :days :hours :minutes :seconds
    :milliseconds :microseconds :nanoseconds))

(defun empty-duration () (list :years 0 :months 0 :weeks 0 :days 0 :hours 0
                               :minutes 0 :seconds 0 :milliseconds 0
                               :microseconds 0 :nanoseconds 0))

(defun parse-temporal-duration (s)
  "Parse an ISO-8601 duration string (P[n]Y[n]M[n]W[n]D[T[n]H[n]M[n]S]). A
   fraction is allowed ONLY on the final present component of H/M/S (and never on
   a date unit); the fractional value CASCADES down the finer time units
   (hours->minutes->seconds->subsecond, minutes->seconds->subsecond,
   seconds->subsecond), exactly per the spec — NOT dumped into seconds. Returns a
   duration plist. RangeError on malformed. This is the single duration-string
   parser for the whole Temporal surface."
  (let* ((s (string-trim '(#\Space #\Tab #\Newline #\Return) s))
         (p (make-pstate :str s :pos 0 :len (length s)))
         (sign 1))
    (case (p-peek p) (#\+ (incf (pstate-pos p))) ((#\-) (setf sign -1) (incf (pstate-pos p))))
    (unless (p-char p #\P) (p-fail))
    (let ((years 0) (months 0) (weeks 0) (days 0)
          (hours 0) (minutes 0) (seconds 0) (sub-ns 0)
          (any nil) (in-time nil) (frac-used nil))
      (labels ((read-num ()
                 "Read an unsigned integer + optional fraction after . or ,.
                  Returns (values int-part frac-rational had-fraction)."
                 (let ((start (pstate-pos p)) (v 0) (n 0))
                   (loop while (and (p-peek p) (digit-char-p (p-peek p)))
                         do (setf v (+ (* v 10) (digit-char-p (p-peek p)))) (incf (pstate-pos p)) (incf n))
                   (when (zerop n) (setf (pstate-pos p) start) (return-from read-num (values nil 0 nil)))
                   (let ((fr 0) (had nil))
                     (when (member (p-peek p) '(#\. #\,))
                       (incf (pstate-pos p)) (setf had t)
                       (let ((num 0) (den 1) (fn 0))
                         (loop while (and (p-peek p) (digit-char-p (p-peek p)))
                               do (setf num (+ (* num 10) (digit-char-p (p-peek p))) den (* den 10))
                                  (incf (pstate-pos p)) (incf fn))
                         ;; 1..9 fractional digits only (ISO Temporal grammar).
                         (when (or (zerop fn) (> fn 9)) (p-fail))
                         (setf fr (/ num den))))
                     (values v fr had)))))
        (loop
          (let ((c (p-peek p)))
            (cond
              ((null c) (return))
              ((and (not in-time) (member c '(#\T #\t)))
               (incf (pstate-pos p)) (setf in-time t))
              (t
               ;; Nothing may follow a fractional component.
               (when frac-used (p-fail))
               (multiple-value-bind (v fr had) (read-num)
                 (unless v (p-fail))
                 (let ((desig (p-peek p)))
                   (unless desig (p-fail))
                   (incf (pstate-pos p))
                   (setf any t)
                   (when had (setf frac-used t))
                   (if (not in-time)
                       (progn
                         (when (plusp fr) (p-fail))  ; date units may not be fractional
                         (case (char-upcase desig)
                           (#\Y (setf years v)) (#\M (setf months v))
                           (#\W (setf weeks v)) (#\D (setf days v))
                           (t (p-fail))))
                       (case (char-upcase desig)
                         (#\H (setf hours v)
                              (when (plusp fr)
                                ;; cascade: frac hours -> minutes -> seconds -> subsec
                                (let* ((fm (* fr 60)) (wm (floor fm)))
                                  (setf minutes wm)
                                  (let* ((fs (* (- fm wm) 60)) (ws (floor fs)))
                                    (setf seconds ws sub-ns (floor (* (- fs ws) +ns-per-s+)))))))
                         (#\M (setf minutes v)
                              (when (plusp fr)
                                (let* ((fs (* fr 60)) (ws (floor fs)))
                                  (setf seconds ws sub-ns (floor (* (- fs ws) +ns-per-s+))))))
                         (#\S (setf seconds v)
                              (when (plusp fr)
                                (setf sub-ns (floor (* fr +ns-per-s+)))))
                         (t (p-fail)))))))))))
      (unless any (p-fail))
      (multiple-value-bind (ms r1) (floor sub-ns +ns-per-ms+)
        (multiple-value-bind (us ns) (floor r1 +ns-per-us+)
          (flet ((m (x) (* sign x)))
            (list :years (m years) :months (m months) :weeks (m weeks) :days (m days)
                  :hours (m hours) :minutes (m minutes) :seconds (m seconds)
                  :milliseconds (m ms) :microseconds (m us) :nanoseconds (m ns))))))))

(defun duration-time-ns (d)
  "Total nanoseconds of the time components (hours..nanoseconds), exact."
  (+ (* (getf d :hours) +ns-per-hour+)
     (* (getf d :minutes) +ns-per-min+)
     (* (getf d :seconds) +ns-per-s+)
     (* (getf d :milliseconds) +ns-per-ms+)
     (* (getf d :microseconds) +ns-per-us+)
     (getf d :nanoseconds)))

(defun duration-sign (d)
  (dolist (f +duration-fields+ 0)
    (let ((v (getf d f)))
      (cond ((plusp v) (return 1)) ((minusp v) (return -1))))))

(defun validate-duration (d)
  "Reject: mixed signs, or non-integer / infinite components. Components in a
   duration plist are already CL integers here, so we only check sign coherence."
  (let ((sign 0))
    (dolist (f +duration-fields+)
      (let ((v (getf d f)))
        (cond ((plusp v) (if (minusp sign) (js-throw (make-native-error "RangeError" "mixed-sign duration")) (setf sign 1)))
              ((minusp v) (if (plusp sign) (js-throw (make-native-error "RangeError" "mixed-sign duration")) (setf sign -1))))))
    d))

(defun validate-duration-range (d)
  "IsValidDuration: sign coherence + magnitude limits. Only years/months/weeks
   are bounded by 2^32 in magnitude; DAYS is bounded solely by the total-time
   limit — the total time (days..nanoseconds, expressed in seconds) must be <
   2^53. RangeError otherwise. Returns D. This is the single IsValidDuration
   used by the whole Temporal surface."
  (validate-duration d)
  (dolist (f '(:years :months :weeks))
    (when (>= (abs (getf d f)) 4294967296)
      (js-throw (make-native-error "RangeError" "duration component out of range"))))
  ;; The total time (days as 24h + time part) in seconds must be strictly < 2^53
  ;; in magnitude. Max valid is 9007199254740991.999999999 s, so compare the exact
  ;; ns total to 2^53 * 1e9.
  (let ((total-ns (+ (* (getf d :days) +ns-per-day+) (duration-time-ns d))))
    (when (>= (abs total-ns) (* (expt 2 53) +ns-per-s+))
      (js-throw (make-native-error "RangeError" "duration out of range"))))
  d)

(defun bag-duration-field (bag key)
  "Read one duration field from a property bag: undefined -> 0; else ToNumber,
   must be an integer, finite; RangeError otherwise."
  (let ((v (js-get bag key)))
    (if (js-undefined-p v)
        0
        (let ((n (to-number v)))
          (when (or (js-nan-p n) (= n *inf*) (= n *-inf*))
            (js-throw (make-native-error "RangeError" "duration field must be finite")))
          (let ((i (with-js-floats (ftruncate n))))
            (when (/= i n)
              (js-throw (make-native-error "RangeError" "duration field must be an integer")))
            (truncate i))))))

(defparameter +duration-bag-keys+
  ;; alphabetical order of property gets, with the plist keyword each maps to
  '(("days" . :days) ("hours" . :hours) ("microseconds" . :microseconds)
    ("milliseconds" . :milliseconds) ("minutes" . :minutes) ("months" . :months)
    ("nanoseconds" . :nanoseconds) ("seconds" . :seconds) ("weeks" . :weeks)
    ("years" . :years)))

(defun to-temporal-duration-record (v)
  "ToTemporalDurationRecord: from a Duration instance (internal slot), a property
   bag (alphabetical observable reads), or a string. Returns a duration plist."
  (cond
    ((and (js-object-p v) (getf (js-object-internal v) :temporal-duration))
     (copy-list (getf (js-object-internal v) :temporal-duration)))
    ((js-object-p v)
     (let ((d (empty-duration)) (any nil))
       (dolist (pair +duration-bag-keys+)
         (let ((val (js-get v (car pair))))
           (unless (js-undefined-p val)
             (setf any t)
             (let ((n (to-number val)))
               (when (or (js-nan-p n) (= n *inf*) (= n *-inf*))
                 (js-throw (make-native-error "RangeError" "duration field must be finite")))
               (let ((i (with-js-floats (ftruncate n))))
                 (when (/= i n)
                   (js-throw (make-native-error "RangeError" "duration field must be an integer")))
                 (setf (getf d (cdr pair)) (truncate i)))))))
       (unless any
         (js-throw (make-native-error "TypeError" "invalid duration-like object")))
       (validate-duration d)))
    ((stringp v) (validate-duration (parse-temporal-duration v)))
    (t (js-throw (make-native-error "TypeError" "cannot convert to a Temporal.Duration")))))

;;; ===========================================================================
;;; Formatter
;;; ===========================================================================
(defun format-fractional (sub-second-ns digits)
  "Format the fractional-second part (0..999999999 ns). DIGITS is :auto or 0..9.
   Returns a string beginning with '.' or the empty string."
  (cond
    ((eql digits 0) "")
    ((eq digits :auto)
     (if (zerop sub-second-ns) ""
         (concatenate 'string "." (string-right-trim "0" (format nil "~9,'0d" sub-second-ns)))))
    (t (concatenate 'string "."
                    (subseq (format nil "~9,'0d" sub-second-ns) 0 digits)))))

(defun format-iso-time (time digits)
  "Format HH:MM:SS[.fff] for an iso-time; DIGITS = :auto | 0..9."
  (let ((sub (+ (* (iso-time-millisecond time) +ns-per-ms+)
                (* (iso-time-microsecond time) +ns-per-us+)
                (iso-time-nanosecond time))))
    (format nil "~2,'0d:~2,'0d:~2,'0d~a"
            (iso-time-hour time) (iso-time-minute time) (iso-time-second time)
            (format-fractional sub digits))))

(defun format-iso-year (y)
  (cond ((<= 0 y 9999) (format nil "~4,'0d" y))
        ((minusp y) (format nil "-~6,'0d" (- y)))
        (t (format nil "+~6,'0d" y))))

(defun format-iso-date-string (y m d)
  (format nil "~a-~2,'0d-~2,'0d" (format-iso-year y) m d))

;;; ===========================================================================
;;; Difference settings (used by since/until)
;;; ===========================================================================
(defun get-difference-settings (op options smallest-default largest-default
                                allowed-smallest allowed-largest max-increment)
  "GetDifferenceSettings, spec-ordered reads: largestUnit, roundingIncrement,
   roundingMode, smallestUnit. OP is :since or :until (negates the rounding mode
   for :since). Returns (values smallest-unit largest-unit increment mode).
   ALLOWED-* are lists of unit keywords. SMALLEST-DEFAULT / LARGEST-DEFAULT are
   the fallback units. MAX-INCREMENT bounds the increment for this smallest unit."
  ;; All four options are READ and cast (largestUnit, roundingIncrement,
  ;; roundingMode, smallestUnit) BEFORE any algorithmic validation, so we cast
  ;; against the full unit table then validate membership afterwards.
  (let* ((all-units '(:year :month :week :day :hour :minute :second
                      :millisecond :microsecond :nanosecond))
         (largest (get-temporal-unit options "largestUnit" :datetime nil
                                     all-units '(("auto" . :auto))))
         (increment (get-rounding-increment options))
         (mode (get-rounding-mode options :trunc))
         (smallest (get-temporal-unit options "smallestUnit" :datetime nil
                                      all-units)))
    ;; Validate the units are allowed for this operation.
    (when (and largest (not (eq largest :auto)) (not (member largest allowed-largest)))
      (js-throw (make-native-error "RangeError" "largestUnit not allowed here")))
    (when (and smallest (not (member smallest allowed-smallest)))
      (js-throw (make-native-error "RangeError" "smallestUnit not allowed here")))
    (when (eq op :since) (setf mode (negate-rounding-mode mode)))
    (let* ((sm (or smallest smallest-default))
           ;; Default largestUnit = the coarser of smallestUnit and the caller's
           ;; default (a smallestUnit coarser than the default widens it).
           (lg (cond ((or (null largest) (eq largest :auto))
                      (if (< (unit-rank sm) (unit-rank largest-default)) sm largest-default))
                     (t largest))))
      ;; largestUnit must be at least as coarse as smallestUnit.
      (when (< (unit-rank sm) (unit-rank lg))
        (js-throw (make-native-error "RangeError" "smallestUnit is coarser than largestUnit")))
      ;; Increment validation. Calendar units (year/month/week/day) are unbounded
      ;; per spec — ValidateTemporalRoundingIncrement is called with the count of
      ;; the smallest unit in the next-coarser unit ONLY for time units (where the
      ;; increment must also divide evenly into that count). MAX-INCREMENT returns
      ;; NIL for a calendar unit (meaning: only require increment >= 1).
      (let ((maximum (funcall max-increment sm)))
        (cond
          (maximum
           (validate-rounding-increment increment maximum nil)
           (when (/= 0 (mod maximum increment))
             (js-throw (make-native-error "RangeError" "roundingIncrement does not divide evenly"))))
          (t
           ;; Unbounded calendar unit: just require a positive integer.
           (validate-rounding-increment increment most-positive-fixnum t))))
      (values sm lg increment mode))))

(defun unit-rank (unit)
  "Coarser units rank lower (year=0 .. nanosecond=9)."
  (position unit '(:year :month :week :day :hour :minute :second
                   :millisecond :microsecond :nanosecond)))

;;; ===========================================================================
;;; Temporal namespace + registration
;;; ===========================================================================
(defvar *temporal-namespace* nil
  "The realm's Temporal object, cached during install so type installers (which
   run after temporal-core) can hang their constructors on it.")
(defvar *temporal-tostringtag* nil)

(defun temporal-tag (realm) (symbol-tostringtag realm))

(defun temporal-namespace (realm)
  "Return the realm's Temporal object (installing it lazily if needed)."
  (or *temporal-namespace*
      (let ((existing (ignore-errors (js-get (realm-global realm) "Temporal"))))
        (when (js-object-p existing) (setf *temporal-namespace* existing)))))

(defun temporal-register (realm name ctor)
  "Hang NAME (e.g. \"PlainDate\") on the Temporal namespace as a non-enumerable,
   writable, configurable data property. Type installers call this."
  (let ((ns (temporal-namespace realm)))
    (when ns
      (put ns name ctor :enumerable nil :writable t :configurable t))))

(defun proto-from-newtarget (nt default-proto)
  "GetPrototypeFromConstructor(nt, default): reads nt.prototype (observable —
   may throw, per get-prototype-from-constructor-throws.js)."
  (if (js-object-p nt)
      (let ((p (js-get nt "prototype")))
        (if (js-object-p p) p default-proto))
      default-proto))

;;; ---- internal-slot branding ----------------------------------------------
(defun temporal-brand (o slot value)
  "Stamp SLOT (a keyword) = VALUE on O's internal plist."
  (setf (getf (js-object-internal o) slot) value)
  o)

(defparameter +temporal-brand-slots+
  '(:temporal-instant :temporal-plaintime :temporal-plaindate :temporal-plaindatetime
    :temporal-plainyearmonth :temporal-plainmonthday :temporal-zoneddatetime
    :temporal-duration)
  "The internal-slot keywords that brand a Temporal instance.")

(defun temporal-branded-object-p (v)
  "T if V is an object carrying any Temporal type brand (used to reject a Temporal
   instance where a plain property bag is required, e.g. PlainXxx.prototype.with)."
  (and (js-object-p v)
       (some (lambda (slot) (not (eq (getf (js-object-internal v) slot 'none) 'none)))
             +temporal-brand-slots+)))

(defun temporal-slot (this slot type-name)
  "RequireInternalSlot: read SLOT off THIS or TypeError with TYPE-NAME."
  (let ((v (if (js-object-p this)
               (getf (js-object-internal this) slot 'none)
               'none)))
    (when (eq v 'none)
      (js-throw (make-native-error "TypeError"
                  (format nil "receiver is not a ~a" type-name))))
    v))

;;; ===========================================================================
;;; Minimal Temporal.Duration
;;;
;;; The whole time-arithmetic surface (Instant/PlainTime add/subtract/until/
;;; since, and later ZonedDateTime/PlainDateTime) needs a real Temporal.Duration
;;; to accept and return. The kernel installs a working-but-minimal Duration so
;;; those methods function this round; the full Duration installer replaces it
;;; wholesale (its installer runs after this one and simply re-`temporal-register`s
;;; and re-`define-global`s). Values are stored as an exact-integer duration
;;; plist in the :temporal-duration internal slot; getters return JS doubles.
;;; ===========================================================================
(defvar *temporal-duration-proto* nil)

(defun duration-plist->fields-valid-p (d)
  "IsValidDuration lite: at most one sign across all fields."
  (handler-case (progn (validate-duration d) t)
    (shuttle-error () nil)))

(defun make-temporal-duration (realm d &optional new-target)
  "Create a Temporal.Duration instance from a duration plist D (exact integers).
   Uses the realm's Duration.prototype (or nt.prototype)."
  (declare (ignore realm))
  (let* ((proto (proto-from-newtarget new-target *temporal-duration-proto*))
         (o (make-object :proto proto :class "Object")))
    (setf (getf (js-object-internal o) :temporal-duration) (copy-list d))
    o))

(defun install-temporal-duration-min (realm)
  (let* ((op (realm-object-proto realm))
         (proto (make-object :proto op :class "Object"))
         (ctor (native-function realm "Duration"
                 (lambda (this args) (declare (ignore this args))
                   (js-throw (make-native-error "TypeError" "Constructor Duration requires 'new'")))
                 0)))
    (setf *temporal-duration-proto* proto)
    (setf (js-object-construct ctor)
          (lambda (args nt)
            ;; ToIntegerIfIntegral for each of the 10 positional args, in order.
            (flet ((fld (i)
                     (let ((v (arg i args)))
                       (if (js-undefined-p v) 0
                           (let ((n (to-number v)))
                             (when (or (js-nan-p n) (= n *inf*) (= n *-inf*))
                               (js-throw (make-native-error "RangeError" "duration field must be finite")))
                             (let ((k (with-js-floats (ftruncate n))))
                               (when (/= k n)
                                 (js-throw (make-native-error "RangeError" "duration field must be an integer")))
                               (truncate k)))))))
              (let ((d (list :years (fld 0) :months (fld 1) :weeks (fld 2) :days (fld 3)
                             :hours (fld 4) :minutes (fld 5) :seconds (fld 6)
                             :milliseconds (fld 7) :microseconds (fld 8) :nanoseconds (fld 9))))
                (validate-duration d)
                (let ((o (make-object :proto (proto-from-newtarget nt proto) :class "Object")))
                  (setf (getf (js-object-internal o) :temporal-duration) d)
                  o)))))
    (def-value ctor "prototype" proto :writable nil :configurable nil)
    (def-value proto "constructor" ctor)
    ;; from(): string | bag | instance -> Duration
    (def-method realm ctor "from" 1 (this args)
      (declare (ignore this))
      (let ((v (arg 0 args)))
        (make-temporal-duration realm (to-temporal-duration-record v))))
    ;; field getters (return JS doubles)
    (macrolet ((dgetter (name key)
                 `(def-getter realm proto ,name
                    (lambda (this args) (declare (ignore args))
                      (float (getf (temporal-slot this :temporal-duration "Temporal.Duration") ,key) 1d0)))))
      (dgetter "years" :years) (dgetter "months" :months) (dgetter "weeks" :weeks)
      (dgetter "days" :days) (dgetter "hours" :hours) (dgetter "minutes" :minutes)
      (dgetter "seconds" :seconds) (dgetter "milliseconds" :milliseconds)
      (dgetter "microseconds" :microseconds) (dgetter "nanoseconds" :nanoseconds))
    (def-getter realm proto "sign"
      (lambda (this args) (declare (ignore args))
        (float (duration-sign (temporal-slot this :temporal-duration "Temporal.Duration")) 1d0)))
    (def-getter realm proto "blank"
      (lambda (this args) (declare (ignore args))
        (js-bool (zerop (duration-sign (temporal-slot this :temporal-duration "Temporal.Duration"))))))
    (def-method realm proto "negated" 0 (this args)
      (let ((d (temporal-slot this :temporal-duration "Temporal.Duration")))
        (make-temporal-duration realm
          (loop for f in +duration-fields+ append (list f (- (getf d f)))))))
    (def-method realm proto "abs" 0 (this args)
      (let ((d (temporal-slot this :temporal-duration "Temporal.Duration")))
        (make-temporal-duration realm
          (loop for f in +duration-fields+ append (list f (abs (getf d f)))))))
    (put proto (symbol-tostringtag realm) "Temporal.Duration"
         :enumerable nil :writable nil :configurable t)
    (temporal-register realm "Duration" ctor)
    ctor))

;;; ===========================================================================
;;; install-temporal-core
;;; ===========================================================================
(defun install-temporal-core (realm)
  (setf *temporal-namespace* nil *temporal-tostringtag* nil)
  (let* ((op (realm-object-proto realm))
         (ns (make-object :proto op :class "Object")))
    (setf *temporal-namespace* ns)
    ;; @@toStringTag = "Temporal", non-writable, configurable.
    (put ns (symbol-tostringtag realm) "Temporal"
         :enumerable nil :writable nil :configurable t)
    ;; Global Temporal: non-enumerable, writable, configurable.
    (put (realm-global realm) "Temporal" ns :enumerable nil :writable t :configurable t)
    ;; Minimal Temporal.Duration (foundation for time arithmetic; the full installer
    ;; may replace it).
    (install-temporal-duration-min realm)))

(register-builtin-installer 'install-temporal-core)
