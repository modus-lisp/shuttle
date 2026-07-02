;;;; builtins/temporal-plainyearmonth.lisp — Temporal.PlainYearMonth.
;;;;
;;;; A year+month (no day) with a reference ISO day (default 1, or the parsed
;;;; day), stored as an iso-date record in the :temporal-plainyearmonth slot plus
;;;; a :temporal-calendar id. Built on the temporal-core kernel and the concurrent
;;;; PlainDate helpers (add-iso-date / difference-iso-date / regulate-iso-date /
;;;; create-iso-date-checked / make-plain-date / canonicalize-calendar-id /
;;;; get-calendar-name-option / format-calendar-annotation / monthcode-well-formed-p),
;;;; which are top-level documented functions in temporal-plaindate.lisp.
(in-package #:shuttle)

(defvar *temporal-plainyearmonth-proto* nil)

(defun temporal-require-string (v what)
  "The monthCode/calendar field coercion: ToPrimitive(V, string) then require the
   result be a String; TypeError otherwise. (A String primitive passes through
   ToPrimitive unchanged; an object's toString/valueOf are observed.)"
  (let ((p (to-primitive v :string)))
    (unless (stringp p)
      (js-throw (make-native-error "TypeError"
                  (format nil "~a must be a string" what))))
    p))

(defun temporal-branded-object-p (v)
  "T if V carries any Temporal internal-slot brand (a Temporal instance)."
  (and (js-object-p v)
       (let ((int (js-object-internal v)))
         (or (not (eq (getf int :temporal-plaindate 'none) 'none))
             (not (eq (getf int :temporal-plaindatetime 'none) 'none))
             (not (eq (getf int :temporal-plainmonthday 'none) 'none))
             (not (eq (getf int :temporal-plainyearmonth 'none) 'none))
             (not (eq (getf int :temporal-plaintime 'none) 'none))
             (not (eq (getf int :temporal-zoneddatetime 'none) 'none))
             (not (eq (getf int :temporal-duration 'none) 'none))
             (not (eq (getf int :temporal-instant 'none) 'none))))))

(defun require-partial-temporal-object (v)
  "IsPartialTemporalObject: V must be an object that is NOT a Temporal-branded
   instance and has no own calendar/timeZone property; else TypeError. (The
   calendar/timeZone getters are observed.) Returns V."
  (unless (and (js-object-p v) (not (temporal-branded-object-p v)))
    (js-throw (make-native-error "TypeError" "expected a partial Temporal property bag")))
  (unless (js-undefined-p (js-get v "calendar"))
    (js-throw (make-native-error "TypeError" "unexpected calendar property")))
  (unless (js-undefined-p (js-get v "timeZone"))
    (js-throw (make-native-error "TypeError" "unexpected timeZone property")))
  v)

(defun canonicalize-calendar-id-strict (v)
  "The CONSTRUCTOR's calendar coercion: V must be a string that equals
   \"iso8601\" (case-insensitive). Unlike ToTemporalCalendarIdentifier this does
   NOT accept an ISO date string carrying a [u-ca=...] annotation. Non-string ->
   TypeError; any other string -> RangeError."
  (cond
    ((not (stringp v)) (js-throw (make-native-error "TypeError" "calendar must be a string")))
    ((string-equal v "iso8601") "iso8601")
    (t (js-throw (make-native-error "RangeError" (format nil "unknown calendar: ~a" v))))))

(defun make-plain-year-month (iso-date calendar-id realm &optional new-target)
  "CreateTemporalYearMonth: ISO-DATE is a valid in-range iso-date whose DAY is the
   reference ISO day; CALENDAR-ID a canonical calendar id string."
  (declare (ignore realm))
  (let* ((proto (proto-from-newtarget new-target *temporal-plainyearmonth-proto*))
         (o (make-object :proto proto :class "Object")))
    (setf (getf (js-object-internal o) :temporal-plainyearmonth) iso-date)
    (setf (getf (js-object-internal o) :temporal-calendar) calendar-id)
    o))

(defun pym-iso-date (this)
  "RequireInternalSlot([[InitializedTemporalYearMonth]]) -> iso-date record."
  (temporal-slot this :temporal-plainyearmonth "Temporal.PlainYearMonth"))

(defun pym-calendar-id (this)
  (temporal-slot this :temporal-plainyearmonth "Temporal.PlainYearMonth")
  (getf (js-object-internal this) :temporal-calendar "iso8601"))

(defun plain-year-month-p (v)
  (and (js-object-p v)
       (not (eq (getf (js-object-internal v) :temporal-plainyearmonth 'none) 'none))))

;;; ISOYearMonthWithinLimits: the year-month is valid iff the first day of the
;;; month (for year<=min) / last day (for year>=max) sits inside the ISO limits.
;;; Concretely: reject year < -271821 or (= -271821 and month < 4); reject year >
;;; 275760 or (= 275760 and month > 9).
(defun iso-year-month-within-limits (year month)
  (cond ((< year +iso-year-min+) nil)
        ((and (= year +iso-year-min+) (< month 4)) nil)
        ((> year +iso-year-max+) nil)
        ((and (= year +iso-year-max+) (> month 9)) nil)
        (t t)))

(defun create-iso-year-month-checked (year month ref-day calendar realm &optional new-target)
  "Validate the (year, month) is within the year-month ISO limits, then build."
  (unless (and (<= 1 month 12) (iso-year-month-within-limits year month))
    (js-throw (make-native-error "RangeError" "PlainYearMonth is outside the representable range")))
  (make-plain-year-month (make-iso-date year month ref-day) calendar realm new-target))

;;; ===========================================================================
;;; ToTemporalYearMonth — from a PlainYearMonth, a property bag, or a string.
;;; ===========================================================================
(defun read-year-month-fields (bag)
  "PrepareCalendarFields for year-month: read month, monthCode, year (alphabetical;
   day is NOT read). Returns a plist. Coercion happens during the read."
  (let ((month nil) (mc-num nil) (mc-leap nil) (mc-present nil) (year nil))
    (let ((v (js-get bag "month")))
      (unless (js-undefined-p v) (setf month (to-positive-integer-with-truncation v "month"))))
    (let ((v (js-get bag "monthCode")))
      (unless (js-undefined-p v)
        (setf mc-present t)
        (let ((s (temporal-require-string v "monthCode")))
          (multiple-value-bind (ok num leap) (monthcode-well-formed-p s)
            (unless ok
              (js-throw (make-native-error "RangeError"
                          (format nil "monthCode '~a' is not well-formed" s))))
            (setf mc-num num mc-leap leap)))))
    (let ((v (js-get bag "year")))
      (unless (js-undefined-p v) (setf year (to-integer-with-truncation v))))
    (list :month month :month-code-num mc-num :month-code-leap mc-leap
          :month-code-present mc-present :year year)))

(defun resolve-year-month-fields (fields overflow calendar realm)
  "CalendarYearMonthFromFields (iso8601). Enforces required fields (year; one of
   month/monthCode), month<->monthCode agreement, leap rejection, regulates the
   day to 1 and range-checks. Returns a PlainYearMonth."
  (let ((year (getf fields :year))
        (month (getf fields :month))
        (mc-num (getf fields :month-code-num))
        (mc-leap (getf fields :month-code-leap))
        (mc-present (getf fields :month-code-present)))
    (when (null year)
      (js-throw (make-native-error "TypeError" "year is required")))
    (when (and (null month) (not mc-present))
      (js-throw (make-native-error "TypeError" "one of month or monthCode is required")))
    (let ((resolved-month
            (cond
              (mc-present
               (when mc-leap
                 (js-throw (make-native-error "RangeError"
                             "leap month is not valid in the ISO 8601 calendar")))
               (unless (<= 1 mc-num 12)
                 (js-throw (make-native-error "RangeError"
                             "monthCode is not valid for ISO 8601 calendar")))
               (when (and month (/= month mc-num))
                 (js-throw (make-native-error "RangeError" "month and monthCode conflict")))
               mc-num)
              (t month))))
      ;; RegulateISODate constrains month/day; day is 1 (reference day).
      (let ((date (regulate-iso-date year resolved-month 1 overflow)))
        (unless (iso-year-month-within-limits (iso-date-year date) (iso-date-month date))
          (js-throw (make-native-error "RangeError" "PlainYearMonth is outside the representable range")))
        (make-plain-year-month date calendar realm)))))

(defun parse-year-month-string (s)
  "Parse a Temporal PlainYearMonth string. Accepts the reduced year-month forms
   (YYYY-MM, YYYYMM, with optional annotations) and any full DateTime string
   (whose day is discarded — reference day forced to 1). Returns (values iso-year
   iso-month ref-day calendar-id). RangeError on malformed."
  (let* ((s (string-trim '(#\Space #\Tab #\Newline #\Return) s))
         (br (or (position #\[ s) (length s)))
         (core (subseq s 0 br))
         (rest (subseq s br))
         (calendar "iso8601"))
    ;; Annotations (calendar id / tz) via the kernel parser.
    (when (plusp (length rest))
      (let ((p (make-pstate :str rest :pos 0 :len (length rest))))
        (let ((cal (parse-annotations p)))
          (unless (p-eof p) (p-fail))
          (when cal (setf calendar (canonicalize-calendar-id-strict cal))))))
    ;; Try the reduced year-month forms first (YYYY-MM / YYYYMM, extended year
    ;; +/-YYYYYY[-]MM).  A full-date/datetime string is handled via the kernel.
    (labels ((all-digits (a b) (and (<= b (length core))
                                    (loop for i from a below b always (digit-char-p (char core i)))))
             (try-reduced ()
               (let ((i 0) (sign 1) (ylen 4))
                 (when (and (plusp (length core)) (member (char core 0) '(#\+ #\-)))
                   (setf sign (if (char= (char core 0) #\-) -1 1) i 1 ylen 6))
                 (let ((yend (+ i ylen)))
                   (when (and (<= yend (length core)) (all-digits i yend))
                     (let* ((year (* sign (parse-integer core :start i :end yend)))
                            (j yend))
                       (when (and (< j (length core)) (char= (char core j) #\-)) (incf j))
                       (when (and (= (+ j 2) (length core)) (all-digits j (+ j 2)))
                         (let ((month (parse-integer core :start j :end (+ j 2))))
                           (when (and (= sign -1) (zerop (parse-integer core :start i :end yend)))
                             (p-fail))
                           (return-from try-reduced (values year month))))))))
               nil))
      (multiple-value-bind (year month) (try-reduced)
        (if year
            (progn
              (unless (<= 1 month 12) (p-fail))
              (values year month 1 calendar))
            ;; Full date/datetime string: parse via kernel, discard the day.
            (let ((r (parse-iso-datetime s :datetime)))
              (when (getf r :z)
                (js-throw (make-native-error "RangeError"
                            "a UTC-designator string cannot be a PlainYearMonth")))
              (let ((y (getf r :year)) (m (getf r :month)) (d (getf r :day)))
                (unless (and (<= 1 m 12) (<= 1 d (days-in-month y m))) (p-fail))
                (let ((cal (getf r :calendar)))
                  (when cal (setf calendar (canonicalize-calendar-id-strict cal))))
                (values y m 1 calendar))))))))

(defun to-temporal-year-month (realm v &optional (options *undefined*))
  "ToTemporalYearMonth. Returns a PlainYearMonth instance."
  (cond
    ((plain-year-month-p v)
     (get-temporal-overflow (get-options-object options))
     (make-plain-year-month (pym-iso-date v) (pym-calendar-id v) realm))
    ((js-object-p v)
     (let* ((cal-v (js-get v "calendar"))
            (calendar (if (js-undefined-p cal-v) "iso8601" (canonicalize-calendar-id cal-v)))
            (fields (read-year-month-fields v))
            (overflow (get-temporal-overflow (get-options-object options))))
       (resolve-year-month-fields fields overflow calendar realm)))
    ((stringp v)
     (multiple-value-bind (year month ref-day calendar) (parse-year-month-string v)
       (get-temporal-overflow (get-options-object options))
       (create-iso-year-month-checked year month ref-day calendar realm)))
    (t (js-throw (make-native-error "TypeError" "cannot convert value to a Temporal.PlainYearMonth")))))

;;; ===========================================================================
;;; add / subtract
;;; ===========================================================================
(defun add-duration-to-year-month (realm this args negate)
  "AddDurationToOrSubtractDurationFromPlainYearMonth."
  (let* ((this-date (pym-iso-date this))
         (calendar (pym-calendar-id this))
         (d (to-temporal-duration-record (arg 0 args))))
    (when negate
      (setf d (loop for f in +duration-fields+ append (list f (- (getf d f))))))
    ;; All options are read and cast BEFORE any algorithmic validation.
    (let* ((options (get-options-object (arg 1 args)))
           (overflow (get-temporal-overflow options)))
      (declare (ignorable overflow))
      ;; days/weeks/hours..nanoseconds must all be zero for a year-month add.
      (dolist (f '(:weeks :days :hours :minutes :seconds :milliseconds :microseconds :nanoseconds))
        (unless (zerop (getf d f))
          (js-throw (make-native-error "RangeError"
                      "PlainYearMonth add/subtract only accepts years and months"))))
      (let* ((sign (duration-sign d))
             (year (iso-date-year this-date))
             (month (iso-date-month this-date))
             ;; Step 8-9: the day-1 anchor date must itself be within the ISO date
             ;; range (CalendarDateFromFields with constrain range-checks it).
             (day1 (make-iso-date year month 1)))
        (unless (iso-date-within-limits day1)
          (js-throw (make-native-error "RangeError" "PlainYearMonth is outside the representable range")))
        (let* (;; Intermediate reference date: day 1 for a non-negative duration;
               ;; for a negative duration, the LAST day of the receiver's month,
               ;; computed as (first day of the next month) minus one day.
               (start
                 (if (< sign 0)
                     (let ((next (add-iso-date day1 0 1 0 0 :constrain)))
                       (epoch-days->iso-date (1- (iso-date->epoch-days next))))
                     day1))
               ;; The day is discarded from the result, so it is regulated with
               ;; constrain regardless of OVERFLOW; OVERFLOW only affects the
               ;; year-month range validity (a no-op for ISO).
               (result (add-iso-date start (getf d :years) (getf d :months) 0 0 :constrain)))
          (unless (iso-year-month-within-limits (iso-date-year result) (iso-date-month result))
            (js-throw (make-native-error "RangeError" "PlainYearMonth is outside the representable range")))
          (unless (iso-date-within-limits (make-iso-date (iso-date-year result) (iso-date-month result) 1))
            (js-throw (make-native-error "RangeError" "PlainYearMonth is outside the representable range")))
          (make-plain-year-month (make-iso-date (iso-date-year result) (iso-date-month result) 1)
                                 calendar realm))))))

;;; ===========================================================================
;;; until / since
;;; ===========================================================================
(defun yearmonth-difference-settings (op options)
  "GetDifferenceSettings for PlainYearMonth: allowed units are year/month only,
   smallestUnit default :month, largestUnit default (auto ->) :year. Year/month
   rounding increments are UNBOUNDED; the kernel's get-difference-settings now
   parameterizes that via a NIL max-increment for calendar units."
  (get-difference-settings op options :month :year
                           '(:year :month) '(:year :month)
                           (lambda (unit) (declare (ignore unit)) nil)))

(defun yearmonth-difference (realm this args op)
  (let* ((this-date (pym-iso-date this))
         (other (to-temporal-year-month realm (arg 0 args)))
         (other-date (pym-iso-date other))
         (options (get-options-object (arg 1 args))))
    (multiple-value-bind (smallest largest increment mode)
        (yearmonth-difference-settings op options)
      ;; Same year-month -> zero.
      (if (and (= (iso-date-year this-date) (iso-date-year other-date))
               (= (iso-date-month this-date) (iso-date-month other-date)))
          (make-temporal-duration realm (empty-duration))
          (let* ((d1 (make-iso-date (iso-date-year this-date) (iso-date-month this-date) 1))
                 (d2 (make-iso-date (iso-date-year other-date) (iso-date-month other-date) 1)))
            ;; The difference is measured between the day-1 dates, which must both
            ;; be within the representable ISO date range.
            (unless (and (iso-date-within-limits d1) (iso-date-within-limits d2))
              (js-throw (make-native-error "RangeError" "PlainYearMonth is outside the representable range")))
            (let ((out (round-year-month-difference d1 d2 smallest largest increment mode)))
              (when (eq op :since)
                (setf out (loop for f in +duration-fields+ append (list f (- (getf out f))))))
              (make-temporal-duration realm out)))))))

(defun round-year-month-difference (d1 d2 smallest largest increment mode)
  "Compute the calendar difference from D1 to D2 (both day-1 anchored) at LARGEST
   granularity, round to SMALLEST with INCREMENT/MODE (day-based fractional
   progress for year rounding), then re-balance to LARGEST. Returns a duration
   plist. D1 is the earlier-or-later anchor; the sign is preserved."
  (let* ((dur (difference-iso-date d1 d2 largest))
         (years (getf dur :years))
         (months (getf dur :months))
         (sign (cond ((or (plusp years) (plusp months)) 1)
                     ((or (minusp years) (minusp months)) -1)
                     (t 0))))
    ;; RoundRelativeDuration range-checks the rounding boundary: the ceiling
    ;; multiple of the increment (in the smallest unit), added to the anchor,
    ;; must remain within the representable ISO date range.
    (let* ((total-months (+ (* years 12) months))
           (unit-months (ecase smallest (:month 1) (:year 12)))
           (total-units (/ total-months unit-months))
           ;; ceiling toward the sign direction:
           (mag (ceiling (abs total-units) increment))
           (boundary-months (* sign mag increment unit-months))
           (boundary (add-iso-date (make-iso-date (iso-date-year d1) (iso-date-month d1) 1)
                                   0 boundary-months 0 0 :constrain)))
      (unless (iso-date-within-limits boundary)
        (js-throw (make-native-error "RangeError"
                    "PlainYearMonth difference rounds outside the representable range"))))
    (ecase smallest
      (:month
       ;; The difference is a whole number of months (day-1 to day-1), so there
       ;; is no sub-month fraction. When LARGEST is :month the total months are
       ;; rounded; when LARGEST is :year the YEARS are held fixed and only the
       ;; months field is rounded, then re-balanced (rounding can carry into
       ;; years — the cross-unit-boundary case).
       (ecase largest
         (:month (year-month-out 0 (round-to-increment (+ (* years 12) months) increment mode)))
         (:year (let* ((rounded (round-to-increment months increment mode))
                       (total (+ (* years 12) rounded))
                       (yy (truncate total 12)))
                  (year-month-out yy (- total (* yy 12)))))))
      (:year
       ;; Round the years, using the day-based fractional progress of the
       ;; remaining months toward a full year past the whole-year anchor.
       (let* ((anchor (add-iso-date (make-iso-date (iso-date-year d1) (iso-date-month d1) 1)
                                    years 0 0 0 :constrain))
              (next   (add-iso-date anchor sign 0 0 0 :constrain))
              ;; Fractional progress from the whole-year anchor toward the target,
              ;; measured in days over the length of the year in the sign
              ;; direction. NUM and DEN share the sign, so the ratio is in [0,1);
              ;; multiply by SIGN to give the signed fraction.
              (num (- (iso-date->epoch-days d2) (iso-date->epoch-days anchor)))
              (den (abs (- (iso-date->epoch-days next) (iso-date->epoch-days anchor))))
              (fraction (if (zerop den) 0 (/ (abs num) den)))
              (rounded-years (round-to-increment (+ years (* sign fraction)) increment mode)))
         (ecase largest
           ((:year :month) (year-month-out rounded-years 0))))))))

(defun year-month-out (years months)
  (list :years years :months months :weeks 0 :days 0
        :hours 0 :minutes 0 :seconds 0 :milliseconds 0
        :microseconds 0 :nanoseconds 0))

;;; ===========================================================================
;;; with
;;; ===========================================================================
(defun year-month-with (realm this args)
  (let ((this-date (pym-iso-date this))
        (calendar (pym-calendar-id this))
        (bag (arg 0 args)))
    (require-partial-temporal-object bag)
    (let* ((fields (read-year-month-fields bag))
           (any (or (getf fields :month) (getf fields :month-code-present) (getf fields :year)))
           (overflow (get-temporal-overflow (get-options-object (arg 1 args)))))
      (unless any
        (js-throw (make-native-error "TypeError" "with() requires at least one recognized field")))
      ;; Merge with the receiver's existing fields.
      (let* ((year (or (getf fields :year) (iso-date-year this-date)))
             (mc-present (getf fields :month-code-present))
             (mc-num (getf fields :month-code-num))
             (mc-leap (getf fields :month-code-leap))
             (month (cond
                      (mc-present
                       (when mc-leap
                         (js-throw (make-native-error "RangeError" "leap month invalid in ISO")))
                       (unless (<= 1 mc-num 12)
                         (js-throw (make-native-error "RangeError" "monthCode out of range")))
                       (when (and (getf fields :month) (/= (getf fields :month) mc-num))
                         (js-throw (make-native-error "RangeError" "month and monthCode conflict")))
                       mc-num)
                      ((getf fields :month) (getf fields :month))
                      (t (iso-date-month this-date)))))
        (let ((date (regulate-iso-date year month 1 overflow)))
          (unless (iso-year-month-within-limits (iso-date-year date) (iso-date-month date))
            (js-throw (make-native-error "RangeError" "PlainYearMonth is outside the representable range")))
          (make-plain-year-month date calendar realm))))))

;;; ===========================================================================
;;; toPlainDate
;;; ===========================================================================
(defun year-month-to-plain-date (realm this args)
  (let ((this-date (pym-iso-date this))
        (calendar (pym-calendar-id this))
        (item (arg 0 args)))
    (unless (js-object-p item)
      (js-throw (make-native-error "TypeError" "toPlainDate() argument must be an object")))
    ;; Requires PlainDate to be registered in this realm.
    (require-temporal-ctor realm "PlainDate")
    (let ((day-v (js-get item "day")))
      (when (js-undefined-p day-v)
        (js-throw (make-native-error "TypeError" "toPlainDate() requires a day field")))
      (let* ((day (to-positive-integer-with-truncation day-v "day"))
             ;; Always constrain (overflow option not read).
             (date (create-iso-date-checked (iso-date-year this-date) (iso-date-month this-date)
                                            day :constrain)))
        (make-plain-date date calendar realm)))))

;;; ===========================================================================
;;; toString
;;; ===========================================================================
(defun year-month-to-string (this options)
  (let* ((date (pym-iso-date this))
         (calendar (pym-calendar-id this))
         (opts (get-options-object options))
         (show (get-calendar-name-option opts))
         (year (iso-date-year date)) (month (iso-date-month date)) (day (iso-date-day date))
         (annotation (format-calendar-annotation calendar show)))
    (concatenate 'string
                 (format nil "~a-~2,'0d" (format-iso-year year) month)
                 ;; The reference day is only emitted when a calendar annotation
                 ;; is present.
                 (if (plusp (length annotation))
                     (format nil "-~2,'0d" day)
                     "")
                 annotation)))

;;; ===========================================================================
;;; install
;;; ===========================================================================
(defun install-temporal-plainyearmonth (realm)
  (let* ((op (realm-object-proto realm))
         (proto (make-object :proto op :class "Object"))
         (ctor (native-function realm "PlainYearMonth"
                 (lambda (this args) (declare (ignore this args))
                   (js-throw (make-native-error "TypeError" "Constructor PlainYearMonth requires 'new'")))
                 2)))
    (setf *temporal-plainyearmonth-proto* proto)
    ;; ---- constructor: (isoYear, isoMonth, calendar?, referenceISODay?) ----
    (setf (js-object-construct ctor)
          (lambda (args nt)
            (let* ((year (to-integer-with-truncation (arg 0 args)))
                   (month (to-integer-with-truncation (arg 1 args)))
                   (cal-v (arg 2 args))
                   (calendar (if (js-undefined-p cal-v) "iso8601" (canonicalize-calendar-id-strict cal-v)))
                   (ref-v (arg 3 args))
                   (ref-day (if (js-undefined-p ref-v) 1 (to-integer-with-truncation ref-v))))
              ;; IsValidISODate on (year, month, ref-day) then year-month range.
              (unless (and (<= 1 month 12) (<= 1 ref-day (days-in-month year month)))
                (js-throw (make-native-error "RangeError" "invalid ISO year-month")))
              (unless (iso-year-month-within-limits year month)
                (js-throw (make-native-error "RangeError" "PlainYearMonth is outside the representable range")))
              (make-plain-year-month (make-iso-date year month ref-day) calendar realm
                                     (proto-from-newtarget nt proto)))))
    (def-value ctor "prototype" proto :writable nil :configurable nil)
    (def-value proto "constructor" ctor)

    ;; ---- statics ----
    (def-method realm ctor "from" 1 (this args)
      (declare (ignore this))
      (to-temporal-year-month realm (arg 0 args) (arg 1 args)))
    (def-method realm ctor "compare" 2 (this args)
      (declare (ignore this))
      (let ((a (pym-iso-date (to-temporal-year-month realm (arg 0 args))))
            (b (pym-iso-date (to-temporal-year-month realm (arg 1 args)))))
        (float (let ((ea (iso-date->epoch-days a)) (eb (iso-date->epoch-days b)))
                 (cond ((< ea eb) -1) ((> ea eb) 1) (t 0)))
               1d0)))

    ;; ---- getters ----
    (def-getter realm proto "calendarId"
      (lambda (this args) (declare (ignore args)) (pym-calendar-id this)))
    (macrolet ((numgetter (name form)
                 `(def-getter realm proto ,name
                    (lambda (this args) (declare (ignore args))
                      (let ((date (pym-iso-date this))) (declare (ignorable date))
                        (float ,form 1d0))))))
      (numgetter "year" (iso-date-year date))
      (numgetter "month" (iso-date-month date))
      (numgetter "daysInMonth" (days-in-month (iso-date-year date) (iso-date-month date)))
      (numgetter "daysInYear" (iso-days-in-year (iso-date-year date)))
      (numgetter "monthsInYear" 12))
    (def-getter realm proto "monthCode"
      (lambda (this args) (declare (ignore args))
        (format nil "M~2,'0d" (iso-date-month (pym-iso-date this)))))
    (def-getter realm proto "inLeapYear"
      (lambda (this args) (declare (ignore args))
        (js-bool (leap-year-p (iso-date-year (pym-iso-date this))))))
    ;; era / eraYear are undefined for the ISO calendar.
    (def-getter realm proto "era"
      (lambda (this args) (declare (ignore args)) (pym-iso-date this) *undefined*))
    (def-getter realm proto "eraYear"
      (lambda (this args) (declare (ignore args)) (pym-iso-date this) *undefined*))

    ;; ---- add / subtract ----
    (def-method realm proto "add" 1 (this args)
      (add-duration-to-year-month realm this args nil))
    (def-method realm proto "subtract" 1 (this args)
      (add-duration-to-year-month realm this args t))

    ;; ---- until / since ----
    (def-method realm proto "until" 1 (this args)
      (yearmonth-difference realm this args :until))
    (def-method realm proto "since" 1 (this args)
      (yearmonth-difference realm this args :since))

    ;; ---- with ----
    (def-method realm proto "with" 1 (this args)
      (year-month-with realm this args))

    ;; ---- equals ----
    (def-method realm proto "equals" 1 (this args)
      (let* ((a (pym-iso-date this))
             (a-cal (pym-calendar-id this))
             (other (to-temporal-year-month realm (arg 0 args)))
             (b (pym-iso-date other))
             (b-cal (pym-calendar-id other)))
        (js-bool (and (= (iso-date-year a) (iso-date-year b))
                      (= (iso-date-month a) (iso-date-month b))
                      (= (iso-date-day a) (iso-date-day b))
                      (string= a-cal b-cal)))))

    ;; ---- toPlainDate ----
    (def-method realm proto "toPlainDate" 1 (this args)
      (year-month-to-plain-date realm this args))

    ;; ---- toString / toJSON / toLocaleString ----
    (def-method realm proto "toString" 0 (this args)
      (year-month-to-string this (arg 0 args)))
    (def-method realm proto "toJSON" 0 (this args)
      (declare (ignore args))
      (year-month-to-string this *undefined*))
    (def-method realm proto "toLocaleString" 0 (this args)
      (declare (ignore args))
      (year-month-to-string this *undefined*))

    ;; ---- valueOf: not a primitive ----
    (def-method realm proto "valueOf" 0 (this args)
      (declare (ignore args))
      (js-throw (make-native-error "TypeError"
                  "Cannot convert a Temporal.PlainYearMonth to a primitive; use compare() or equals()")))

    ;; ---- @@toStringTag ----
    (put proto (symbol-tostringtag realm) "Temporal.PlainYearMonth"
         :enumerable nil :writable nil :configurable t)

    (temporal-register realm "PlainYearMonth" ctor)))

(register-builtin-installer 'install-temporal-plainyearmonth)
