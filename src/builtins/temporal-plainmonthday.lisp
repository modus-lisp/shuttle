;;;; builtins/temporal-plainmonthday.lisp — Temporal.PlainMonthDay.
;;;;
;;;; A month+day (no year) with a reference ISO year (default 1972, a leap year,
;;;; or the parsed year), stored as an iso-date record in the
;;;; :temporal-plainmonthday slot plus a :temporal-calendar id. Built on the
;;;; temporal-core kernel and the concurrent PlainDate helpers (regulate-iso-date,
;;;; create-iso-date-checked, make-plain-date, canonicalize-calendar-id,
;;;; get-calendar-name-option, format-calendar-annotation, monthcode-well-formed-p,
;;;; require-temporal-ctor).
(in-package #:shuttle)

(defvar *temporal-plainmonthday-proto* nil)

(defconstant +monthday-ref-year+ 1972 "The canonical leap-year reference year.")

(defun make-plain-month-day (iso-date calendar-id realm &optional new-target)
  "CreateTemporalMonthDay: ISO-DATE is a valid iso-date whose YEAR is the
   reference ISO year; CALENDAR-ID a canonical calendar id string."
  (declare (ignore realm))
  (let* ((proto (proto-from-newtarget new-target *temporal-plainmonthday-proto*))
         (o (make-object :proto proto :class "Object")))
    (setf (getf (js-object-internal o) :temporal-plainmonthday) iso-date)
    (setf (getf (js-object-internal o) :temporal-calendar) calendar-id)
    o))

(defun pmd-iso-date (this)
  "RequireInternalSlot([[InitializedTemporalMonthDay]]) -> iso-date record."
  (temporal-slot this :temporal-plainmonthday "Temporal.PlainMonthDay"))

(defun pmd-calendar-id (this)
  (temporal-slot this :temporal-plainmonthday "Temporal.PlainMonthDay")
  (getf (js-object-internal this) :temporal-calendar "iso8601"))

(defun plain-month-day-p (v)
  (and (js-object-p v)
       (not (eq (getf (js-object-internal v) :temporal-plainmonthday 'none) 'none))))

;;; ===========================================================================
;;; ToTemporalMonthDay — from a PlainMonthDay, a property bag, or a string.
;;; ===========================================================================
(defun read-month-day-fields (bag)
  "PrepareCalendarFields for month-day: read day, month, monthCode, year
   (alphabetical). Coercion happens during the read (observable). NOTE: month-code
   well-formedness is validated during the read, but its suitability (M01..M12
   range, leap) is validated later so that a well-formed but out-of-range code
   defers to a later year TypeError — matching the ordering tests."
  (let ((day nil) (month nil) (mc-num nil) (mc-leap nil) (mc-present nil) (year nil))
    (let ((v (js-get bag "day")))
      (unless (js-undefined-p v) (setf day (to-positive-integer-with-truncation v "day"))))
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
    (list :day day :month month :month-code-num mc-num :month-code-leap mc-leap
          :month-code-present mc-present :year year)))

(defun resolve-month-day-fields (fields overflow calendar realm)
  "CalendarMonthDayFromFields (iso8601). day required; one of month/monthCode
   required; month<->monthCode agreement; leap rejection. When a `year` is
   supplied it is used ONLY to apply overflow to Feb 29 (the year itself is NOT
   range-checked) — otherwise the canonical leap year 1972 is used so any valid
   (month, day) including Feb 29 is representable. Returns a PlainMonthDay."
  (let ((day (getf fields :day))
        (month (getf fields :month))
        (mc-num (getf fields :month-code-num))
        (mc-leap (getf fields :month-code-leap))
        (mc-present (getf fields :month-code-present))
        (year (getf fields :year)))
    (when (null day)
      (js-throw (make-native-error "TypeError" "day is required")))
    (when (and (null month) (not mc-present))
      (js-throw (make-native-error "TypeError" "one of month or monthCode is required")))
    (let ((resolved-month
            (cond
              (mc-present
               (when mc-leap
                 (js-throw (make-native-error "RangeError" "leap month invalid in ISO")))
               (unless (<= 1 mc-num 12)
                 (js-throw (make-native-error "RangeError" "monthCode out of range")))
               (when (and month (/= month mc-num))
                 (js-throw (make-native-error "RangeError" "month and monthCode conflict")))
               mc-num)
              (t month))))
      ;; Overflow year: the caller's year (used only for leap-day overflow) or the
      ;; canonical leap reference year.
      (let* ((ref-year (or year +monthday-ref-year+))
             (date (regulate-iso-date ref-year resolved-month day overflow)))
        ;; After resolving in the caller's (or reference) year, normalize the
        ;; reference year: 1972 unless the day is Feb-29-only (which 1972 keeps).
        (make-plain-month-day
         (make-iso-date +monthday-ref-year+ (iso-date-month date) (iso-date-day date))
         calendar realm)))))

(defun parse-month-day-string (s)
  "Parse a Temporal PlainMonthDay string. Accepts the reduced forms MM-DD, MMDD,
   --MM-DD, --MMDD (with optional annotations) and any full DateTime string
   (whose year is discarded). Returns (values month day calendar-id). RangeError
   on malformed. A bare month-day carrying a UTC offset (Z / +HH:MM) with NO time
   is invalid."
  (let* ((s (string-trim '(#\Space #\Tab #\Newline #\Return) s))
         (br (or (position #\[ s) (length s)))
         (core (subseq s 0 br))
         (rest (subseq s br))
         (calendar "iso8601"))
    (when (plusp (length rest))
      (let ((p (make-pstate :str rest :pos 0 :len (length rest))))
        (let ((cal (parse-annotations p)))
          (unless (p-eof p) (p-fail))
          (when cal (setf calendar (canonicalize-calendar-id-strict cal))))))
    (labels ((all-digits (a b) (and (<= b (length core))
                                    (loop for i from a below b always (digit-char-p (char core i)))))
             (try-reduced ()
               (let ((start 0))
                 (when (and (>= (length core) 2) (char= (char core 0) #\-) (char= (char core 1) #\-))
                   (setf start 2))
                 (let ((body (subseq core start)))
                   (cond
                     ;; MM-DD
                     ((and (= (length body) 5) (char= (char body 2) #\-)
                           (loop for i in '(0 1 3 4) always (digit-char-p (char body i))))
                      (values (parse-integer body :start 0 :end 2)
                              (parse-integer body :start 3 :end 5)))
                     ;; MMDD
                     ((and (= (length body) 4)
                           (every #'digit-char-p body))
                      (values (parse-integer body :start 0 :end 2)
                              (parse-integer body :start 2 :end 4)))
                     (t nil))))))
      (multiple-value-bind (month day) (try-reduced)
        (if month
            (progn
              (unless (and (<= 1 month 12) (<= 1 day (days-in-month +monthday-ref-year+ month))) (p-fail))
              (values month day calendar))
            ;; Full date/datetime string: parse via kernel, discard the year.
            (let ((r (parse-iso-datetime s :datetime)))
              (when (getf r :z)
                (js-throw (make-native-error "RangeError"
                            "a UTC-designator string cannot be a PlainMonthDay")))
              (let ((m (getf r :month)) (d (getf r :day)) (y (getf r :year)))
                (unless (and (<= 1 m 12) (<= 1 d (days-in-month y m))) (p-fail))
                (let ((cal (getf r :calendar)))
                  (when cal (setf calendar (canonicalize-calendar-id-strict cal))))
                (values m d calendar))))))))

(defun to-temporal-month-day (realm v &optional (options *undefined*))
  "ToTemporalMonthDay. Returns a PlainMonthDay instance."
  (cond
    ((plain-month-day-p v)
     (get-temporal-overflow (get-options-object options))
     (make-plain-month-day (pmd-iso-date v) (pmd-calendar-id v) realm))
    ((js-object-p v)
     (let* ((cal-v (js-get v "calendar"))
            (calendar (if (js-undefined-p cal-v) "iso8601" (canonicalize-calendar-id cal-v)))
            (fields (read-month-day-fields v))
            (overflow (get-temporal-overflow (get-options-object options))))
       (resolve-month-day-fields fields overflow calendar realm)))
    ((stringp v)
     (multiple-value-bind (month day calendar) (parse-month-day-string v)
       (get-temporal-overflow (get-options-object options))
       (make-plain-month-day (make-iso-date +monthday-ref-year+ month day) calendar realm)))
    (t (js-throw (make-native-error "TypeError" "cannot convert value to a Temporal.PlainMonthDay")))))

;;; ===========================================================================
;;; with
;;; ===========================================================================
(defun month-day-with (realm this args)
  (let ((this-date (pmd-iso-date this))
        (calendar (pmd-calendar-id this))
        (bag (arg 0 args)))
    (require-partial-temporal-object bag)
    (let* ((fields (read-month-day-fields bag))
           (any (or (getf fields :day) (getf fields :month)
                    (getf fields :month-code-present) (getf fields :year)))
           (overflow (get-temporal-overflow (get-options-object (arg 1 args)))))
      (unless any
        (js-throw (make-native-error "TypeError" "with() requires at least one recognized field")))
      (let* ((day (or (getf fields :day) (iso-date-day this-date)))
             (mc-present (getf fields :month-code-present))
             (mc-num (getf fields :month-code-num))
             (mc-leap (getf fields :month-code-leap))
             (this-month (iso-date-month this-date))
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
                      (t this-month)))
             ;; year only used for overflow; default to reference year.
             (ref-year (or (getf fields :year) +monthday-ref-year+))
             (date (regulate-iso-date ref-year month day overflow)))
        (make-plain-month-day
         (make-iso-date +monthday-ref-year+ (iso-date-month date) (iso-date-day date))
         calendar realm)))))

;;; ===========================================================================
;;; toPlainDate
;;; ===========================================================================
(defun month-day-to-plain-date (realm this args)
  (let ((this-date (pmd-iso-date this))
        (calendar (pmd-calendar-id this))
        (item (arg 0 args)))
    (unless (js-object-p item)
      (js-throw (make-native-error "TypeError" "toPlainDate() argument must be an object")))
    (require-temporal-ctor realm "PlainDate")
    (let ((year-v (js-get item "year")))
      (when (js-undefined-p year-v)
        (js-throw (make-native-error "TypeError" "toPlainDate() requires a year field")))
      (let* ((year (to-integer-with-truncation year-v))
             ;; Always constrain (overflow option not read).
             (date (create-iso-date-checked year (iso-date-month this-date) (iso-date-day this-date)
                                            :constrain)))
        (make-plain-date date calendar realm)))))

;;; ===========================================================================
;;; toString
;;; ===========================================================================
(defun month-day-to-string (this options)
  (let* ((date (pmd-iso-date this))
         (calendar (pmd-calendar-id this))
         (opts (get-options-object options))
         (show (get-calendar-name-option opts))
         (year (iso-date-year date)) (month (iso-date-month date)) (day (iso-date-day date))
         (annotation (format-calendar-annotation calendar show)))
    ;; The reference year prefix is only emitted when a calendar annotation is
    ;; present (always / critical).
    (concatenate 'string
                 (if (plusp (length annotation))
                     (format nil "~a-" (format-iso-year year))
                     "")
                 (format nil "~2,'0d-~2,'0d" month day)
                 annotation)))

;;; ===========================================================================
;;; install
;;; ===========================================================================
(defun install-temporal-plainmonthday (realm)
  (let* ((op (realm-object-proto realm))
         (proto (make-object :proto op :class "Object"))
         (ctor (native-function realm "PlainMonthDay"
                 (lambda (this args) (declare (ignore this args))
                   (js-throw (make-native-error "TypeError" "Constructor PlainMonthDay requires 'new'")))
                 2)))
    (setf *temporal-plainmonthday-proto* proto)
    ;; ---- constructor: (isoMonth, isoDay, calendar?, referenceISOYear?) ----
    (setf (js-object-construct ctor)
          (lambda (args nt)
            (let* ((month (to-integer-with-truncation (arg 0 args)))
                   (day (to-integer-with-truncation (arg 1 args)))
                   (cal-v (arg 2 args))
                   (calendar (if (js-undefined-p cal-v) "iso8601" (canonicalize-calendar-id-strict cal-v)))
                   (ref-v (arg 3 args))
                   (ref-year (if (js-undefined-p ref-v) +monthday-ref-year+ (to-integer-with-truncation ref-v))))
              ;; IsValidISODate on (ref-year, month, day) — strict, no constrain.
              (unless (and (<= 1 month 12) (<= 1 day (days-in-month ref-year month)))
                (js-throw (make-native-error "RangeError" "invalid ISO month-day")))
              (unless (iso-date-within-limits (make-iso-date ref-year month day))
                (js-throw (make-native-error "RangeError" "PlainMonthDay is outside the representable range")))
              (make-plain-month-day (make-iso-date ref-year month day) calendar realm
                                    (proto-from-newtarget nt proto)))))
    (def-value ctor "prototype" proto :writable nil :configurable nil)
    (def-value proto "constructor" ctor)

    ;; ---- statics ----
    (def-method realm ctor "from" 1 (this args)
      (declare (ignore this))
      (to-temporal-month-day realm (arg 0 args) (arg 1 args)))

    ;; ---- getters (calendarId, monthCode, day only — NO month/year/era) ----
    (def-getter realm proto "calendarId"
      (lambda (this args) (declare (ignore args)) (pmd-calendar-id this)))
    (def-getter realm proto "monthCode"
      (lambda (this args) (declare (ignore args))
        (format nil "M~2,'0d" (iso-date-month (pmd-iso-date this)))))
    (def-getter realm proto "day"
      (lambda (this args) (declare (ignore args))
        (float (iso-date-day (pmd-iso-date this)) 1d0)))

    ;; ---- with ----
    (def-method realm proto "with" 1 (this args)
      (month-day-with realm this args))

    ;; ---- equals ----
    (def-method realm proto "equals" 1 (this args)
      (let* ((a (pmd-iso-date this))
             (a-cal (pmd-calendar-id this))
             (other (to-temporal-month-day realm (arg 0 args)))
             (b (pmd-iso-date other))
             (b-cal (pmd-calendar-id other)))
        (js-bool (and (= (iso-date-year a) (iso-date-year b))
                      (= (iso-date-month a) (iso-date-month b))
                      (= (iso-date-day a) (iso-date-day b))
                      (string= a-cal b-cal)))))

    ;; ---- toPlainDate ----
    (def-method realm proto "toPlainDate" 1 (this args)
      (month-day-to-plain-date realm this args))

    ;; ---- toString / toJSON / toLocaleString ----
    (def-method realm proto "toString" 0 (this args)
      (month-day-to-string this (arg 0 args)))
    (def-method realm proto "toJSON" 0 (this args)
      (declare (ignore args))
      (month-day-to-string this *undefined*))
    (def-method realm proto "toLocaleString" 0 (this args)
      (declare (ignore args))
      (month-day-to-string this *undefined*))

    ;; ---- valueOf: not a primitive ----
    (def-method realm proto "valueOf" 0 (this args)
      (declare (ignore args))
      (js-throw (make-native-error "TypeError"
                  "Cannot convert a Temporal.PlainMonthDay to a primitive; use equals()")))

    ;; ---- @@toStringTag ----
    (put proto (symbol-tostringtag realm) "Temporal.PlainMonthDay"
         :enumerable nil :writable nil :configurable t)

    (temporal-register realm "PlainMonthDay" ctor)))

(register-builtin-installer 'install-temporal-plainmonthday)
