;;;; builtins/temporal-plaindate.lisp — Temporal.PlainDate + shared ISO date arithmetic.
;;;;
;;;; A PlainDate is a calendar date (year/month/day) with no time or zone, stored
;;;; as an iso-date struct in the :temporal-plaindate internal slot plus a
;;;; calendar-id string in :temporal-calendar (always "iso8601" here). Built on
;;;; the temporal-core kernel (iso-date records, epoch-day arithmetic, the ISO
;;;; parser, options readers).
;;;;
;;;; ---------------------------------------------------------------------------
;;;; SIBLING API — the PlainYearMonth / PlainMonthDay / PlainDateTime installers
;;;; run in parallel and call the reusable date machinery here:
;;;;    (make-plain-date iso-date calendar-id realm &optional nt)  -> PlainDate obj
;;;;    (pd-iso-date obj)          -> the iso-date record of a PlainDate (branded)
;;;;    (pd-calendar-id obj)       -> its calendar id string
;;;;    (add-iso-date date years months weeks days overflow) -> iso-date  (AddISODate)
;;;;    (difference-iso-date d1 d2 largest-unit)  -> duration plist  (DifferenceISODate)
;;;;    (regulate-iso-date y m d overflow)        -> iso-date         (RegulateISODate)
;;;;    (iso-date-surpasses sign y1 m1 d1 y2 m2 d2) -> bool           (ISODateSurpasses)
;;;;    (iso-date-within-limits date)  -> bool  (ISODateTimeWithinLimits at midnight)
;;;;    (canonicalize-calendar-id v)   -> "iso8601" | RangeError (case-insensitive)
;;;; ---------------------------------------------------------------------------
(in-package #:shuttle)

(defvar *temporal-plaindate-proto* nil)

;;; ===========================================================================
;;; Instance creation + slot access
;;; ===========================================================================
(defun make-plain-date (iso-date calendar-id realm &optional new-target)
  "CreateTemporalDate: ISO-DATE is a valid in-range iso-date; CALENDAR-ID a
   canonical calendar id string. Returns a branded Temporal.PlainDate."
  (declare (ignore realm))
  (let* ((proto (proto-from-newtarget new-target *temporal-plaindate-proto*))
         (o (make-object :proto proto :class "Object")))
    (setf (getf (js-object-internal o) :temporal-plaindate) iso-date)
    (setf (getf (js-object-internal o) :temporal-calendar) calendar-id)
    o))

(defun pd-iso-date (this)
  "RequireInternalSlot([[InitializedTemporalDate]]) -> iso-date record."
  (temporal-slot this :temporal-plaindate "Temporal.PlainDate"))

(defun pd-calendar-id (this)
  "The calendar id string of a PlainDate (\"iso8601\")."
  (temporal-slot this :temporal-plaindate "Temporal.PlainDate")
  (getf (js-object-internal this) :temporal-calendar "iso8601"))

(defun plaindate-p (v)
  (and (js-object-p v)
       (not (eq (getf (js-object-internal v) :temporal-plaindate 'none) 'none))))

;;; ===========================================================================
;;; Calendar id
;;; ===========================================================================
(defun parse-calendar-annotation-from-string (s)
  "ParseTemporalCalendarString: parse S as any Temporal ISO string (datetime,
   time, or the reduced year-month / month-day forms) and return the calendar id
   from its [u-ca=...] annotation (default \"iso8601\"). RangeError if S is not a
   valid Temporal string at all. The annotation calendar is validated to be
   iso8601 (case-insensitive) here."
  (let ((s (string-trim '(#\Space #\Tab #\Newline #\Return) s)))
    (flet ((try (kind pre)
             (handler-case
                 (let ((full (if pre (concatenate 'string pre s) s)))
                   (list (or (getf (parse-iso-datetime full kind) :calendar) "iso8601")))
               (shuttle-error () nil))))
      (let ((res (or (try :datetime nil)
                     (try :time nil)
                     ;; reduced year-month (YYYY-MM / YYYYMM): complete to a day.
                     (and (>= (length s) 4) (try :datetime nil))
                     nil)))
        ;; Try reduced forms by completing them to a full date for the parser.
        (unless res
          (setf res (or (try-reduced-yearmonth s) (try-reduced-monthday s))))
        (unless res
          (js-throw (make-native-error "RangeError"
                      (format nil "~a is not a valid calendar string" s))))
        (let ((cal (first res)))
          (if (string-equal cal "iso8601") "iso8601"
              (js-throw (make-native-error "RangeError"
                          (format nil "unknown calendar: ~a" cal)))))))))

(defun try-reduced-yearmonth (s)
  "Attempt to read S as a reduced year-month string (YYYY-MM[annotations] /
   YYYYMM[...]) and return (list calendar-id) or NIL."
  (let* ((br (or (position #\[ s) (length s)))
         (core (subseq s 0 br)))
    (when (or (and (= (length core) 7) (char= (char core 4) #\-)
                   (every #'digit-char-p (subseq core 0 4))
                   (every #'digit-char-p (subseq core 5 7)))
              (and (= (length core) 6) (every #'digit-char-p core)))
      ;; complete to YYYY-MM-01 and parse for the annotation.
      (handler-case
          (let* ((full (concatenate 'string
                        (if (find #\- core) core
                            (concatenate 'string (subseq core 0 4) "-" (subseq core 4 6)))
                        "-01" (subseq s br))))
            (list (or (getf (parse-iso-datetime full :datetime) :calendar) "iso8601")))
        (shuttle-error () nil)))))

(defun try-reduced-monthday (s)
  "Attempt to read S as a reduced month-day string (MM-DD / --MM-DD /
   MMDD[annotations]) and return (list calendar-id) or NIL."
  (let* ((br (or (position #\[ s) (length s)))
         (core (subseq s 0 br))
         (rest (subseq s br)))
    (flet ((build (mm dd) (concatenate 'string "2000-" mm "-" dd rest)))
      (let ((full
              (cond
                ((and (= (length core) 5) (char= (char core 2) #\-)
                      (every #'digit-char-p (subseq core 0 2))
                      (every #'digit-char-p (subseq core 3 5)))
                 (build (subseq core 0 2) (subseq core 3 5)))
                ((and (= (length core) 7) (string= (subseq core 0 2) "--")
                      (char= (char core 4) #\-))
                 (build (subseq core 2 4) (subseq core 5 7)))
                ((and (= (length core) 4) (every #'digit-char-p core))
                 (build (subseq core 0 2) (subseq core 2 4)))
                (t nil))))
        (when full
          (handler-case
              (list (or (getf (parse-iso-datetime full :datetime) :calendar) "iso8601"))
            (shuttle-error () nil)))))))

(defun canonicalize-calendar-id (v)
  "ToTemporalCalendarIdentifier for the ISO calendar only. V must be a string (a
   bare id \"iso8601\", or any Temporal ISO string carrying a [u-ca=...]
   annotation) — else TypeError. A string that neither equals iso8601 nor parses
   is a RangeError. Returns \"iso8601\"."
  (cond
    ;; A Temporal object with its own calendar slot supplies it directly.
    ((and (js-object-p v) (getf (js-object-internal v) :temporal-calendar))
     (let ((c (getf (js-object-internal v) :temporal-calendar)))
       (if (string-equal c "iso8601") "iso8601"
           (js-throw (make-native-error "RangeError" "unknown calendar")))))
    ((not (stringp v))
     (js-throw (make-native-error "TypeError" "calendar must be a string")))
    ((string-equal v "iso8601") "iso8601")
    (t (parse-calendar-annotation-from-string v))))

;;; ===========================================================================
;;; ISO date range / regulation
;;; ===========================================================================
(defun iso-date-within-limits (date)
  "ISODateTimeWithinLimits for the date at noon (the reference the spec uses for
   PlainDate range checks). RejectDateTimeRange allows one extra day of margin at
   each end of the instant range."
  (let ((noon (+ (* (iso-date->epoch-days date) +ns-per-day+)
                 (* 12 +ns-per-hour+))))
    (<= (- +ns-min+ +ns-per-day+) noon (+ +ns-max+ +ns-per-day+))))

(defun valid-iso-date-fields-p (y m d)
  (and (<= 1 m 12) (<= 1 d (days-in-month y m))))

(defun regulate-iso-date (y m d overflow)
  "RegulateISODate: :constrain clamps month into 1..12 then day into the valid
   range for that month; :reject RangeErrors on any out-of-range field. Returns
   an iso-date. (Does NOT range-check against the calendar limits — callers do.)"
  (ecase overflow
    (:constrain
     (let* ((cm (max 1 (min 12 m)))
            (cd (max 1 (min (days-in-month y cm) d))))
       (make-iso-date y cm cd)))
    (:reject
     (unless (valid-iso-date-fields-p y m d)
       (js-throw (make-native-error "RangeError" "ISO date field out of range")))
     (make-iso-date y m d))))

(defun create-iso-date-checked (y m d overflow)
  "RegulateISODate then range-check against the calendar limits (RangeError)."
  (let ((date (regulate-iso-date y m d overflow)))
    (unless (iso-date-within-limits date)
      (js-throw (make-native-error "RangeError" "date out of range")))
    date))

;;; ===========================================================================
;;; Date arithmetic — AddISODate / DifferenceISODate / ISODateSurpasses
;;; ===========================================================================
(defun balance-iso-year-month (year month)
  "BalanceISOYearMonth: fold an out-of-range MONTH (0-based arithmetic) back into
   1..12 with a year carry. Returns (values year month)."
  (let* ((m0 (+ (* year 12) (1- month)))
         (y (floor m0 12))
         (m (1+ (mod m0 12))))
    (values y m)))

(defun add-iso-date (date years months weeks days overflow)
  "AddISODate: add YEARS/MONTHS (with regulation) then WEEKS+DAYS to DATE.
   Years+months are applied first and the intermediate y/m/d regulated per
   OVERFLOW; then (weeks*7 + days) are added via epoch-day arithmetic. Returns an
   iso-date (NOT range-checked; callers validate)."
  (let* ((y0 (+ (iso-date-year date) years))
         (raw-month (+ (iso-date-month date) months)))
    (multiple-value-bind (y m) (balance-iso-year-month y0 raw-month)
      (let* ((intermediate (regulate-iso-date y m (iso-date-day date) overflow))
             (total-days (+ (* weeks 7) days))
             (edays (+ (iso-date->epoch-days intermediate) total-days)))
        (epoch-days->iso-date edays)))))

(defun iso-date-surpasses (sign y1 m1 d1 y2 m2 d2)
  "ISODateSurpasses: T when (y1,m1,d1) is strictly beyond (y2,m2,d2) in the
   direction of SIGN (+1 => later surpasses, -1 => earlier surpasses)."
  (cond ((/= y1 y2) (= sign (if (> y1 y2) 1 -1)))
        ((/= m1 m2) (= sign (if (> m1 m2) 1 -1)))
        ((/= d1 d2) (= sign (if (> d1 d2) 1 -1)))
        (t nil)))

(defun date-duration (years months weeks days)
  "A full duration plist with only date fields set (time fields zeroed) so
   Temporal.Duration getters never see a missing key."
  (list :years years :months months :weeks weeks :days days
        :hours 0 :minutes 0 :seconds 0 :milliseconds 0
        :microseconds 0 :nanoseconds 0))

(defun difference-iso-date (d1 d2 largest-unit)
  "DifferenceISODate(d1, d2, largestUnit): the calendar difference from D1 to D2
   as a date-only duration plist. LARGEST-UNIT is :year, :month, :week or :day.
   Follows the spec's sign-dependent constrain-into-target algorithm exactly."
  (let ((y1 (iso-date-year d1)) (m1 (iso-date-month d1)) (dd1 (iso-date-day d1))
        (y2 (iso-date-year d2)) (m2 (iso-date-month d2)) (dd2 (iso-date-day d2)))
    (ecase largest-unit
      ((:year :month)
       (let ((sign (cond ((iso-date-surpasses 1 y2 m2 dd2 y1 m1 dd1) 1)
                         ((iso-date-surpasses -1 y2 m2 dd2 y1 m1 dd1) -1)
                         (t 0))))
         (if (zerop sign)
             (date-duration 0 0 0 0)
             (let* ((years 0) (months 0))
               ;; Walk years toward the target without overshooting.
               (let ((yy y1))
                 (loop
                   (let ((cand (+ yy sign)))
                     (if (iso-date-surpasses sign cand m1 dd1 y2 m2 dd2)
                         (return)
                         (setf yy cand)))
                   (incf years sign))
                 ;; Walk months.
                 (let ((cy yy) (cm m1))
                   (loop
                     (multiple-value-bind (ny nm) (balance-iso-year-month cy (+ cm sign))
                       (if (iso-date-surpasses sign ny nm dd1 y2 m2 dd2)
                           (return)
                           (setf cy ny cm nm)))
                     (incf months sign))
                   ;; Constrain the intermediate day into the target month, then
                   ;; count the remaining whole days.
                   (let* ((cd (min dd1 (days-in-month cy cm)))
                          (mid (make-iso-date cy cm cd))
                          (days (- (iso-date->epoch-days d2) (iso-date->epoch-days mid))))
                     (when (eq largest-unit :month)
                       (incf months (* years 12))
                       (setf years 0))
                     (date-duration years months 0 days))))))))
      ((:week :day)
       (let ((days (- (iso-date->epoch-days d2) (iso-date->epoch-days d1)))
             (weeks 0))
         (when (eq largest-unit :week)
           (setf weeks (truncate days 7))
           (setf days (- days (* weeks 7))))
         (date-duration 0 0 weeks days))))))

;;; ===========================================================================
;;; Property-bag field reads (ToTemporalDate from an object)
;;; ===========================================================================
(defun monthcode-well-formed-p (s)
  "A monthCode is well-formed iff it matches M[0-9][0-9] (optionally a trailing
   'L' leap marker). Returns (values well-formed month-number leap-p)."
  (let ((n (length s)))
    (when (and (>= n 3) (char= (char s 0) #\M)
               (digit-char-p (char s 1)) (digit-char-p (char s 2))
               (or (= n 3) (and (= n 4) (char= (char s 3) #\L))))
      (values t
              (+ (* 10 (digit-char-p (char s 1))) (digit-char-p (char s 2)))
              (= n 4)))))

(defun to-positive-integer-with-truncation (v what)
  "ToPositiveIntegerWithTruncation: ToIntegerWithTruncation then require > 0."
  (let ((i (to-integer-with-truncation v)))
    (when (<= i 0)
      (js-throw (make-native-error "RangeError"
                  (format nil "~a must be a positive integer" what))))
    i))

;;; PrepareCalendarFields read order = ALPHABETICAL: day, month, monthCode, year.
;;; (calendar is read first, before these, by the caller.)
(defun read-date-fields (bag)
  "Read day/month/monthCode/year off BAG in alphabetical order, each coerced
   (day/year via ToIntegerWithTruncation, month via ToPositiveIntegerWithTruncation,
   monthCode via ToString + well-formedness). Returns a plist
   (:day :month :month-code-num :month-code-leap :year), NIL where absent.
   Coercion happens during the read (observable); presence/validity checks are
   done by RESOLVE-DATE-FIELDS afterward."
  (let ((day nil) (month nil) (mc-num nil) (mc-leap nil) (mc-present nil) (year nil))
    (let ((v (js-get bag "day")))
      (unless (js-undefined-p v) (setf day (to-positive-integer-with-truncation v "day"))))
    (let ((v (js-get bag "month")))
      (unless (js-undefined-p v) (setf month (to-positive-integer-with-truncation v "month"))))
    (let ((v (js-get bag "monthCode")))
      (unless (js-undefined-p v)
        (setf mc-present t)
        ;; ToPrimitiveAndRequireString: ToPrimitive(v, string), then the result
        ;; MUST be a String primitive — a number/bigint/boolean/symbol is a
        ;; TypeError (not coerced). An object with a string-valued toString is OK.
        (let ((prim (if (js-object-p v) (to-primitive v :string) v)))
          (unless (stringp prim)
            (js-throw (make-native-error "TypeError" "monthCode must be a string")))
          (setf v prim))
        (let ((s v))
          (multiple-value-bind (ok num leap) (monthcode-well-formed-p s)
            (unless ok
              (js-throw (make-native-error "RangeError"
                          (format nil "monthCode '~a' is not well-formed" s))))
            (setf mc-num num mc-leap leap)))))
    (let ((v (js-get bag "year")))
      (unless (js-undefined-p v) (setf year (to-integer-with-truncation v))))
    (list :day day :month month :month-code-num mc-num
          :month-code-leap mc-leap :month-code-present mc-present :year year)))

(defun resolve-date-fields (fields overflow)
  "CalendarResolveFields (iso8601) + RegulateISODate. FIELDS is from
   READ-DATE-FIELDS. Enforces required-field presence (TypeError: year, day, and
   at least one of month/monthCode), month<->monthCode agreement, leap-month
   rejection, then regulates + range-checks. Returns a valid iso-date."
  (let ((year (getf fields :year))
        (day (getf fields :day))
        (month (getf fields :month))
        (mc-num (getf fields :month-code-num))
        (mc-leap (getf fields :month-code-leap))
        (mc-present (getf fields :month-code-present)))
    ;; Required fields (TypeError, before range validation).
    (when (null year)
      (js-throw (make-native-error "TypeError" "year is required")))
    (when (and (null month) (not mc-present))
      (js-throw (make-native-error "TypeError" "one of month or monthCode is required")))
    (when (null day)
      (js-throw (make-native-error "TypeError" "day is required")))
    ;; Resolve month from monthCode.
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
      (create-iso-date-checked year resolved-month day overflow))))

;;; ===========================================================================
;;; ToTemporalDate
;;; ===========================================================================
(defun iso-date-from-parse (r)
  "Build a validated iso-date from a parse-iso-datetime plist R (date part)."
  (let ((date (make-iso-date (getf r :year) (getf r :month) (getf r :day))))
    (unless (valid-iso-date-p date) (p-fail))
    (unless (iso-date-within-limits date)
      (js-throw (make-native-error "RangeError" "date out of range")))
    date))

(defun calendar-from-parse (r s)
  "The calendar id from a parsed string's [u-ca=...] annotation (defaults to
   iso8601). R is the parse-iso-datetime plist, which now surfaces :calendar. The
   recovered id must be iso8601 — RangeError otherwise."
  (declare (ignore s))
  (let ((cal (getf r :calendar)))
    (cond ((null cal) "iso8601")
          ((string-equal cal "iso8601") "iso8601")
          (t (js-throw (make-native-error "RangeError"
                         (format nil "unknown calendar: ~a" cal)))))))

(defun to-temporal-date (realm v &optional (options *undefined*))
  "ToTemporalDate: a PlainDate instance -> copy (options.overflow still read); a
   PlainDateTime/ZonedDateTime -> its date (overflow read); a property bag ->
   PrepareCalendarFields + resolve; a string -> parse (overflow read after).
   Returns (values iso-date calendar-id)."
  (cond
    ((plaindate-p v)
     (get-temporal-overflow (get-options-object options))
     (values (getf (js-object-internal v) :temporal-plaindate)
             (getf (js-object-internal v) :temporal-calendar "iso8601")))
    ;; Sibling datetime types (PlainDateTime / ZonedDateTime) expose their ISO
    ;; date + calendar via the same slot convention.
    ((and (js-object-p v) (getf (js-object-internal v) :temporal-plaindatetime))
     (get-temporal-overflow (get-options-object options))
     (let ((slot (getf (js-object-internal v) :temporal-plaindatetime)))
       (values (getf slot :date)
               (getf (js-object-internal v) :temporal-calendar "iso8601"))))
    ((and (js-object-p v) (getf (js-object-internal v) :temporal-zoneddatetime))
     (get-temporal-overflow (get-options-object options))
     (let* ((slot (getf (js-object-internal v) :temporal-zoneddatetime))
            (ns (getf slot :ns)))
       (multiple-value-bind (date time) (epoch-ns->iso-datetime ns)
         (declare (ignore time))
         (values date (getf (js-object-internal v) :temporal-calendar "iso8601")))))
    ((js-object-p v)
     ;; Property bag: read calendar first, then the date fields, then overflow.
     (let* ((cal-v (js-get v "calendar"))
            (calendar (if (js-undefined-p cal-v) "iso8601" (canonicalize-calendar-id cal-v)))
            (fields (read-date-fields v))
            (overflow (get-temporal-overflow (get-options-object options))))
       (values (resolve-date-fields fields overflow) calendar)))
    ((stringp v)
     (let* ((trimmed (string-trim '(#\Space #\Tab #\Newline #\Return) v))
            (r (parse-iso-datetime trimmed :datetime)))
       (when (getf r :z)
         (js-throw (make-native-error "RangeError"
                     "a UTC-offset Z string cannot be a PlainDate")))
       (let ((date (iso-date-from-parse r))
             (calendar (calendar-from-parse r trimmed)))
         (get-temporal-overflow (get-options-object options))
         (values date calendar))))
    (t (js-throw (make-native-error "TypeError" "cannot convert value to a Temporal.PlainDate")))))

;;; ===========================================================================
;;; ISO week-of-year (weekOfYear + yearOfWeek)
;;; ===========================================================================
(defun iso-week-of-year (date)
  "ISO-8601 week number + week-year. Returns (values week week-year)."
  (let* ((doy (1+ (- (iso-date->epoch-days date)
                     (iso-date->epoch-days (make-iso-date (iso-date-year date) 1 1)))))
         (dow (iso-day-of-week date))               ; 1..7 (Mon..Sun)
         (week (floor (+ (- doy dow) 10) 7))
         (year (iso-date-year date)))
    (cond
      ((< week 1)
       ;; Belongs to the last week of the previous year.
       (let ((py (1- year)))
         (values (iso-weeks-in-year py) py)))
      ((> week (iso-weeks-in-year year))
       (values 1 (1+ year)))
      (t (values week year)))))

(defun iso-weeks-in-year (year)
  "Number of ISO weeks (52 or 53) in YEAR."
  (flet ((p (y) (mod (+ y (floor y 4) (- (floor y 100)) (floor y 400)) 7)))
    (if (or (= (p year) 4) (= (p (1- year)) 3)) 53 52)))

(defun iso-day-of-year (date)
  (1+ (- (iso-date->epoch-days date)
         (iso-date->epoch-days (make-iso-date (iso-date-year date) 1 1)))))

;;; ===========================================================================
;;; toString
;;; ===========================================================================
(defun get-calendar-name-option (options)
  "GetTemporalShowCalendarNameOption: 'auto' (default) | 'always' | 'never' |
   'critical'."
  (get-option-string options "calendarName"
                     '(("auto" . :auto) ("always" . :always)
                       ("never" . :never) ("critical" . :critical))
                     :auto))

(defun format-calendar-annotation (calendar-id show)
  (ecase show
    (:never "")
    (:auto (if (string= calendar-id "iso8601") "" (format nil "[u-ca=~a]" calendar-id)))
    (:always (format nil "[u-ca=~a]" calendar-id))
    (:critical (format nil "[!u-ca=~a]" calendar-id))))

(defun plaindate-to-string (date calendar-id options)
  (let* ((opts (get-options-object options))
         (show (get-calendar-name-option opts)))
    (concatenate 'string
                 (format-iso-date-string (iso-date-year date) (iso-date-month date)
                                         (iso-date-day date))
                 (format-calendar-annotation calendar-id show))))

;;; ===========================================================================
;;; Sibling-type construction (dynamic dispatch through the realm registry)
;;; ===========================================================================
(defun registered-temporal-ctor (realm name)
  "The realm's Temporal.<name> constructor object, or NIL if that type
   hasn't registered yet."
  (let ((ns (temporal-namespace realm)))
    (when ns
      (let ((c (js-get ns name)))
        (when (and (js-object-p c) (js-object-construct c)) c)))))

(defun require-temporal-ctor (realm name)
  (or (registered-temporal-ctor realm name)
      (js-throw (make-native-error "TypeError"
                  (format nil "Temporal.~a is not implemented in this realm" name)))))

;;; ===========================================================================
;;; install
;;; ===========================================================================
(defun install-temporal-plaindate (realm)
  (let* ((op (realm-object-proto realm))
         (proto (make-object :proto op :class "Object"))
         (ctor (native-function realm "PlainDate"
                 (lambda (this args) (declare (ignore this args))
                   (js-throw (make-native-error "TypeError" "Constructor PlainDate requires 'new'")))
                 3)))
    (setf *temporal-plaindate-proto* proto)

    ;; ---- constructor: (isoYear, isoMonth, isoDay, calendar?) ----
    (setf (js-object-construct ctor)
          (lambda (args nt)
            (let ((y (to-integer-with-truncation (arg 0 args)))
                  (m (to-integer-with-truncation (arg 1 args)))
                  (d (to-integer-with-truncation (arg 2 args)))
                  (cal-v (arg 3 args)))
              (let ((calendar (if (js-undefined-p cal-v) "iso8601"
                                  (if (stringp cal-v)
                                      (if (string-equal cal-v "iso8601") "iso8601"
                                          (js-throw (make-native-error "RangeError"
                                                      "calendar must be iso8601")))
                                      (js-throw (make-native-error "TypeError"
                                                  "calendar must be a string"))))))
                (unless (valid-iso-date-fields-p y m d)
                  (js-throw (make-native-error "RangeError" "ISO date field out of range")))
                (let ((date (make-iso-date y m d)))
                  (unless (iso-date-within-limits date)
                    (js-throw (make-native-error "RangeError" "date out of range")))
                  (make-plain-date date calendar realm nt))))))
    (def-value ctor "prototype" proto :writable nil :configurable nil)
    (def-value proto "constructor" ctor)

    ;; ---- statics ----
    (def-method realm ctor "from" 1 (this args)
      (declare (ignore this))
      (multiple-value-bind (date calendar) (to-temporal-date realm (arg 0 args) (arg 1 args))
        (make-plain-date date calendar realm)))
    (def-method realm ctor "compare" 2 (this args)
      (declare (ignore this))
      (let ((a (to-temporal-date realm (arg 0 args)))
            (b (to-temporal-date realm (arg 1 args))))
        (let ((da (iso-date->epoch-days a)) (db (iso-date->epoch-days b)))
          (float (cond ((< da db) -1) ((> da db) 1) (t 0)) 1d0))))

    ;; ---- getters ----
    (macrolet ((dgetter (name &body body)
                 `(def-getter realm proto ,name
                    (lambda (this args) (declare (ignore args))
                      (let ((date (pd-iso-date this)))
                        (declare (ignorable date))
                        ,@body)))))
      (dgetter "calendarId" (declare (ignore date)) (pd-calendar-id this))
      (dgetter "year" (float (iso-date-year date) 1d0))
      (dgetter "month" (float (iso-date-month date) 1d0))
      (dgetter "monthCode" (format nil "M~2,'0d" (iso-date-month date)))
      (dgetter "day" (float (iso-date-day date) 1d0))
      (dgetter "dayOfWeek" (float (iso-day-of-week date) 1d0))
      (dgetter "dayOfYear" (float (iso-day-of-year date) 1d0))
      (dgetter "weekOfYear"
        (multiple-value-bind (w y) (iso-week-of-year date) (declare (ignore y))
          (float w 1d0)))
      (dgetter "yearOfWeek"
        (multiple-value-bind (w y) (iso-week-of-year date) (declare (ignore w))
          (float y 1d0)))
      (dgetter "daysInWeek" 7d0)
      (dgetter "daysInMonth" (float (days-in-month (iso-date-year date) (iso-date-month date)) 1d0))
      (dgetter "daysInYear" (float (iso-days-in-year (iso-date-year date)) 1d0))
      (dgetter "monthsInYear" 12d0)
      (dgetter "inLeapYear" (js-bool (leap-year-p (iso-date-year date))))
      (dgetter "era" (declare (ignore date)) *undefined*)
      (dgetter "eraYear" (declare (ignore date)) *undefined*))

    ;; ---- add / subtract ----
    (labels ((add-dur (this args negate)
               (let* ((date (pd-iso-date this))
                      (calendar (pd-calendar-id this))
                      (d (to-temporal-duration-record (arg 0 args)))
                      (overflow (get-temporal-overflow (get-options-object (arg 1 args))))
                      (sign (if negate -1 1)))
                 ;; Time components must balance into whole days (they're durations
                 ;; with no time-of-day carry here — add their day-equivalent).
                 (let* ((time-days (truncate (duration-time-ns d) +ns-per-day+))
                        (result (add-iso-date date
                                  (* sign (getf d :years)) (* sign (getf d :months))
                                  (* sign (getf d :weeks))
                                  (* sign (+ (getf d :days) time-days))
                                  overflow)))
                   (unless (iso-date-within-limits result)
                     (js-throw (make-native-error "RangeError" "result out of range")))
                   (make-plain-date result calendar realm)))))
      (def-method realm proto "add" 1 (this args) (add-dur this args nil))
      (def-method realm proto "subtract" 1 (this args) (add-dur this args t)))

    ;; ---- with ----
    (def-method realm proto "with" 1 (this args)
      (let ((date (pd-iso-date this))
            (calendar (pd-calendar-id this))
            (bag (arg 0 args)))
        (unless (js-object-p bag)
          (js-throw (make-native-error "TypeError" "with() argument must be an object")))
        (when (temporal-branded-object-p bag)
          (js-throw (make-native-error "TypeError" "with() argument must be a plain object, not a Temporal instance")))
        (reject-calendar-or-timezone bag)
        ;; Read partial fields (alpha order), fill from THIS, then resolve via
        ;; the same validator as from() so monthCode range / conflicts throw.
        (let* ((partial (read-date-fields bag))
               (overflow (get-temporal-overflow (get-options-object (arg 1 args))))
               (any (or (getf partial :day) (getf partial :month)
                        (getf partial :month-code-present) (getf partial :year))))
          (unless any
            (js-throw (make-native-error "TypeError" "with() needs at least one recognized field")))
          ;; Merge: supply this date's fields for anything absent. If neither
          ;; month nor monthCode is given, inherit the current month.
          (let ((merged
                  (list :year (or (getf partial :year) (iso-date-year date))
                        :day  (or (getf partial :day) (iso-date-day date))
                        :month (getf partial :month)
                        :month-code-num (getf partial :month-code-num)
                        :month-code-leap (getf partial :month-code-leap)
                        :month-code-present (getf partial :month-code-present))))
            (unless (or (getf merged :month) (getf merged :month-code-present))
              (setf (getf merged :month) (iso-date-month date)))
            (make-plain-date (resolve-date-fields merged overflow) calendar realm)))))

    ;; ---- withCalendar ----
    (def-method realm proto "withCalendar" 1 (this args)
      (let ((date (pd-iso-date this))
            (calendar (canonicalize-calendar-id (arg 0 args))))
        (make-plain-date date calendar realm)))

    ;; ---- until / since ----
    (labels ((diff (this args op)
               (let* ((d1 (pd-iso-date this))
                      (cal1 (pd-calendar-id this)))
                 (multiple-value-bind (d2 cal2) (to-temporal-date realm (arg 0 args))
                   (unless (string= cal1 cal2)
                     (js-throw (make-native-error "RangeError"
                                 "cannot compute difference between dates of different calendars")))
                   (let ((options (get-options-object (arg 1 args))))
                     (multiple-value-bind (smallest largest increment mode)
                         (get-date-difference-settings op options)
                       (if (zerop (- (iso-date->epoch-days d2) (iso-date->epoch-days d1)))
                           (make-temporal-duration realm (empty-duration))
                           (let* ((dur (difference-iso-date-rounded
                                        d1 d2 largest smallest increment mode))
                                  (final (if (eq op :since) (negate-date-duration dur) dur)))
                             (make-temporal-duration realm final))))))))
             (negate-date-duration (d)
               (list :years (- (getf d :years)) :months (- (getf d :months))
                     :weeks (- (getf d :weeks)) :days (- (getf d :days))
                     :hours 0 :minutes 0 :seconds 0 :milliseconds 0
                     :microseconds 0 :nanoseconds 0)))
      (def-method realm proto "until" 1 (this args) (diff this args :until))
      (def-method realm proto "since" 1 (this args) (diff this args :since)))

    ;; ---- equals ----
    (def-method realm proto "equals" 1 (this args)
      (let ((d1 (pd-iso-date this))
            (cal1 (pd-calendar-id this)))
        (multiple-value-bind (d2 cal2) (to-temporal-date realm (arg 0 args))
          (js-bool (and (= (iso-date-year d1) (iso-date-year d2))
                        (= (iso-date-month d1) (iso-date-month d2))
                        (= (iso-date-day d1) (iso-date-day d2))
                        (string= cal1 cal2))))))

    ;; ---- toPlainDateTime ----
    (def-method realm proto "toPlainDateTime" 0 (this args)
      (let* ((date (pd-iso-date this))
             (calendar (pd-calendar-id this))
             (pdt-ctor (require-temporal-ctor realm "PlainDateTime"))
             (time (pd-to-iso-time realm (arg 0 args))))
        (js-construct pdt-ctor
          (list (float (iso-date-year date) 1d0) (float (iso-date-month date) 1d0)
                (float (iso-date-day date) 1d0)
                (float (iso-time-hour time) 1d0) (float (iso-time-minute time) 1d0)
                (float (iso-time-second time) 1d0) (float (iso-time-millisecond time) 1d0)
                (float (iso-time-microsecond time) 1d0) (float (iso-time-nanosecond time) 1d0)
                calendar))))

    ;; ---- toPlainYearMonth ----
    (def-method realm proto "toPlainYearMonth" 0 (this args)
      (declare (ignore args))
      (let* ((date (pd-iso-date this))
             (calendar (pd-calendar-id this))
             (pym-ctor (require-temporal-ctor realm "PlainYearMonth")))
        ;; For iso8601 the resulting PlainYearMonth's reference ISO day is the
        ;; canonical 1 (CalendarYearMonthFromFields), NOT the source date's day.
        (js-construct pym-ctor
          (list (float (iso-date-year date) 1d0) (float (iso-date-month date) 1d0)
                calendar 1d0))))

    ;; ---- toPlainMonthDay ----
    (def-method realm proto "toPlainMonthDay" 0 (this args)
      (declare (ignore args))
      (let* ((date (pd-iso-date this))
             (calendar (pd-calendar-id this))
             (pmd-ctor (require-temporal-ctor realm "PlainMonthDay")))
        ;; For iso8601 the resulting PlainMonthDay's reference ISO year is the
        ;; canonical 1972 (a leap year), NOT the source date's year.
        (js-construct pmd-ctor
          (list (float (iso-date-month date) 1d0) (float (iso-date-day date) 1d0)
                calendar 1972d0))))

    ;; ---- toZonedDateTime ----
    ;; Dispatch dynamically to the realm's Temporal.ZonedDateTime if present (the
    ;; concurrent ZDT type lights this up); a clear TypeError otherwise. ITEM is a
    ;; time-zone string, or { timeZone, plainTime? }.
    (def-method realm proto "toZonedDateTime" 1 (this args)
      (let ((date (pd-iso-date this))
            (calendar (pd-calendar-id this))
            (item (arg 0 args)))
        (unless (and (fboundp 'to-time-zone-identifier) (fboundp 'make-zoneddatetime))
          (js-throw (make-native-error "TypeError" "Temporal.ZonedDateTime is not available")))
        (multiple-value-bind (tz-id offset time)
            (if (and (js-object-p item) (not (js-undefined-p (js-get item "timeZone"))))
                ;; { timeZone, plainTime? }
                (multiple-value-bind (id off) (funcall 'to-time-zone-identifier (js-get item "timeZone"))
                  (let ((pt (js-get item "plainTime")))
                    (values id off
                            (if (js-undefined-p pt)
                                (make-iso-time 0 0 0 0 0 0)
                                (to-temporal-time realm pt)))))
                ;; a bare time-zone value -> midnight
                (multiple-value-bind (id off) (funcall 'to-time-zone-identifier item)
                  (values id off (make-iso-time 0 0 0 0 0 0))))
          (let ((ns (- (iso-datetime->epoch-ns date time) offset)))
            (unless (valid-epoch-ns-p ns)
              (js-throw (make-native-error "RangeError" "ZonedDateTime out of range")))
            (funcall 'make-zoneddatetime realm ns tz-id offset calendar)))))

    ;; ---- toString / toJSON / toLocaleString ----
    (def-method realm proto "toString" 0 (this args)
      (plaindate-to-string (pd-iso-date this) (pd-calendar-id this) (arg 0 args)))
    (def-method realm proto "toJSON" 0 (this args)
      (declare (ignore args))
      (plaindate-to-string (pd-iso-date this) (pd-calendar-id this) *undefined*))
    (def-method realm proto "toLocaleString" 0 (this args)
      (declare (ignore args))
      (plaindate-to-string (pd-iso-date this) (pd-calendar-id this) *undefined*))

    ;; ---- valueOf: not a primitive ----
    (def-method realm proto "valueOf" 0 (this args)
      (declare (ignore args))
      (js-throw (make-native-error "TypeError"
                  "Cannot convert a Temporal.PlainDate to a primitive; use compare() or equals()")))

    ;; ---- @@toStringTag ----
    (put proto (symbol-tostringtag realm) "Temporal.PlainDate"
         :enumerable nil :writable nil :configurable t)

    (temporal-register realm "PlainDate" ctor)
    ctor))

;;; ===========================================================================
;;; helpers
;;; ===========================================================================
(defun plaindate-max-increment (unit)
  "MaximumTemporalDurationRoundingIncrement for date units: unbounded (spec
   returns undefined) — we use a large sentinel so validate-rounding-increment
   only enforces >= 1."
  (declare (ignore unit))
  most-positive-fixnum)

(defun pd-to-iso-time (realm v)
  "Coerce V (a PlainTime instance, a time string, a time bag, or undefined) to an
   iso-time for toPlainDateTime. Undefined -> midnight."
  (declare (ignore realm))
  (if (js-undefined-p v)
      (make-iso-time 0 0 0 0 0 0)
      (to-temporal-time realm v)))

(defun get-date-difference-settings (op options)
  "GetDifferenceSettings specialized for PlainDate: units restricted to
   year/month/week/day, and (unlike the generic kernel helper) NO
   divide-evenly / maximum-increment constraint — date units have an undefined
   maximum, so any integer increment >= 1 is accepted. Reads largestUnit,
   roundingIncrement, roundingMode, smallestUnit in spec order. Returns
   (values smallest largest increment mode)."
  (let* ((date-units '(:year :month :week :day))
         ;; Read ALL four options first (against the full unit table so any unit
         ;; name parses), THEN validate membership — reads must precede
         ;; algorithmic validation (observable order).
         (every-unit '(:year :month :week :day :hour :minute :second
                       :millisecond :microsecond :nanosecond))
         (largest (get-temporal-unit options "largestUnit" :datetime nil
                                     every-unit '(("auto" . :auto))))
         (increment (get-rounding-increment options))
         (mode (get-rounding-mode options :trunc))
         (smallest (get-temporal-unit options "smallestUnit" :datetime nil
                                      every-unit)))
    (when (and largest (not (eq largest :auto)) (not (member largest date-units)))
      (js-throw (make-native-error "RangeError" "largestUnit not allowed here")))
    (when (and smallest (not (member smallest date-units)))
      (js-throw (make-native-error "RangeError" "smallestUnit not allowed here")))
    (when (eq op :since) (setf mode (negate-rounding-mode mode)))
    (let* ((sm (or smallest :day))
           (lg (cond ((or (null largest) (eq largest :auto))
                      (if (< (unit-rank sm) (unit-rank :day)) sm :day))
                     (t largest))))
      (when (< (unit-rank sm) (unit-rank lg))
        (js-throw (make-native-error "RangeError" "smallestUnit is coarser than largestUnit")))
      (validate-rounding-increment increment most-positive-fixnum nil)
      (values sm lg increment mode))))

(defun add-unit-to-date (date unit count overflow)
  "Add COUNT of UNIT (:year/:month/:week/:day) to DATE via AddISODate."
  (ecase unit
    (:year  (add-iso-date date count 0 0 0 overflow))
    (:month (add-iso-date date 0 count 0 0 overflow))
    (:week  (add-iso-date date 0 0 count 0 overflow))
    (:day   (add-iso-date date 0 0 0 count overflow))))

(defun date-duration-in-unit (dur unit)
  "The signed whole count of UNIT already present in the (un-nudged) date
   difference DUR expressed with largestUnit=UNIT. For :year/:month/:week the
   sub-unit remainder lives in the lower fields; for :day the whole thing is
   days+weeks*7."
  (ecase unit
    (:year  (getf dur :years))
    (:month (+ (* (getf dur :years) 12) (getf dur :months)))
    (:week  (getf dur :weeks))
    (:day   (+ (* (getf dur :weeks) 7) (getf dur :days)))))

(defun coarser-part-date (d1 dur smallest)
  "The date reached by adding to D1 only the components of DUR coarser than
   SMALLEST (the nudge anchor). E.g. for SMALLEST=:week this is d1 + years +
   months; for SMALLEST=:day it is d1 + years + months + weeks."
  (ecase smallest
    (:year  d1)
    (:month (add-iso-date d1 (getf dur :years) 0 0 0 :constrain))
    (:week  (add-iso-date d1 (getf dur :years) (getf dur :months) 0 0 :constrain))
    (:day   (add-iso-date d1 (getf dur :years) (getf dur :months) (getf dur :weeks) 0 :constrain))))

(defun difference-iso-date-rounded (d1 d2 largest smallest increment mode)
  "DifferenceISODate then RoundDuration for the date-only case: the whole
   calendar difference from D1 to D2 with LARGEST unit, rounding the SMALLEST
   unit (to INCREMENT per MODE) while preserving coarser units. Full plist."
  (let ((dur (difference-iso-date d1 d2 largest)))
    (if (and (eq smallest :day) (= increment 1))
        dur
        ;; NudgeToCalendarUnit: anchor at the coarser part, round the SMALLEST
        ;; unit over the residual span, then carry.
        (let* ((anchor (coarser-part-date d1 dur smallest))
               (sign (let ((dd (- (iso-date->epoch-days d2) (iso-date->epoch-days anchor))))
                       (cond ((plusp dd) 1) ((minusp dd) -1) (t 0))))
               (residual (date-duration-in-unit
                          (difference-iso-date anchor d2 smallest) smallest))
               (r1 (* increment (if (minusp sign)
                                    (ceiling residual increment)
                                    (floor residual increment))))
               (r2 (+ r1 (* increment sign)))
               (date-r1 (add-unit-to-date anchor smallest r1 :constrain))
               (date-r2 (add-unit-to-date anchor smallest r2 :constrain))
               (span (- (iso-date->epoch-days date-r2) (iso-date->epoch-days date-r1))))
          ;; For irregular-length units (year/month/week) the rounding boundaries
          ;; are produced by CalendarDateAdd and must fall within the valid ISO
          ;; range. Day rounding is pure epoch arithmetic with no such boundary.
          (unless (eq smallest :day)
            (unless (and (iso-date-within-limits date-r1) (iso-date-within-limits date-r2))
              (js-throw (make-native-error "RangeError" "rounded date outside valid ISO range"))))
          (let ((rounded-units
                  (if (zerop span)
                      r1
                      (let* ((progress (/ (- (iso-date->epoch-days d2)
                                             (iso-date->epoch-days date-r1))
                                          span))
                             (total (+ (/ r1 increment) (* progress sign))))
                        (* increment (apply-rounding-mode total mode))))))
            ;; Endpoint = anchor + rounded SMALLEST units; re-difference with
            ;; LARGEST so a full unit carries (e.g. 12m -> 1y).
            (let ((endpoint (add-unit-to-date anchor smallest rounded-units :constrain)))
              (if (member smallest '(:year :month))
                  (difference-iso-date d1 endpoint largest)
                  ;; week/day: coarser (year/month) part is exact; add the rounded
                  ;; week/day tail expressed under LARGEST.
                  (let ((days (- (iso-date->epoch-days endpoint)
                                 (iso-date->epoch-days anchor))))
                    (case smallest
                      (:week
                       (list :years (getf dur :years) :months (getf dur :months)
                             :weeks (truncate days 7) :days 0
                             :hours 0 :minutes 0 :seconds 0 :milliseconds 0
                             :microseconds 0 :nanoseconds 0))
                      (:day
                       (if (eq largest :week)
                           (list :years (getf dur :years) :months (getf dur :months)
                                 :weeks (+ (getf dur :weeks) (truncate days 7))
                                 :days (- days (* 7 (truncate days 7)))
                                 :hours 0 :minutes 0 :seconds 0 :milliseconds 0
                                 :microseconds 0 :nanoseconds 0)
                           (list :years (getf dur :years) :months (getf dur :months)
                                 :weeks (getf dur :weeks) :days days
                                 :hours 0 :minutes 0 :seconds 0 :milliseconds 0
                                 :microseconds 0 :nanoseconds 0))))))))))))

(register-builtin-installer 'install-temporal-plaindate)
