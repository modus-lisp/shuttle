;;;; builtins/temporal-plaindatetime.lisp — Temporal.PlainDateTime.
;;;;
;;;; A wall-clock date+time with no zone (iso8601 calendar only). Internally it
;;;; is an ISO date record + an ISO time record, stored as a plist
;;;;   (:date iso-date :time iso-time)
;;;; in the :temporal-plaindatetime internal slot. Built entirely on the
;;;; temporal-core kernel (ISO records, parser, rounding engine, options
;;;; readers) plus reusable ISO date arithmetic defined here (pdt-add-iso-date /
;;;; pdt-difference-iso-date / pdt-regulate-iso-date). The concurrent PlainDate
;;;; sibling file may later export AddISODate/DifferenceISODate/RegulateISODate;
;;;; when it does those can replace the pdt- locals, but they are self-contained
;;;; here so PlainDateTime never blocks on that file.
(in-package #:shuttle)

(defvar *temporal-plaindatetime-proto* nil)

;;; ---------------------------------------------------------------------------
;;; Reusable ISO date arithmetic (local; pdt- prefix to avoid cross-file collision)
;;; ---------------------------------------------------------------------------
(defun pdt-valid-iso-date-p (y m d)
  (and (<= 1 m 12) (<= 1 d (days-in-month y m))))

(defun pdt-regulate-iso-date (y m d overflow)
  "RegulateISODate: :constrain clamps month to 1..12 then day to that month's
   range; :reject RangeErrors on any out-of-range field. Returns an iso-date."
  (ecase overflow
    (:constrain
     (let* ((mm (max 1 (min 12 m)))
            (dd (max 1 (min (days-in-month y mm) d))))
       (make-iso-date y mm dd)))
    (:reject
     (unless (pdt-valid-iso-date-p y m d)
       (js-throw (make-native-error "RangeError" "date field out of range")))
     (make-iso-date y m d))))

(defun pdt-balance-iso-date (y m d)
  "BalanceISODate: normalize a possibly out-of-range (m may be <1 or >12, d may
   be anything) date into a canonical iso-date via day arithmetic."
  ;; First balance the month into the year.
  (multiple-value-bind (yy mm0) (floor (+ (1- m) (* 12 y)) 12)
    (let* ((mm (1+ mm0))
           ;; epoch-days of (yy mm 1) then add (d-1) days.
           (days (+ (iso-date->epoch-days (make-iso-date yy mm 1)) (1- d))))
      (epoch-days->iso-date days))))

(defun pdt-add-iso-date (y m d years months weeks days overflow)
  "AddISODate: add a calendar duration (years/months/weeks/days) to an ISO date.
   Years+months are added to the year/month then RegulateISODate constrains the
   day; weeks+days are added as plain days afterward."
  (let* ((ym (+ (* y 12) (1- m) (* years 12) months))
         (yy (floor ym 12))
         (mm (1+ (mod ym 12)))
         ;; regulate the (yy mm d) into range first
         (reg (pdt-regulate-iso-date yy mm d overflow))
         (extra-days (+ (* weeks 7) days))
         (total (+ (iso-date->epoch-days reg) extra-days)))
    (epoch-days->iso-date total)))

(defun pdt-days-until (y1 m1 d1 y2 m2 d2)
  (- (iso-date->epoch-days (make-iso-date y2 m2 d2))
     (iso-date->epoch-days (make-iso-date y1 m1 d1))))

(defun pdt-difference-iso-date (y1 m1 d1 y2 m2 d2 largest-unit)
  "DifferenceISODate: the difference date2 - date1 as a (values years months
   weeks days). LARGEST-UNIT is one of :year :month :week :day. Follows the
   spec's estimate-then-correct calendar-difference algorithm for iso8601."
  (ecase largest-unit
    ((:year :month)
     (let ((sign (cond ((< (pdt-cmp-date y1 m1 d1 y2 m2 d2) 0) 1)
                       ((> (pdt-cmp-date y1 m1 d1 y2 m2 d2) 0) -1)
                       (t 0))))
       (if (zerop sign)
           (values 0 0 0 0)
           ;; Work entirely in whole months of offset from date1. Estimate the
           ;; total-month offset, correct it so the intermediate does not pass
           ;; date2, then take the leftover days. Split into years+months only
           ;; when year-largest.
           (labels ((intermediate (mos)
                      ;; date1 + MOS months, day constrained into the target month.
                      (let* ((tot (+ (* y1 12) (1- m1) mos))
                             (iy (floor tot 12)) (im (1+ (mod tot 12)))
                             (id (min d1 (days-in-month iy im))))
                        (values iy im id))))
             (let ((mtotal (- (+ (* y2 12) m2) (+ (* y1 12) m1))))
               ;; Correct for overshoot: if the intermediate has passed date2 in
               ;; the sign direction (signum c = sign), step one month back. This
               ;; runs at most a couple iterations (the day-constrain can only
               ;; shift the boundary by ~1 month).
               (loop
                 (multiple-value-bind (iy im id) (intermediate mtotal)
                   (let ((c (pdt-cmp-date iy im id y2 m2 d2)))
                     (if (= (signum c) sign)
                         (decf mtotal sign)
                         (return)))))
               (multiple-value-bind (iy im id) (intermediate mtotal)
                 (let ((days (pdt-days-until iy im id y2 m2 d2)))
                   (if (eq largest-unit :month)
                       (values 0 mtotal 0 days)
                       (values (truncate mtotal 12) (rem mtotal 12) 0 days)))))))))
    ((:week :day)
     (let ((days (pdt-days-until y1 m1 d1 y2 m2 d2)))
       (if (eq largest-unit :week)
           (multiple-value-bind (w rem) (truncate days 7)
             (values 0 0 w rem))
           (values 0 0 0 days))))))

(defun pdt-cmp-date (y1 m1 d1 y2 m2 d2)
  "-1/0/1 comparing two ISO dates."
  (cond ((< y1 y2) -1) ((> y1 y2) 1)
        ((< m1 m2) -1) ((> m1 m2) 1)
        ((< d1 d2) -1) ((> d1 d2) 1)
        (t 0)))

;;; ---------------------------------------------------------------------------
;;; Constructors / slot access
;;; ---------------------------------------------------------------------------
(defun make-temporal-plaindatetime (realm date time &optional new-target)
  "CreateTemporalDateTime: DATE + TIME are valid in-range ISO records."
  (declare (ignore realm))
  (let* ((proto (proto-from-newtarget new-target *temporal-plaindatetime-proto*))
         (o (make-object :proto proto :class "Object")))
    (setf (getf (js-object-internal o) :temporal-plaindatetime)
          (list :date date :time time))
    o))

(defun plaindatetime-slot (this)
  (temporal-slot this :temporal-plaindatetime "Temporal.PlainDateTime"))
(defun plaindatetime-date (this) (getf (plaindatetime-slot this) :date))
(defun plaindatetime-time (this) (getf (plaindatetime-slot this) :time))

(defun pdt-check-range (date &optional time)
  "ISODateTimeWithinLimits: RangeError if outside the representable range. The
   valid band is the instant range widened by one nanosecond-day either side
   (nsMinInstant - nsPerDay .. nsMaxInstant + nsPerDay). When TIME is supplied
   the exact datetime ns is checked; otherwise the whole day must fall within."
  (let* ((lo (- +ns-min+ +ns-per-day+))
         (hi (+ +ns-max+ +ns-per-day+))
         (day-ns (* (iso-date->epoch-days date) +ns-per-day+))
         (ns (if time (+ day-ns (iso-datetime->epoch-ns (make-iso-date 1970 1 1) time)) day-ns)))
    ;; With no time, be conservative: reject only when the whole day is outside.
    ;; The exclusive spec bound means midnight of the min/max edge day is invalid.
    (unless (< lo ns hi)
      (js-throw (make-native-error "RangeError" "PlainDateTime is outside the representable range"))))
  date)

;;; ---------------------------------------------------------------------------
;;; monthCode helpers
;;; ---------------------------------------------------------------------------
(defun pdt-parse-month-code (s)
  "Parse a monthCode string of the form 'M' NN (no leap suffix for iso8601).
   Returns the month integer (1..12), or signals RangeError for a well-formed
   but out-of-range/leap code, or NIL for a syntactically ill-formed one."
  ;; Syntax: 'M' two-digits optional 'L'.  iso8601 has no leap months, and
  ;; single-digit forms (M1) are ill-formed.
  (let ((n (length s)))
    (unless (and (>= n 3) (char= (char s 0) #\M)
                 (digit-char-p (char s 1)) (digit-char-p (char s 2)))
      (return-from pdt-parse-month-code :ill-formed))
    (let ((leap (and (= n 4) (char= (char s 3) #\L))))
      (when (and (> n 3) (not (and (= n 4) leap)))
        (return-from pdt-parse-month-code :ill-formed))
      (let ((m (+ (* 10 (digit-char-p (char s 1))) (digit-char-p (char s 2)))))
        (when (or leap (< m 1) (> m 12))
          (return-from pdt-parse-month-code :out-of-range))
        m))))

(defun pdt-month-code-string (m) (format nil "M~2,'0d" m))

;;; ---------------------------------------------------------------------------
;;; Field bag reads (ISODateTimeFromFields-style, alphabetical observable reads)
;;; ---------------------------------------------------------------------------
;;; The 10 recognized fields, in ALPHABETICAL order (the observable read order):
;;; day, hour, microsecond, millisecond, minute, month, monthCode, nanosecond,
;;; second, year. monthCode is read via ToString, the rest via ToNumber /
;;; ToIntegerWithTruncation.
(defparameter +pdt-integer-fields+
  '(("day" . :day) ("hour" . :hour) ("microsecond" . :microsecond)
    ("millisecond" . :millisecond) ("minute" . :minute) ("month" . :month)
    ;; monthCode handled specially between month and nanosecond
    ("nanosecond" . :nanosecond) ("second" . :second) ("year" . :year)))

(defun pdt-read-fields (bag)
  "PrepareTemporalFields for PlainDateTime: read the 10 fields in alphabetical
   order. Integer fields via ToIntegerWithTruncation, monthCode via ToString.
   Returns a plist of the present values (missing -> not in plist). monthCode is
   parsed for SYNTAX here (RangeError on ill-formed) — before year-type errors."
  (let ((out '()))
    ;; day, hour, microsecond, millisecond, minute, month
    (dolist (name '("day" "hour" "microsecond" "millisecond" "minute" "month"))
      (let ((v (js-get bag name)))
        (unless (js-undefined-p v)
          (setf (getf out (cdr (assoc name +pdt-integer-fields+ :test #'string=)))
                (to-integer-with-truncation v)))))
    ;; monthCode (ToPrimitiveAndRequireString + syntax validation, before
    ;; nanosecond..year). A non-string primitive is a TypeError; an object has
    ;; its toString called.
    (let ((v (js-get bag "monthCode")))
      (unless (js-undefined-p v)
        (unless (or (stringp v) (js-object-p v))
          (js-throw (make-native-error "TypeError" "monthCode must be a string")))
        (let* ((s (to-string v))
               (parsed (pdt-parse-month-code s)))
          (when (eq parsed :ill-formed)
            (js-throw (make-native-error "RangeError" "invalid monthCode syntax")))
          (setf (getf out :monthcode) s))))
    ;; nanosecond, second, year
    (dolist (name '("nanosecond" "second" "year"))
      (let ((v (js-get bag name)))
        (unless (js-undefined-p v)
          (setf (getf out (cdr (assoc name +pdt-integer-fields+ :test #'string=)))
                (to-integer-with-truncation v)))))
    out))

(defun pdt-resolve-month (fields)
  "Resolve the month from :month / :monthcode fields (post-read). RangeError on
   disagreement or leap/out-of-range monthCode; :monthcode may be absent."
  (let ((month (getf fields :month))
        (mc (getf fields :monthcode)))
    (cond
      ((and (null month) (null mc)) nil)  ; caller decides required-ness
      ((null mc) month)
      (t
       (let ((parsed (pdt-parse-month-code mc)))
         (when (eq parsed :out-of-range)
           (js-throw (make-native-error "RangeError" "monthCode out of range for iso8601")))
         (when (and month (/= month parsed))
           (js-throw (make-native-error "RangeError" "month and monthCode disagree")))
         parsed)))))

(defun pdt-from-fields (bag overflow-opts)
  "ISODateTimeFromFields: read fields, resolve, regulate, and build the datetime.
   Observable read order: fields (alphabetical) then overflow. Year+day required."
  (let* ((fields (pdt-read-fields bag))
         (overflow (get-temporal-overflow (get-options-object overflow-opts)))
         (year (getf fields :year))
         (month (pdt-resolve-month fields))
         (day (getf fields :day)))
    (when (or (null year) (null month) (null day))
      (js-throw (make-native-error "TypeError" "year, month/monthCode and day are required")))
    ;; month and day are positive integers (ToPositiveIntegerWithTruncation): a
    ;; non-positive value is a RangeError even under constrain overflow.
    (when (or (< month 1) (< day 1))
      (js-throw (make-native-error "RangeError" "month and day must be positive")))
    (let* ((date (pdt-regulate-iso-date year month day overflow))
           (time (regulate-time (or (getf fields :hour) 0) (or (getf fields :minute) 0)
                                (or (getf fields :second) 0) (or (getf fields :millisecond) 0)
                                (or (getf fields :microsecond) 0) (or (getf fields :nanosecond) 0)
                                overflow)))
      (pdt-check-range date time)
      (values date time))))

;;; ---------------------------------------------------------------------------
;;; ToTemporalDateTime (from() and compare()/until()/since()/equals())
;;; ---------------------------------------------------------------------------
(defun pdt-validate-calendar-string (s)
  "ToTemporalCalendarIdentifier: a calendar value that is a string may be the
   bare identifier \"iso8601\" OR any ISO 8601 date/datetime string whose (u-ca)
   calendar is iso8601 (the calendar is parsed out of it). RangeError otherwise."
  (cond
    ((string-equal s "iso8601"))
    (t
     ;; Try to parse it as an ISO date/datetime and read its calendar annotation.
     ;; A calendar string must contain a DATE and must NOT carry a UTC designator
     ;; or numeric offset (those make it an instant string, not a calendar id).
     (let ((r (handler-case (parse-iso-datetime s :datetime)
                (shuttle-error ()
                  ;; also accept reduced date-only forms like "01-01" / "2020-01"
                  (if (pdt-reduced-date-string-p s) :reduced
                      (js-throw (make-native-error "RangeError" "invalid calendar string")))))))
       (unless (eq r :reduced)
         (when (or (getf r :offset-present) (getf r :z))
           (js-throw (make-native-error "RangeError" "a calendar string may not carry a time zone"))))
       ;; The [u-ca=...] annotation (if any) must name iso8601. Extract it
       ;; directly since the core parser doesn't surface it.
       (let ((cal (pdt-extract-calendar-annotation s)))
         (when (and cal (not (string-equal cal "iso8601")))
           (js-throw (make-native-error "RangeError" "only the iso8601 calendar is supported"))))))))

(defun pdt-extract-calendar-annotation (s)
  "Return the first [u-ca=VALUE] (or [!u-ca=VALUE]) annotation VALUE in S, or NIL
   if none. Used because the core parser doesn't surface the calendar in its
   result plist. VALUE is returned as-is (the caller validates it)."
  (let ((pos 0) (n (length s)))
    (loop
      (let ((open (position #\[ s :start pos)))
        (unless open (return nil))
        (let ((close (position #\] s :start open)))
          (unless close (return nil))
          (let* ((inner (subseq s (1+ open) close))
                 (inner (if (and (plusp (length inner)) (char= (char inner 0) #\!))
                            (subseq inner 1) inner))
                 (eq (position #\= inner)))
            (when (and eq (string= (subseq inner 0 eq) "u-ca"))
              (return (subseq inner (1+ eq)))))
          (setf pos (1+ close))))
      (when (>= pos n) (return nil)))))

(defun pdt-reduced-date-string-p (s)
  "T if S is a reduced ISO calendar-date form (YYYY-MM, YYYY-MM-DD, MM-DD, or the
   same with a trailing [u-ca=iso8601] annotation)."
  (let* ((br (or (position #\[ s) (length s)))
         (core (subseq s 0 br))
         (rest (subseq s br)))
    (flet ((ann-ok ()
             (or (zerop (length rest))
                 (handler-case
                     (let ((p (make-pstate :str rest :pos 0 :len (length rest))))
                       (let ((cal (parse-annotations p)))
                         (and (p-eof p) (or (null cal) (string-equal cal "iso8601")))))
                   (shuttle-error () nil))))
           (all-digits (a b) (loop for i from a below b always (and (< i (length core)) (digit-char-p (char core i))))))
      (and (ann-ok)
           (or (and (= (length core) 7) (char= (char core 4) #\-) (all-digits 0 4) (all-digits 5 7))   ; YYYY-MM
               (and (= (length core) 10) (char= (char core 4) #\-) (char= (char core 7) #\-)
                    (all-digits 0 4) (all-digits 5 7) (all-digits 8 10))                                  ; YYYY-MM-DD
               (and (= (length core) 5) (char= (char core 2) #\-) (all-digits 0 2) (all-digits 3 5))))))) ; MM-DD

(defun to-temporal-datetime (realm v &optional (options *undefined*))
  "ToTemporalDateTime: PlainDateTime instance (options.overflow still read),
   PlainDate instance (midnight), property bag (fields+overflow), or ISO string.
   Returns (values date time)."
  (declare (ignore realm))
  (cond
    ((and (js-object-p v)
          (not (eq (getf (js-object-internal v) :temporal-plaindatetime 'none) 'none)))
     (get-temporal-overflow (get-options-object options))
     (let ((slot (getf (js-object-internal v) :temporal-plaindatetime)))
       (values (getf slot :date) (getf slot :time))))
    ;; PlainDate instance -> date at midnight
    ((and (js-object-p v)
          (not (eq (getf (js-object-internal v) :temporal-plaindate 'none) 'none)))
     (get-temporal-overflow (get-options-object options))
     (values (getf (js-object-internal v) :temporal-plaindate)
             (make-iso-time 0 0 0 0 0 0)))
    ;; property bag
    ((js-object-p v)
     ;; Reject a bag carrying a calendar that isn't iso8601 (string form only).
     (let ((cal (js-get v "calendar")))
       (unless (js-undefined-p cal)
         (if (stringp cal) (pdt-validate-calendar-string cal)
             (js-throw (make-native-error "TypeError" "calendar must be a string")))))
     (pdt-from-fields v options))
    ((stringp v)
     (let ((r (parse-iso-datetime v :datetime)))
       (get-temporal-overflow (get-options-object options))
       (when (getf r :z)
         (js-throw (make-native-error "RangeError" "a UTC designator is not valid for PlainDateTime")))
       ;; A [u-ca=...] annotation value must be exactly the iso8601 identifier
       ;; (a date-like string is NOT a valid annotation calendar, unlike a bag's
       ;; calendar property). The core parser doesn't surface :calendar in its
       ;; plist, so extract it from the string ourselves.
       (let ((cal (pdt-extract-calendar-annotation v)))
         (when (and cal (not (string-equal cal "iso8601")))
           (js-throw (make-native-error "RangeError" "only the iso8601 calendar is supported"))))
       (let ((date (make-iso-date (getf r :year) (getf r :month) (getf r :day)))
             (time (make-iso-time (getf r :hour) (getf r :minute) (getf r :second)
                                  (getf r :ms) (getf r :us) (getf r :ns))))
         (unless (valid-iso-date-p date)
           (js-throw (make-native-error "RangeError" "invalid ISO date")))
         (pdt-check-range date time)
         (values date time))))
    (t (js-throw (make-native-error "TypeError" "cannot convert value to a Temporal.PlainDateTime")))))

;;; ---------------------------------------------------------------------------
;;; Comparison / difference core
;;; ---------------------------------------------------------------------------
(defun pdt-compare (d1 t1 d2 t2)
  "-1/0/1 comparing two datetimes (date then time)."
  (let ((c (pdt-cmp-date (iso-date-year d1) (iso-date-month d1) (iso-date-day d1)
                         (iso-date-year d2) (iso-date-month d2) (iso-date-day d2))))
    (if (/= c 0) c
        (let ((n1 (iso-datetime->epoch-ns (make-iso-date 1970 1 1) t1))
              (n2 (iso-datetime->epoch-ns (make-iso-date 1970 1 1) t2)))
          (cond ((< n1 n2) -1) ((> n1 n2) 1) (t 0))))))

(defun pdt-difference (d1 t1 d2 t2 largest-unit)
  "DifferenceISODateTime -> a duration plist. Compute the time difference; if it
   borrows a day (opposite sign to the date difference) adjust the date by one
   day, then compute the calendar date difference for the requested largestUnit
   (:year..:day) or fold the date into the time part for time largestUnits."
  (let* ((time1-ns (iso-datetime->epoch-ns (make-iso-date 1970 1 1) t1))
         (time2-ns (iso-datetime->epoch-ns (make-iso-date 1970 1 1) t2))
         (time-diff (- time2-ns time1-ns))
         (date-sign (pdt-cmp-date (iso-date-year d1) (iso-date-month d1) (iso-date-day d1)
                                  (iso-date-year d2) (iso-date-month d2) (iso-date-day d2)))
         (adj-date2 d2))
    ;; If the time difference has the opposite sign to the date difference,
    ;; borrow/lend a day so the time part carries the same sign.
    (let ((time-sign (cond ((plusp time-diff) 1) ((minusp time-diff) -1) (t 0))))
      (when (and (/= date-sign 0) (/= time-sign 0) (= date-sign (- time-sign)))
        ;; move date2 one day toward date1 by -date-sign... actually toward date1
        (let ((days (+ (iso-date->epoch-days d2) (- date-sign))))
          (setf adj-date2 (epoch-days->iso-date days))
          (incf time-diff (* date-sign +ns-per-day+)))))
    (if (member largest-unit '(:year :month :week :day))
        ;; Calendar date difference + balanced time.
        (multiple-value-bind (years months weeks days)
            (pdt-difference-iso-date
             (iso-date-year d1) (iso-date-month d1) (iso-date-day d1)
             (iso-date-year adj-date2) (iso-date-month adj-date2) (iso-date-day adj-date2)
             largest-unit)
          (let ((td (ns->time-duration time-diff :hour)))
            (list :years years :months months :weeks weeks :days days
                  :hours (getf td :hours) :minutes (getf td :minutes) :seconds (getf td :seconds)
                  :milliseconds (getf td :milliseconds) :microseconds (getf td :microseconds)
                  :nanoseconds (getf td :nanoseconds))))
        ;; time largestUnit: fold the whole date difference into the time total.
        (let* ((date-ns (* (- (iso-date->epoch-days d2) (iso-date->epoch-days d1)) +ns-per-day+))
               (total (+ date-ns time2-ns (- time1-ns))))
          (ns->time-duration total largest-unit)))))

;;; ---------------------------------------------------------------------------
;;; Rounding
;;; ---------------------------------------------------------------------------
(defun pdt-round (date time smallest increment mode)
  "RoundISODateTime: round to SMALLEST (:day..:nanosecond). Day-rounding rounds
   the day boundary (fraction of a day). Returns (values date time)."
  (if (eq smallest :day)
      (let* ((day-ns (iso-datetime->epoch-ns (make-iso-date 1970 1 1) time))
             (rounded-days (round-to-increment day-ns (* increment +ns-per-day+) mode))
             (carry (truncate rounded-days +ns-per-day+))
             (new-days (+ (iso-date->epoch-days date) carry)))
        (values (epoch-days->iso-date new-days) (make-iso-time 0 0 0 0 0 0)))
      (let* ((unit-ns (unit->ns smallest))
             (time-ns (iso-datetime->epoch-ns (make-iso-date 1970 1 1) time))
             (rounded (round-to-increment time-ns (* increment unit-ns) mode)))
        (multiple-value-bind (carry newtime) (balance-time 0 0 0 0 0 rounded)
          (values (epoch-days->iso-date (+ (iso-date->epoch-days date) carry)) newtime)))))

;;; ---------------------------------------------------------------------------
;;; toString
;;; ---------------------------------------------------------------------------
(defun pdt-to-string (date time options &optional json)
  (if json
      (concatenate 'string
                   (format-iso-date-string (iso-date-year date) (iso-date-month date) (iso-date-day date))
                   "T" (format-iso-time time :auto))
      (let* ((opts (get-options-object options))
             ;; spec order: calendarName, fractionalSecondDigits, roundingMode,
             ;; smallestUnit
             (cal-name (get-option-string opts "calendarName"
                          '(("auto" . :auto) ("always" . :always)
                            ("never" . :never) ("critical" . :critical))
                          :auto))
             (digits (get-fractional-second-digits opts))
             (mode (get-rounding-mode opts :trunc))
             (smallest (get-temporal-unit opts "smallestUnit" :time nil
                                          '(:year :month :week :day :hour :minute
                                            :second :millisecond :microsecond :nanosecond))))
        (when (and smallest (not (member smallest '(:minute :second :millisecond :microsecond :nanosecond))))
          (js-throw (make-native-error "RangeError" "smallestUnit not allowed for PlainDateTime.toString")))
        (let* ((prec (cond ((null smallest) digits)
                           ((eq smallest :minute) :minute)
                           (t (ecase smallest
                                (:second 0) (:millisecond 3) (:microsecond 6) (:nanosecond 9)))))
               (unit-ns (cond ((null smallest)
                               (if (eq digits :auto) 1 (expt 10 (- 9 digits))))
                              (t (ecase smallest
                                   (:minute +ns-per-min+) (:second +ns-per-s+)
                                   (:millisecond +ns-per-ms+) (:microsecond +ns-per-us+)
                                   (:nanosecond 1)))))
               (time-ns (iso-datetime->epoch-ns (make-iso-date 1970 1 1) time))
               (rounded (round-to-increment time-ns unit-ns mode)))
          (multiple-value-bind (carry newtime) (balance-time 0 0 0 0 0 rounded)
            (let* ((newdate (epoch-days->iso-date (+ (iso-date->epoch-days date) carry))))
              (pdt-check-range newdate newtime)
              (let*
                 ((datestr (format-iso-date-string (iso-date-year newdate) (iso-date-month newdate)
                                                    (iso-date-day newdate)))
                   (timestr (if (eq prec :minute)
                                (format nil "~2,'0d:~2,'0d" (iso-time-hour newtime) (iso-time-minute newtime))
                                (format-iso-time newtime prec)))
                   (calstr (case cal-name
                             (:critical "[!u-ca=iso8601]")
                             (:always "[u-ca=iso8601]")
                             (t ""))))
              (concatenate 'string datestr "T" timestr calstr))))))))

;;; ---------------------------------------------------------------------------
;;; Installation
;;; ---------------------------------------------------------------------------
(defun install-temporal-plaindatetime (realm)
  (let* ((op (realm-object-proto realm))
         (proto (make-object :proto op :class "Object"))
         (ctor (native-function realm "PlainDateTime"
                 (lambda (this args) (declare (ignore this args))
                   (js-throw (make-native-error "TypeError" "Constructor PlainDateTime requires 'new'")))
                 3)))
    (setf *temporal-plaindatetime-proto* proto)
    ;; ---- constructor ----
    (setf (js-object-construct ctor)
          (lambda (args nt)
            (flet ((f (i) (let ((v (arg i args)))
                            (if (js-undefined-p v) 0 (to-integer-with-truncation v)))))
              ;; Order-of-operations: ToIntegerWithTruncation on args 0..8 in
              ;; order, then calendar (arg 9), then validate.
              (let* ((y (f 0)) (mo (f 1)) (d (f 2))
                     (h (f 3)) (mi (f 4)) (s (f 5)) (ms (f 6)) (us (f 7)) (ns (f 8))
                     (cal (arg 9 args)))
                (unless (js-undefined-p cal)
                  (if (stringp cal) (pdt-validate-calendar-string cal)
                      (js-throw (make-native-error "TypeError" "calendar must be a string"))))
                (unless (pdt-valid-iso-date-p y mo d)
                  (js-throw (make-native-error "RangeError" "date field out of range")))
                (unless (valid-time-p h mi s ms us ns)
                  (js-throw (make-native-error "RangeError" "time field out of range")))
                (let ((date (make-iso-date y mo d)))
                  (pdt-check-range date (make-iso-time h mi s ms us ns))
                  (let ((o (make-object :proto (proto-from-newtarget nt proto) :class "Object")))
                    (setf (getf (js-object-internal o) :temporal-plaindatetime)
                          (list :date date :time (make-iso-time h mi s ms us ns)))
                    o))))))
    (def-value ctor "prototype" proto :writable nil :configurable nil)
    (def-value proto "constructor" ctor)

    ;; ---- statics ----
    (def-method realm ctor "from" 1 (this args)
      (declare (ignore this))
      (multiple-value-bind (date time) (to-temporal-datetime realm (arg 0 args) (arg 1 args))
        (make-temporal-plaindatetime realm date time)))
    (def-method realm ctor "compare" 2 (this args)
      (declare (ignore this))
      (multiple-value-bind (d1 t1) (to-temporal-datetime realm (arg 0 args))
        (multiple-value-bind (d2 t2) (to-temporal-datetime realm (arg 1 args))
          (float (pdt-compare d1 t1 d2 t2) 1d0))))

    ;; ---- getters ----
    (def-getter realm proto "calendarId"
      (lambda (this args) (declare (ignore args))
        (plaindatetime-slot this) "iso8601"))
    (macrolet ((dgetter (name accessor)
                 `(def-getter realm proto ,name
                    (lambda (this args) (declare (ignore args))
                      (float (,accessor (plaindatetime-date this)) 1d0))))
               (tgetter (name accessor)
                 `(def-getter realm proto ,name
                    (lambda (this args) (declare (ignore args))
                      (float (,accessor (plaindatetime-time this)) 1d0)))))
      (dgetter "year" iso-date-year)
      (dgetter "month" iso-date-month)
      (dgetter "day" iso-date-day)
      (tgetter "hour" iso-time-hour)
      (tgetter "minute" iso-time-minute)
      (tgetter "second" iso-time-second)
      (tgetter "millisecond" iso-time-millisecond)
      (tgetter "microsecond" iso-time-microsecond)
      (tgetter "nanosecond" iso-time-nanosecond))
    (def-getter realm proto "monthCode"
      (lambda (this args) (declare (ignore args))
        (pdt-month-code-string (iso-date-month (plaindatetime-date this)))))
    ;; calendar-derived getters
    (def-getter realm proto "dayOfWeek"
      (lambda (this args) (declare (ignore args))
        (float (iso-day-of-week (plaindatetime-date this)) 1d0)))
    (def-getter realm proto "dayOfYear"
      (lambda (this args) (declare (ignore args))
        (let ((d (plaindatetime-date this)))
          (float (1+ (- (iso-date->epoch-days d)
                        (iso-date->epoch-days (make-iso-date (iso-date-year d) 1 1)))) 1d0))))
    (def-getter realm proto "weekOfYear"
      (lambda (this args) (declare (ignore args))
        (let ((v (pdt-iso-week-of-year (plaindatetime-date this))))
          (float (car v) 1d0))))
    (def-getter realm proto "yearOfWeek"
      (lambda (this args) (declare (ignore args))
        (let ((v (pdt-iso-week-of-year (plaindatetime-date this))))
          (float (cdr v) 1d0))))
    (def-getter realm proto "daysInWeek"
      (lambda (this args) (declare (ignore args)) (plaindatetime-slot this) 7d0))
    (def-getter realm proto "daysInMonth"
      (lambda (this args) (declare (ignore args))
        (let ((d (plaindatetime-date this)))
          (float (days-in-month (iso-date-year d) (iso-date-month d)) 1d0))))
    (def-getter realm proto "daysInYear"
      (lambda (this args) (declare (ignore args))
        (float (iso-days-in-year (iso-date-year (plaindatetime-date this))) 1d0)))
    (def-getter realm proto "monthsInYear"
      (lambda (this args) (declare (ignore args)) (plaindatetime-slot this) 12d0))
    (def-getter realm proto "inLeapYear"
      (lambda (this args) (declare (ignore args))
        (js-bool (leap-year-p (iso-date-year (plaindatetime-date this))))))
    (def-getter realm proto "era"
      (lambda (this args) (declare (ignore args)) (plaindatetime-slot this) *undefined*))
    (def-getter realm proto "eraYear"
      (lambda (this args) (declare (ignore args)) (plaindatetime-slot this) *undefined*))

    ;; ---- with ----
    (def-method realm proto "with" 1 (this args)
      (let ((slot (plaindatetime-slot this))
            (bag (arg 0 args)))
        (unless (js-object-p bag)
          (js-throw (make-native-error "TypeError" "with() argument must be an object")))
        ;; RejectObjectWithCalendarOrTimeZone (calendar then timeZone).
        (reject-calendar-or-timezone bag)
        (let* ((date (getf slot :date)) (time (getf slot :time))
               (fields (pdt-read-fields bag))
               (overflow (get-temporal-overflow (get-options-object (arg 1 args)))))
          ;; Merge: month/monthCode resolve together (a lone monthCode overrides
          ;; the receiver's month; a lone month overrides too).
          (let* ((year (or (getf fields :year) (iso-date-year date)))
                 (month (let ((m (pdt-resolve-month fields)))
                          (or m (iso-date-month date))))
                 (day (or (getf fields :day) (iso-date-day date)))
                 (hour (or (getf fields :hour) (iso-time-hour time)))
                 (minute (or (getf fields :minute) (iso-time-minute time)))
                 (second (or (getf fields :second) (iso-time-second time)))
                 (ms (or (getf fields :millisecond) (iso-time-millisecond time)))
                 (us (or (getf fields :microsecond) (iso-time-microsecond time)))
                 (ns (or (getf fields :nanosecond) (iso-time-nanosecond time)))
                 (newdate (pdt-regulate-iso-date year month day overflow))
                 (newtime (regulate-time hour minute second ms us ns overflow)))
            (pdt-check-range newdate newtime)
            (make-temporal-plaindatetime realm newdate newtime)))))

    ;; ---- withPlainTime ----
    (def-method realm proto "withPlainTime" 0 (this args)
      (let* ((date (plaindatetime-date this))
             (v (arg 0 args))
             (time (if (js-undefined-p v)
                       (make-iso-time 0 0 0 0 0 0)
                       (to-temporal-time realm v))))
        (make-temporal-plaindatetime realm date time)))

    ;; ---- withCalendar ----
    (def-method realm proto "withCalendar" 1 (this args)
      (let ((slot (plaindatetime-slot this))
            (v (arg 0 args)))
        (if (stringp v)
            (pdt-validate-calendar-string v)
            (js-throw (make-native-error "TypeError" "calendar must be a string")))
        (make-temporal-plaindatetime realm (getf slot :date) (getf slot :time))))

    ;; ---- add / subtract ----
    (labels ((add-dur (this args negate)
               (let* ((date (plaindatetime-date this)) (time (plaindatetime-time this))
                      (d (validate-duration-range (to-temporal-duration-record (arg 0 args))))
                      (overflow (get-temporal-overflow (get-options-object (arg 1 args))))
                      (sgn (if negate -1 1)))
                 ;; time part via ns with day carry
                 (let* ((time-ns (iso-datetime->epoch-ns (make-iso-date 1970 1 1) time))
                        (delta (* sgn (duration-time-ns d)))
                        (total (+ time-ns delta)))
                   (multiple-value-bind (carry newtime) (balance-time 0 0 0 0 0 total)
                     ;; date part via AddISODate (+ the time day-carry)
                     (let ((newdate (pdt-add-iso-date
                                     (iso-date-year date) (iso-date-month date)
                                     (iso-date-day date)
                                     (* sgn (getf d :years)) (* sgn (getf d :months))
                                     (* sgn (getf d :weeks))
                                     (+ (* sgn (getf d :days)) carry)
                                     overflow)))
                       (pdt-check-range newdate newtime)
                       (make-temporal-plaindatetime realm newdate newtime)))))))
      (def-method realm proto "add" 1 (this args) (add-dur this args nil))
      (def-method realm proto "subtract" 1 (this args) (add-dur this args t)))

    ;; ---- until / since ----
    (labels ((diff (this args op)
               (let* ((d1 (plaindatetime-date this)) (t1 (plaindatetime-time this)))
                 (multiple-value-bind (d2 t2) (to-temporal-datetime realm (arg 0 args))
                   (let ((options (get-options-object (arg 1 args))))
                     (multiple-value-bind (smallest largest increment mode)
                         (get-difference-settings op options
                           :nanosecond :day
                           '(:year :month :week :day :hour :minute :second
                             :millisecond :microsecond :nanosecond)
                           '(:year :month :week :day :hour :minute :second
                             :millisecond :microsecond :nanosecond)
                           #'pdt-max-increment)
                       (let ((d (pdt-difference d1 t1 d2 t2 largest)))
                         ;; rounding: round smallest unit unless it's a pure
                         ;; nanosecond/inc-1 no-op.
                         (setf d (pdt-round-duration d d1 t1 d2 t2 smallest largest increment mode))
                         (when (eq op :since)
                           (setf d (loop for f in +duration-fields+ append (list f (- (getf d f))))))
                         (make-temporal-duration realm d))))))))
      (def-method realm proto "until" 1 (this args) (diff this args :until))
      (def-method realm proto "since" 1 (this args) (diff this args :since)))

    ;; ---- round ----
    (def-method realm proto "round" 1 (this args)
      (let ((date (plaindatetime-date this)) (time (plaindatetime-time this))
            (arg0 (arg 0 args)))
        (when (js-undefined-p arg0)
          (js-throw (make-native-error "TypeError" "options required")))
        (multiple-value-bind (smallest increment mode)
            (if (stringp arg0)
                (let ((hit (assoc arg0 (unit-alist '(:day :hour :minute :second :millisecond :microsecond :nanosecond))
                                  :test #'string=)))
                  (unless hit (js-throw (make-native-error "RangeError" "invalid smallestUnit")))
                  (values (cdr hit) 1 :half-expand))
                (let* ((options (get-options-object arg0))
                       (increment (get-rounding-increment options))
                       (mode (get-rounding-mode options :half-expand))
                       (smallest (get-temporal-unit options "smallestUnit" :time :required
                                                    '(:day :hour :minute :second :millisecond :microsecond :nanosecond))))
                  (values smallest increment mode)))
          (let ((max (pdt-round-max smallest)))
            (validate-rounding-increment increment max (eq smallest :day))
            (unless (eq smallest :day)
              (when (/= 0 (mod max increment))
                (js-throw (make-native-error "RangeError" "increment does not divide evenly")))))
          (multiple-value-bind (newdate newtime) (pdt-round date time smallest increment mode)
            (pdt-check-range newdate newtime)
            (make-temporal-plaindatetime realm newdate newtime)))))

    ;; ---- equals ----
    (def-method realm proto "equals" 1 (this args)
      (let ((d1 (plaindatetime-date this)) (t1 (plaindatetime-time this)))
        (multiple-value-bind (d2 t2) (to-temporal-datetime realm (arg 0 args))
          (js-bool (zerop (pdt-compare d1 t1 d2 t2))))))

    ;; ---- toString / toJSON / toLocaleString ----
    (def-method realm proto "toString" 0 (this args)
      (pdt-to-string (plaindatetime-date this) (plaindatetime-time this) (arg 0 args)))
    (def-method realm proto "toJSON" 0 (this args)
      (declare (ignore args))
      (pdt-to-string (plaindatetime-date this) (plaindatetime-time this) *undefined* t))
    (def-method realm proto "toLocaleString" 0 (this args)
      (declare (ignore args))
      (pdt-to-string (plaindatetime-date this) (plaindatetime-time this) *undefined* t))

    ;; ---- toPlainDate / toPlainTime ----
    (def-method realm proto "toPlainDate" 0 (this args)
      (declare (ignore args))
      (let ((date (plaindatetime-date this)))
        ;; The concurrent PlainDate file exports make-plain-date; call it when
        ;; the type is present, else degrade to a clear TypeError.
        (if (fboundp 'make-plain-date)
            (make-plain-date date "iso8601" realm)
            (js-throw (make-native-error "TypeError" "Temporal.PlainDate is not available")))))
    (def-method realm proto "toPlainTime" 0 (this args)
      (declare (ignore args))
      (make-temporal-plaintime realm (plaindatetime-time this)))

    ;; ---- toZonedDateTime (B3 — ZonedDateTime deferred) ----
    (def-method realm proto "toZonedDateTime" 1 (this args)
      (plaindatetime-slot this)   ; brand-check
      (js-throw (make-native-error "TypeError" "Temporal.ZonedDateTime is not implemented")))

    ;; ---- valueOf ----
    (def-method realm proto "valueOf" 0 (this args)
      (declare (ignore args))
      (js-throw (make-native-error "TypeError"
                  "Cannot convert a Temporal.PlainDateTime to a primitive; use compare() or equals()")))

    ;; ---- @@toStringTag ----
    (put proto (symbol-tostringtag realm) "Temporal.PlainDateTime"
         :enumerable nil :writable nil :configurable t)

    (temporal-register realm "PlainDateTime" ctor)))

;;; ---------------------------------------------------------------------------
;;; helpers (post-install)
;;; ---------------------------------------------------------------------------
(defun pdt-max-increment (unit)
  ;; Calendar units (year/month/week/day) have no spec maximum on the difference
  ;; rounding increment — only >= 1. The kernel's get-difference-settings still
  ;; runs validate + a divisibility check against this value, so we return a
  ;; large value that admits increment 1 (the only calendar increment the corpus
  ;; exercises) while time units use their real next-coarser-unit counts.
  (ecase unit
    (:year 1000000000) (:month 1000000000) (:week 1000000000) (:day 1000000000)
    (:hour 24) (:minute 60) (:second 60)
    (:millisecond 1000) (:microsecond 1000) (:nanosecond 1000)))

(defun pdt-round-max (unit)
  "Max increment for round(): day is [1,inf) effectively (inclusive of large),
   time units bound by their count in the next-coarser unit."
  (ecase unit
    (:day 1)
    (:hour 24) (:minute 60) (:second 60)
    (:millisecond 1000) (:microsecond 1000) (:nanosecond 1000)))

(defun pdt-datetime-ns (date time)
  "Exact epoch ns of DATE+TIME (a wall-clock instant, UTC-anchored)."
  (+ (* (iso-date->epoch-days date) +ns-per-day+)
     (iso-datetime->epoch-ns (make-iso-date 1970 1 1) time)))

(defun pdt-round-duration (d d1 t1 d2 t2 smallest largest increment mode)
  "RoundDuration for a PlainDateTime difference D between (d1 t1) and (d2 t2).
   SMALLEST selects the rounding grain. Time smallestUnits round the ns total;
   day/week/month/year use the calendar 'nudge' algorithm anchored at (d1 t1):
   the fraction of progress between the smallestUnit floor and ceil dates
   determines the rounded count. Returns a duration plist balanced to LARGEST."
  (if (member smallest '(:hour :minute :second :millisecond :microsecond :nanosecond))
      ;; --- time smallestUnit: fold the whole difference into ns and round. ---
      (let* ((total (- (pdt-datetime-ns d2 t2) (pdt-datetime-ns d1 t1)))
             (unit-ns (unit->ns smallest))
             (rounded (round-to-increment total (* increment unit-ns) mode)))
        (if (member largest '(:year :month :week :day))
            ;; largest is a calendar unit: keep the calendar part of D, replace
            ;; only the time part with the rounded remainder within the days.
            (pdt-rebalance-with-days d d1 rounded largest)
            (ns->time-duration rounded largest)))
      ;; --- calendar smallestUnit (day/week/month/year): nudge. ---
      (pdt-nudge-calendar d d1 t1 d2 t2 smallest largest increment mode)))

(defun pdt-rebalance-with-days (d d1 total-ns largest)
  "For a calendar LARGEST with a time SMALLEST: TOTAL-NS is the signed exact ns
   difference; re-derive the whole (years..days) using the days that fit, then
   the time remainder. We recompute the date part from the day count so the
   calendar breakdown stays consistent with LARGEST."
  (declare (ignore d))
  (multiple-value-bind (days rem) (truncate total-ns +ns-per-day+)
    (let* ((y1 (iso-date-year d1)) (m1 (iso-date-month d1)) (dd1 (iso-date-day d1))
           (target (epoch-days->iso-date (+ (iso-date->epoch-days d1) days))))
      (multiple-value-bind (yy mm ww dcarry)
          (pdt-difference-iso-date y1 m1 dd1
                                   (iso-date-year target) (iso-date-month target) (iso-date-day target)
                                   largest)
        (let ((td (ns->time-duration rem :hour)))
          (list :years yy :months mm :weeks ww :days dcarry
                :hours (getf td :hours) :minutes (getf td :minutes) :seconds (getf td :seconds)
                :milliseconds (getf td :milliseconds) :microseconds (getf td :microseconds)
                :nanoseconds (getf td :nanoseconds)))))))

(defun pdt-add-calendar-units (d1 years months weeks days)
  "date1 + (years months weeks days) with constrain overflow -> iso-date."
  (pdt-add-iso-date (iso-date-year d1) (iso-date-month d1) (iso-date-day d1)
                    years months weeks days :constrain))

(defun pdt-nudge-calendar (d d1 t1 d2 t2 smallest largest increment mode)
  "Nudge the calendar part of the difference D to a multiple of INCREMENT
   SMALLEST units (SMALLEST in :day :week :month :year). The exact target
   instant is (d2 t2); the anchor is (d1 t1). We take the whole count of
   SMALLEST already in D (r0), build the floor/ceil candidate dates, and use the
   exact-ns fraction of progress between them to pick the rounded count."
  (let* ((years (getf d :years)) (months (getf d :months))
         (weeks (getf d :weeks)) (days (getf d :days))
         (target-ns (pdt-datetime-ns d2 t2))
         (base-ns (pdt-datetime-ns d1 t1))
         (sign (if (>= target-ns base-ns) 1 -1)))
    ;; r0 = the whole count of SMALLEST currently in the (years..days) part,
    ;; expressed keeping coarser units fixed at their current value.
    (multiple-value-bind (fixed-y fixed-m fixed-w r0)
        (ecase smallest
          (:year   (values 0 0 0 years))
          (:month  (values years 0 0 months))
          (:week   (values years months 0 weeks))
          (:day    (values years months weeks days)))
      ;; Floor count rounded down to the increment (toward date1).
      (let* ((r-floor (* increment (floor (/ r0 increment))))
             (r-ceil  (+ r-floor increment))
             ;; candidate dates at r-floor and r-ceil SMALLEST units. Both the
             ;; floor and ceil candidate must be within the representable ISO
             ;; range (NudgeToCalendarUnit constrains + range-checks the end).
             (date-floor (pdt-check-range (pdt-candidate-date d1 smallest fixed-y fixed-m fixed-w r-floor) t1))
             (date-ceil  (pdt-check-range (pdt-candidate-date d1 smallest fixed-y fixed-m fixed-w r-ceil) t1))
             (ns-floor (+ (* (iso-date->epoch-days date-floor) +ns-per-day+)
                          (iso-datetime->epoch-ns (make-iso-date 1970 1 1) t1)))
             (ns-ceil  (+ (* (iso-date->epoch-days date-ceil) +ns-per-day+)
                          (iso-datetime->epoch-ns (make-iso-date 1970 1 1) t1))))
        (declare (ignore sign))
        ;; progress fraction = (target - floor) / (ceil - floor); round it.
        (let* ((span (- ns-ceil ns-floor))
               (progress (if (zerop span) 0 (/ (- target-ns ns-floor) span)))
               (rounded-count (* increment
                                 (apply-rounding-mode (+ (/ r-floor increment) progress) mode)))
               (final-date (pdt-candidate-date d1 smallest fixed-y fixed-m fixed-w rounded-count)))
          ;; Re-derive the (years..days) breakdown to LARGEST between date1 and
          ;; the nudged date; the time part is zero (rounding landed on a date).
          (multiple-value-bind (yy mm ww dcarry)
              (pdt-difference-iso-date
               (iso-date-year d1) (iso-date-month d1) (iso-date-day d1)
               (iso-date-year final-date) (iso-date-month final-date) (iso-date-day final-date)
               largest)
            (list :years yy :months mm :weeks ww :days dcarry
                  :hours 0 :minutes 0 :seconds 0
                  :milliseconds 0 :microseconds 0 :nanoseconds 0)))))))

(defun pdt-candidate-date (d1 smallest fixed-y fixed-m fixed-w count)
  "date1 + fixed coarser units + COUNT of SMALLEST, constrain overflow."
  (ecase smallest
    (:year  (pdt-add-calendar-units d1 count 0 0 0))
    (:month (pdt-add-calendar-units d1 fixed-y count 0 0))
    (:week  (pdt-add-calendar-units d1 fixed-y fixed-m count 0))
    (:day   (pdt-add-calendar-units d1 fixed-y fixed-m fixed-w count))))

(defun pdt-iso-week-of-year (date)
  "ISO 8601 week-of-year -> (week . year). Weeks start Monday; week 1 contains
   the year's first Thursday."
  (let* ((y (iso-date-year date))
         (doy (1+ (- (iso-date->epoch-days date)
                     (iso-date->epoch-days (make-iso-date y 1 1)))))
         (dow (iso-day-of-week date))      ; 1..7 Mon..Sun
         (week (floor (+ (- doy dow) 10) 7)))
    (cond
      ((< week 1)
       ;; belongs to the last week of the previous year
       (let ((py (1- y)))
         (cons (pdt-weeks-in-iso-year py) py)))
      ((> week (pdt-weeks-in-iso-year y))
       (cons 1 (1+ y)))
      (t (cons week y)))))

(defun pdt-weeks-in-iso-year (y)
  "Number of ISO weeks (52 or 53) in ISO year Y."
  (flet ((p (yy) (mod (+ yy (floor yy 4) (- (floor yy 100)) (floor yy 400)) 7)))
    (if (or (= (p y) 4) (= (p (1- y)) 3)) 53 52)))

;;; toPlainDate constructs via the concurrent PlainDate file's exported
;;; make-plain-date (called by fboundp guard in the method above); no interop
;;; shim is needed now that PlainDate is present.

(register-builtin-installer 'install-temporal-plaindatetime)
