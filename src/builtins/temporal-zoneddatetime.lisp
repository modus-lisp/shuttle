;;;; builtins/temporal-zoneddatetime.lisp — Temporal.ZonedDateTime.
;;;;
;;;; A ZonedDateTime is an exact instant (epoch nanoseconds, a CL integer) paired
;;;; with a time-zone identifier string and a calendar id ("iso8601"). The corpus
;;;; only exercises "UTC" and fixed-offset zones (±HH:MM, minute precision as an
;;;; identifier), so a time zone is fully described by a single offset-ns integer.
;;;;
;;;; The internal slot :temporal-zoneddatetime holds a plist
;;;;   (:ns epoch-ns :timezone canonical-id-string :offset offset-ns)
;;;; plus :temporal-calendar = "iso8601" (the sibling ToTemporalDate/Time helpers
;;;; read (:ns ...) off this slot — keep that shape).
(in-package #:shuttle)

(defvar *temporal-zoneddatetime-proto* nil)

;;; ===========================================================================
;;; Time-zone identifiers (UTC + fixed offsets only)
;;; ===========================================================================
(defun format-offset-id (ns)
  "FormatOffsetTimeZoneIdentifier: canonical +HH:MM (or +HH:MM:SS[.fff] for a
   sub-minute offset — never produced as an *identifier* here, but used for the
   offset string). Minute-precision identifiers canonicalize to +HH:MM."
  (format-offset-ns ns))

(defun parse-time-zone-identifier (s)
  "ToTemporalTimeZoneIdentifier for the corpus's zones. Accepts:
     - \"UTC\" (any case)                     -> (values \"UTC\" 0)
     - a bare minute-precision offset         -> (values \"+HH:MM\" offset-ns)
     - an ISO date-time string whose bracket [Zone] annotation names one of the
       above, OR (no annotation) whose Z/numeric-offset gives the zone.
   A sub-minute offset is NOT a valid identifier (RangeError). A bare date-time
   with no offset/Z/annotation is not a time zone (RangeError). Non-string input
   is handled by the caller (TypeError)."
  (when (string-equal s "UTC") (return-from parse-time-zone-identifier (values "UTC" 0)))
  ;; bare offset?
  (multiple-value-bind (off nx sub) (parse-offset-string s 0 (length s))
    (when (and off (= nx (length s)))
      (when sub
        (js-throw (make-native-error "RangeError" "sub-minute offset is not a valid time zone")))
      (return-from parse-time-zone-identifier (values (format-offset-id off) off))))
  ;; ISO string form: an annotation [Zone] wins; else the numeric offset / Z.
  (let ((br (position #\[ s)))
    (if br
        ;; The full string must still be a valid Temporal date-time string
        ;; (year-zero, malformed date, etc. are rejected before the annotation is
        ;; honoured) — but only when there IS a date-time part before the bracket.
        ;; A bare "[Zone]" (bracket at position 0) is the annotation alone.
        (progn
          (when (plusp br)
            (parse-iso-datetime (string-trim '(#\Space) s) :datetime))
          (let ((rb (position #\] s :start br)))
            (unless rb (js-throw (make-native-error "RangeError" "invalid time zone")))
            (let ((ann (subseq s (1+ br) rb)))
              (when (and (plusp (length ann)) (char= (char ann 0) #\!)) (setf ann (subseq ann 1)))
              ;; The annotation names the zone; parse it recursively (it must itself
              ;; be UTC or a minute-precision offset).
              (parse-time-zone-identifier ann))))
        ;; No annotation: parse as a datetime, use its offset (Z => UTC).
        (let ((r (parse-iso-datetime (string-trim '(#\Space) s) :datetime)))
          (unless (getf r :offset-present)
            (js-throw (make-native-error "RangeError" "bare date-time is not a time zone")))
          (when (getf r :offset-sub-minute)
            (js-throw (make-native-error "RangeError" "sub-minute offset is not a valid time zone")))
          (if (getf r :z)
              (values "UTC" 0)
              (let ((off (getf r :offset)))
                (values (format-offset-id off) off)))))))

(defun parse-offset-value (s)
  "Parse an offset STRING from a property bag's `offset` field into offset-ns, or
   NIL when malformed. Stricter than parse-offset-string: a fractional part is
   only valid after a two-digit seconds group (guards against '+00:00.0')."
  (let ((dot (or (position #\. s) (position #\, s))))
    ;; A fractional part is only valid after a full SECONDS group: either the
    ;; extended form has TWO colons before it (±HH:MM:SS.f) or the basic form has
    ;; six offset digits before it (±HHMMSS.f). A fraction after only minutes
    ;; (e.g. '+00:00.0') is malformed.
    (when dot
      (let ((colons (count #\: s :end dot))
            (digits (count-if #'digit-char-p s :end dot)))
        (unless (or (= colons 2) (and (= colons 0) (= digits 6)))
          (return-from parse-offset-value nil)))))
  (multiple-value-bind (off nx) (parse-offset-string s 0 (length s))
    (when (and off (= nx (length s))) off)))

(defun to-time-zone-identifier (v)
  "ToTemporalTimeZoneIdentifier: a String is parsed; a Temporal.ZonedDateTime
   object supplies its own time zone (fast path, reads the internal slot).
   Returns (values canonical-id offset-ns). Any other value -> TypeError; an
   invalid string -> RangeError (raised by parse-time-zone-identifier)."
  (cond
    ((and (js-object-p v)
          (not (eq (getf (js-object-internal v) :temporal-zoneddatetime 'none) 'none)))
     (let ((s (getf (js-object-internal v) :temporal-zoneddatetime)))
       (values (getf s :timezone) (getf s :offset))))
    ((stringp v) (parse-time-zone-identifier v))
    (t (js-throw (make-native-error "TypeError" "time zone must be a string")))))

;;; ===========================================================================
;;; Instance creation + slot access
;;; ===========================================================================
(defun make-zoneddatetime (realm ns tz-id offset calendar &optional new-target)
  "CreateTemporalZonedDateTime. NS is a valid in-range epoch-ns integer; TZ-ID a
   canonical id string; OFFSET its offset-ns; CALENDAR an id string."
  (declare (ignore realm))
  (let* ((proto (proto-from-newtarget new-target *temporal-zoneddatetime-proto*))
         (o (make-object :proto proto :class "Object")))
    (setf (getf (js-object-internal o) :temporal-zoneddatetime)
          (list :ns ns :timezone tz-id :offset offset))
    (setf (getf (js-object-internal o) :temporal-calendar) calendar)
    o))

(defun zdt-canonicalize-calendar (v)
  "ToTemporalCalendarIdentifier that also honours the fast path for ALL
   temporal-branded objects (PlainDateTime stores its calendar implicitly as
   iso8601 without a :temporal-calendar slot). Reads the internal calendar slot
   if present; otherwise defers to the shared canonicalize-calendar-id."
  (if (and (js-object-p v)
           (or (getf (js-object-internal v) :temporal-plaindate)
               (getf (js-object-internal v) :temporal-plaindatetime)
               (getf (js-object-internal v) :temporal-plainmonthday)
               (getf (js-object-internal v) :temporal-plainyearmonth)
               (getf (js-object-internal v) :temporal-zoneddatetime)))
      (let ((c (getf (js-object-internal v) :temporal-calendar "iso8601")))
        (if (string-equal c "iso8601") "iso8601"
            (js-throw (make-native-error "RangeError" "unknown calendar"))))
      (canonicalize-calendar-id v)))

(defun zdt-slot (this)
  (temporal-slot this :temporal-zoneddatetime "Temporal.ZonedDateTime"))
(defun zdt-ns (this) (getf (zdt-slot this) :ns))
(defun zdt-tz (this) (getf (zdt-slot this) :timezone))
(defun zdt-offset (this) (getf (zdt-slot this) :offset))
(defun zdt-calendar (this)
  (zdt-slot this)
  (getf (js-object-internal this) :temporal-calendar "iso8601"))

(defun zoneddatetime-p (v)
  (and (js-object-p v)
       (not (eq (getf (js-object-internal v) :temporal-zoneddatetime 'none) 'none))))

(defun zdt-local-datetime (this)
  "The local (wall-clock) ISO date + time for THIS, applying the zone offset.
   Returns (values iso-date iso-time)."
  (epoch-ns->iso-datetime (+ (zdt-ns this) (zdt-offset this))))

;;; ===========================================================================
;;; ToTemporalZonedDateTime (from bag / string / instance)
;;; ===========================================================================
(defun get-offset-option (options)
  "ToTemporalOffset: 'prefer' | 'use' | 'ignore' | 'reject' (default reject)."
  (get-option-string options "offset"
                     '(("prefer" . :prefer) ("use" . :use)
                       ("ignore" . :ignore) ("reject" . :reject))
                     :reject))

(defun get-disambiguation-option (options)
  "ToTemporalDisambiguation: 'compatible' (default) | 'earlier' | 'later' |
   'reject'. For fixed-offset zones there are no gaps/overlaps, so the value is
   read (observable) but does not change the result."
  (get-option-string options "disambiguation"
                     '(("compatible" . :compatible) ("earlier" . :earlier)
                       ("later" . :later) ("reject" . :reject))
                     :compatible))

(defun interpret-iso-datetime-offset (date time zone-offset provided-offset offset-behaviour offset-option)
  "InterpretISODateTimeOffset for a fixed-offset zone. Returns the epoch-ns.
   OFFSET-BEHAVIOUR is :wall (an offset value, if any, is a UTC offset to reconcile
   with the zone) or :exact (a Z designator — the local time is UTC and the
   instant is exact). PROVIDED-OFFSET is the parsed numeric offset (ns) or NIL."
  (let ((local-ns (iso-datetime->epoch-ns date time)))
    (flet ((wall ()
             ;; Deriving the instant from the zone offset goes through
             ;; GetPossibleEpochNanoseconds, which requires the wall-clock
             ;; datetime to be within the ISO datetime limits (the instant range
             ;; widened by one nanosecond-day at each end).
             (unless (<= (- +ns-min+ +ns-per-day+) local-ns (+ +ns-max+ +ns-per-day+))
               (js-throw (make-native-error "RangeError"
                           "wall-clock time is outside the representable range")))
             (- local-ns zone-offset)))
      (cond
        ;; Z present: the local time is already UTC (exact instant).
        ((eq offset-behaviour :exact)
         local-ns)
        ;; offset:ignore -> use the zone's offset, but WITHOUT the wall-clock
        ;; range restriction (only the resulting instant must be valid).
        ((eq offset-option :ignore)
         (- local-ns zone-offset))
        ;; offset:use -> honour the provided offset exactly (no wall-clock check).
        ((and provided-offset (eq offset-option :use))
         (- local-ns provided-offset))
        ;; No offset supplied -> the disambiguation path (zone offset, wall check).
        ((null provided-offset) (wall))
        ;; prefer/reject: the provided offset must match the zone offset (a fixed
        ;; zone allows only one). If it matches, use it; else prefer falls back to
        ;; the zone offset, reject throws. Either way the wall clock is computed.
        ((= provided-offset zone-offset) (wall))
        ((eq offset-option :prefer) (wall))
        (t (js-throw (make-native-error "RangeError"
                       "offset does not match the time zone")))))))

(defun read-zdt-bag-timezone (bag)
  "Read the required timeZone property off a property bag (TypeError if absent).
   Returns (values canonical-id offset-ns)."
  (let ((tz (js-get bag "timeZone")))
    (when (js-undefined-p tz)
      (js-throw (make-native-error "TypeError" "timeZone is required")))
    (to-time-zone-identifier tz)))

(defun to-temporal-zoneddatetime (realm v options)
  "ToTemporalZonedDateTime: a ZonedDateTime instance (options read), a property
   bag (calendar, date/time fields, timeZone, offset + option reads), or a string
   with a required [TimeZone] annotation. Returns a ZonedDateTime object."
  (cond
    ((zoneddatetime-p v)
     (let ((opts (get-options-object options)))
       (get-disambiguation-option opts)
       (get-offset-option opts)
       (get-temporal-overflow opts))
     (let ((s (getf (js-object-internal v) :temporal-zoneddatetime)))
       (make-zoneddatetime realm (getf s :ns) (getf s :timezone) (getf s :offset)
                           (getf (js-object-internal v) :temporal-calendar "iso8601"))))
    ((js-object-p v)
     ;; Property bag. Read order: calendar, then date/time fields (alphabetical),
     ;; then timeZone/offset, then options.
     (let* ((cal-v (js-get v "calendar"))
            (calendar (if (js-undefined-p cal-v) "iso8601" (zdt-canonicalize-calendar cal-v))))
       ;; Read the recognized fields alphabetically: the date/time fields, offset,
       ;; then timeZone (between "second" and "year"), then year.
       (multiple-value-bind (year month mc mc-leap mc-present day hour minute second ms us ns-frac
                             provided-offset offset-present tz-id zone-offset)
           (zdt-read-datetime-fields v t)
         ;; Options read AFTER the bag, in alphabetical key order:
         ;; disambiguation, offset, overflow.
         (let* ((opts (get-options-object options))
                (disamb (get-disambiguation-option opts))
                (offset-option (get-offset-option opts))
                (overflow (get-temporal-overflow opts)))
           (declare (ignore disamb))
           (let* ((resolved-month (zdt-resolve-month month mc mc-leap mc-present))
                  (date (create-iso-date-checked year resolved-month day overflow))
                  (time (regulate-time hour minute second ms us ns-frac overflow))
                  (ns (interpret-iso-datetime-offset
                       date time zone-offset
                       (if offset-present provided-offset nil)
                       :wall offset-option)))
             (unless (valid-epoch-ns-p ns)
               (js-throw (make-native-error "RangeError" "ZonedDateTime out of range")))
             (make-zoneddatetime realm ns tz-id zone-offset calendar))))))
    ((stringp v)
     (let* ((s (string-trim '(#\Space #\Tab #\Newline #\Return) v))
            (r (parse-iso-datetime s :datetime)))
       ;; A ZonedDateTime string REQUIRES a [TimeZone] annotation.
       (let ((br (position #\[ s)))
         (unless (and br
                      ;; the first bracket is a bare (time-zone) annotation, not
                      ;; a [u-ca=...] one.
                      (let ((rb (position #\] s :start br)))
                        (and rb
                             (let ((ann (subseq s (1+ br) rb)))
                               (when (and (plusp (length ann)) (char= (char ann 0) #\!))
                                 (setf ann (subseq ann 1)))
                               (null (position #\= ann))))))
           (js-throw (make-native-error "RangeError"
                       "a ZonedDateTime string requires a time zone annotation")))
         (multiple-value-bind (tz-id zone-offset)
             (parse-time-zone-identifier (subseq s br))
           (let* ((calendar (calendar-from-parse r s))
                  (date (make-iso-date (getf r :year) (getf r :month) (getf r :day)))
                  (time (make-iso-time (getf r :hour) (getf r :minute) (getf r :second)
                                       (getf r :ms) (getf r :us) (getf r :ns)))
                  (opts (get-options-object options)))
             (get-disambiguation-option opts)
             (let ((offset-option (get-offset-option opts)))
             (get-temporal-overflow opts)
             (unless (valid-iso-date-p date) (p-fail))
             (let* ((z (getf r :z))
                    (offset-present (getf r :offset-present))
                    (provided (getf r :offset))
                    ;; Z => exact instant; a numeric offset => the wall time is
                    ;; anchored at that offset (must agree per the offset option).
                    (ns (cond
                          (z ;; Z present: local time is UTC; apply offset option
                             ;; against the zone offset (prefer/reject check).
                           (interpret-iso-datetime-offset date time zone-offset 0
                                                          :exact offset-option))
                          (offset-present
                           (interpret-iso-datetime-offset date time zone-offset provided
                                                          :wall offset-option))
                          (t ;; no offset, only annotation: pure wall time.
                           (- (iso-datetime->epoch-ns date time) zone-offset)))))
               (unless (valid-epoch-ns-p ns)
                 (js-throw (make-native-error "RangeError" "ZonedDateTime out of range")))
               (make-zoneddatetime realm ns tz-id zone-offset calendar))))))))
    (t (js-throw (make-native-error "TypeError" "cannot convert value to a Temporal.ZonedDateTime")))))

(defun zdt-read-datetime-fields (bag &optional read-timezone)
  "Read the datetime fields + offset off a property bag for a ZonedDateTime.
   Read order is ALPHABETICAL over the recognized keys: day, hour, microsecond,
   millisecond, minute, month, monthCode, nanosecond, offset, second, timeZone,
   year. When READ-TIMEZONE is true the required timeZone property is read (in
   its alphabetical slot, before year). Year/month(-code)/day are required.
   Returns (values iso-date iso-time offset-ns offset-present tz-id zone-offset)."
  (let ((day nil) (hour 0) (us 0) (ms 0) (minute 0) (month nil)
        (mc nil) (mc-leap nil) (mc-present nil)
        (ns 0) (offset nil) (offset-present nil) (second 0) (year nil)
        (tz-id nil) (zone-offset 0))
    (flet ((rd-int (k) (let ((v (js-get bag k)))
                         (unless (js-undefined-p v) (to-integer-with-truncation v))))
           (rd-pos (k) (let ((v (js-get bag k)))
                         (unless (js-undefined-p v) (to-positive-integer-with-truncation v k)))))
      (let ((v (rd-pos "day"))) (when v (setf day v)))
      (let ((v (rd-int "hour"))) (when v (setf hour v)))
      (let ((v (rd-int "microsecond"))) (when v (setf us v)))
      (let ((v (rd-int "millisecond"))) (when v (setf ms v)))
      (let ((v (rd-int "minute"))) (when v (setf minute v)))
      (let ((v (rd-pos "month"))) (when v (setf month v)))
      ;; monthCode (ToPrimitiveAndRequireString + SYNTAX well-formedness). The
      ;; suitability check (range 1..12, leap-month rejection) is deferred until
      ;; AFTER year is read/coerced (spec order).
      (let ((v (js-get bag "monthCode")))
        (unless (js-undefined-p v)
          (setf mc-present t)
          (let ((prim (if (js-object-p v) (to-primitive v :string) v)))
            (unless (stringp prim)
              (js-throw (make-native-error "TypeError" "monthCode must be a string")))
            (multiple-value-bind (ok num leap) (monthcode-well-formed-p prim)
              (unless ok (js-throw (make-native-error "RangeError" "monthCode is not well-formed")))
              (setf mc num mc-leap leap)))))
      (let ((v (rd-int "nanosecond"))) (when v (setf ns v)))
      ;; offset: ToOffsetString — a String only (ToPrimitiveAndRequireString).
      (let ((v (js-get bag "offset")))
        (unless (js-undefined-p v)
          (setf offset-present t)
          (let ((prim (if (js-object-p v) (to-primitive v :string) v)))
            (unless (stringp prim)
              (js-throw (make-native-error "TypeError" "offset must be a string")))
            (let ((off (parse-offset-value prim)))
              (unless off
                (js-throw (make-native-error "RangeError" "invalid offset string")))
              (setf offset off)))))
      (let ((v (rd-int "second"))) (when v (setf second v)))
      ;; timeZone is read in its alphabetical slot (between second and year).
      (when read-timezone
        (let ((v (js-get bag "timeZone")))
          (when (js-undefined-p v)
            (js-throw (make-native-error "TypeError" "timeZone is required")))
          (multiple-value-setq (tz-id zone-offset) (to-time-zone-identifier v))))
      (let ((v (rd-int "year"))) (when v (setf year v)))
      ;; Required-field validation (TypeError) happens now (part of
      ;; PrepareCalendarFields, before options are read). monthCode SUITABILITY
      ;; and month<->monthCode resolution are DEFERRED to the caller (after the
      ;; options are read), so they run as algorithmic validation.
      (when (null year) (js-throw (make-native-error "TypeError" "year is required")))
      (when (and (null month) (not mc-present))
        (js-throw (make-native-error "TypeError" "month or monthCode is required")))
      (when (null day) (js-throw (make-native-error "TypeError" "day is required")))
      ;; Return raw fields; the caller resolves the month + applies overflow.
      (values year month mc mc-leap mc-present day hour minute second ms us ns
              offset offset-present tz-id zone-offset))))

(defun zdt-read-partial-fields (bag)
  "PrepareCalendarFields (partial) for with(): read the recognized fields in
   ALPHABETICAL order — day, hour, microsecond, millisecond, minute, month,
   monthCode, nanosecond, offset, second, year — coercing each present value.
   Returns a plist of present fields (:day :hour ... :monthcode(num) :monthcode-leap
   :monthcode-present :offset(ns) :offset-present :any). Absent fields are NIL."
  (let ((out '()) (any nil))
    (flet ((rd-int (k key) (let ((v (js-get bag k)))
                             (unless (js-undefined-p v)
                               (setf any t (getf out key) (to-integer-with-truncation v)))))
           (rd-pos (k key) (let ((v (js-get bag k)))
                             (unless (js-undefined-p v)
                               (setf any t (getf out key) (to-positive-integer-with-truncation v k))))))
      (rd-pos "day" :day)
      (rd-int "hour" :hour)
      (rd-int "microsecond" :microsecond)
      (rd-int "millisecond" :millisecond)
      (rd-int "minute" :minute)
      (rd-pos "month" :month)
      (let ((v (js-get bag "monthCode")))
        (unless (js-undefined-p v)
          (setf any t (getf out :monthcode-present) t)
          (let ((prim (if (js-object-p v) (to-primitive v :string) v)))
            (unless (stringp prim)
              (js-throw (make-native-error "TypeError" "monthCode must be a string")))
            (multiple-value-bind (ok num leap) (monthcode-well-formed-p prim)
              (unless ok (js-throw (make-native-error "RangeError" "monthCode is not well-formed")))
              (setf (getf out :monthcode) num (getf out :monthcode-leap) leap)))))
      (rd-int "nanosecond" :nanosecond)
      (let ((v (js-get bag "offset")))
        (unless (js-undefined-p v)
          (setf any t (getf out :offset-present) t)
          (let ((prim (if (js-object-p v) (to-primitive v :string) v)))
            (unless (stringp prim)
              (js-throw (make-native-error "TypeError" "offset must be a string")))
            (let ((off (parse-offset-value prim)))
              (unless off (js-throw (make-native-error "RangeError" "invalid offset string")))
              (setf (getf out :offset) off)))))
      (rd-int "second" :second)
      (rd-int "year" :year))
    (setf (getf out :any) any)
    out))

(defun zdt-resolve-month (month mc mc-leap mc-present)
  "Resolve the ISO month from month / monthCode fields, applying the SUITABILITY
   checks (leap-month rejection + 1..12 range + month/monthCode agreement)."
  (when mc-present
    (when mc-leap
      (js-throw (make-native-error "RangeError" "leap month is not valid in the ISO 8601 calendar")))
    (unless (<= 1 mc 12)
      (js-throw (make-native-error "RangeError" "monthCode is not valid for the ISO 8601 calendar"))))
  (cond ((and month mc-present)
         (unless (= month mc)
           (js-throw (make-native-error "RangeError" "month and monthCode conflict")))
         month)
        (mc-present mc)
        (t month)))

;;; ===========================================================================
;;; Calendar week helpers (share PlainDate's if present)
;;; ===========================================================================
(defun zdt-week-of-year (date) (iso-week-of-year date))

;;; ===========================================================================
;;; Difference / add (AddZonedDateTime, DifferenceZonedDateTime)
;;; ===========================================================================
(defun zdt-add (this d sign realm overflow)
  "AddZonedDateTime: add the date part in local calendar space, the time part in
   exact epoch space. SIGN is +1/-1. Returns a new ZonedDateTime."
  (let ((tz (zdt-tz this)) (offset (zdt-offset this)) (calendar (zdt-calendar this)))
    (multiple-value-bind (date time) (zdt-local-datetime this)
      ;; 1. add years/months/weeks/days to the local date.
      (let* ((newdate (add-iso-date date
                                    (* sign (getf d :years)) (* sign (getf d :months))
                                    (* sign (getf d :weeks)) (* sign (getf d :days))
                                    overflow))
             ;; 2. re-anchor to the zone: local wall time -> epoch (fixed offset).
             (local-ns (iso-datetime->epoch-ns newdate time))
             (epoch-after-date (- local-ns offset))
             ;; 3. add the time part in exact epoch space.
             (result (+ epoch-after-date (* sign (duration-time-ns d)))))
        (unless (valid-epoch-ns-p result)
          (js-throw (make-native-error "RangeError" "ZonedDateTime out of range")))
        (make-zoneddatetime realm result tz offset calendar)))))

(defun zdt-difference (this other-ns other-offset other-tz this-tz op options realm)
  "DifferenceZonedDateTime. For largestUnit day+ the date part is a calendar diff
   in local space; hour- is an exact epoch diff. OTHER-NS/OTHER-OFFSET describe
   the other ZonedDateTime. When largestUnit is a calendar unit the two time
   zones must be equal (RangeError otherwise)."
  (multiple-value-bind (smallest largest increment mode)
      (get-difference-settings op options
        :nanosecond :hour
        '(:year :month :week :day :hour :minute :second :millisecond :microsecond :nanosecond)
        '(:year :month :week :day :hour :minute :second :millisecond :microsecond :nanosecond)
        #'zdt-max-increment)
    (when (and (member largest '(:year :month :week :day))
               (not (string= this-tz other-tz)))
      (js-throw (make-native-error "RangeError"
                  "cannot compute a calendar difference between ZonedDateTimes with different time zones")))
    (let ((ns1 (zdt-ns this)))
      (if (member largest '(:hour :minute :second :millisecond :microsecond :nanosecond))
          ;; time-only difference: exact epoch ns.
          (let* ((raw (- other-ns ns1))
                 (unit-ns (unit->ns smallest))
                 (rounded (round-to-increment raw (* increment unit-ns) mode))
                 (final (if (eq op :since) (- rounded) rounded)))
            (make-temporal-duration realm (ns->time-duration final largest)))
          ;; calendar (day+) difference in local space.
          (let* ((offset (zdt-offset this))
                 (d1 (multiple-value-list (epoch-ns->iso-datetime (+ ns1 offset))))
                 (d2 (multiple-value-list (epoch-ns->iso-datetime (+ other-ns other-offset))))
                 (dur (zdt-diff-local (first d1) (second d1) (first d2) (second d2)
                                      offset ns1 other-ns smallest largest increment mode)))
            (make-temporal-duration realm
              (if (eq op :since)
                  (loop for f in +duration-fields+ append (list f (- (getf dur f))))
                  dur)))))))

(defun zdt-diff-local (d1 t1 d2 t2 offset ns1 ns2 smallest largest increment mode)
  "The local calendar+time difference between two wall-clock datetimes in the
   same fixed-offset zone. Reuses the PlainDateTime difference machinery, then
   rounds. For fixed zones the day length is always 24h, so the exact ns delta
   and the wall-clock delta agree — we can round via the epoch ns."
  (declare (ignore offset ns1 ns2))
  (let ((dur (pdt-difference d1 t1 d2 t2 largest)))
    (setf dur (pdt-round-duration dur d1 t1 d2 t2 smallest largest increment mode))
    dur))

(defun zdt-max-increment (unit)
  (ecase unit
    (:year 1000000000) (:month 1000000000) (:week 1000000000) (:day 1000000000)
    (:hour 24) (:minute 60) (:second 60)
    (:millisecond 1000) (:microsecond 1000) (:nanosecond 1000)))

;;; ===========================================================================
;;; round
;;; ===========================================================================
(defun zdt-round (this smallest increment mode realm)
  "Temporal.ZonedDateTime.prototype.round. Day rounding uses the day length
   (24h for fixed zones); time units round the exact epoch ns aligned to the
   local wall clock start-of-day."
  (let ((ns (zdt-ns this)) (offset (zdt-offset this))
        (tz (zdt-tz this)) (calendar (zdt-calendar this)))
    (if (eq smallest :day)
        ;; round to the nearest local start-of-day. Both the start of this day
        ;; and the start of the next day must be representable (the day length is
        ;; the rounding span) — RangeError otherwise.
        (multiple-value-bind (date time) (epoch-ns->iso-datetime (+ ns offset))
          (let* ((start-ns (- (* (iso-date->epoch-days date) +ns-per-day+) offset))
                 (next-start (+ start-ns +ns-per-day+)))
            (unless (and (valid-epoch-ns-p start-ns) (valid-epoch-ns-p next-start))
              (js-throw (make-native-error "RangeError" "day boundary is out of range")))
            (let* ((day-progress (iso-datetime->epoch-ns (make-iso-date 1970 1 1) time))
                   (rounded (round-to-increment day-progress (* increment +ns-per-day+) mode))
                   (result (+ start-ns rounded)))
              (unless (valid-epoch-ns-p result)
                (js-throw (make-native-error "RangeError" "ZonedDateTime out of range")))
              (make-zoneddatetime realm result tz offset calendar))))
        ;; time unit: round the local wall-clock ns since local start-of-day,
        ;; then re-anchor.
        (multiple-value-bind (date time) (epoch-ns->iso-datetime (+ ns offset))
          (let* ((start-ns (- (* (iso-date->epoch-days date) +ns-per-day+) offset))
                 (day-progress (iso-datetime->epoch-ns (make-iso-date 1970 1 1) time))
                 (unit-ns (unit->ns smallest))
                 (rounded (round-to-increment day-progress (* increment unit-ns) mode))
                 (result (+ start-ns rounded)))
            (unless (valid-epoch-ns-p result)
              (js-throw (make-native-error "RangeError" "ZonedDateTime out of range")))
            (make-zoneddatetime realm result tz offset calendar))))))

;;; ===========================================================================
;;; toString
;;; ===========================================================================
(defun get-timezone-name-option (options)
  (get-option-string options "timeZoneName"
                     '(("auto" . :auto) ("never" . :never) ("critical" . :critical))
                     :auto))

(defun zdt-to-string (this options realm &optional json)
  (declare (ignore realm))
  (let* ((ns (zdt-ns this)) (offset (zdt-offset this))
         (tz (zdt-tz this)) (calendar (zdt-calendar this)))
    (if json
        (multiple-value-bind (date time) (epoch-ns->iso-datetime (+ ns offset))
          (concatenate 'string
                       (format-iso-date-string (iso-date-year date) (iso-date-month date) (iso-date-day date))
                       "T" (format-iso-time time :auto)
                       (format-offset-ns offset)
                       (format nil "[~a]" tz)
                       (format-calendar-annotation calendar :auto)))
        (let* ((opts (get-options-object options))
               ;; spec read order: calendarName, fractionalSecondDigits, offset,
               ;; roundingMode, smallestUnit, timeZoneName
               (cal-name (get-calendar-name-option opts))
               (digits (get-fractional-second-digits opts))
               (show-offset (get-option-string opts "offset"
                              '(("auto" . :auto) ("never" . :never)) :auto))
               (mode (get-rounding-mode opts :trunc))
               (smallest (get-temporal-unit opts "smallestUnit" :time nil
                            '(:year :month :week :day :hour :minute :second
                              :millisecond :microsecond :nanosecond)))
               (show-tz (get-timezone-name-option opts)))
          (when (and smallest (not (member smallest '(:minute :second :millisecond :microsecond :nanosecond))))
            (js-throw (make-native-error "RangeError" "smallestUnit not allowed here")))
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
                 ;; RoundISODateTime rounds the LOCAL wall-clock datetime, whose
                 ;; fields are unsigned — so 'floor'/'trunc' both go toward the
                 ;; past and 'ceil'/'expand' toward the future regardless of the
                 ;; epoch sign. RoundNumberToIncrementAsIfPositive captures that.
                 (rounded-local (round-to-increment-as-if-positive (+ ns offset) unit-ns mode)))
            (multiple-value-bind (date time) (epoch-ns->iso-datetime rounded-local)
              (let* ((datestr (format-iso-date-string (iso-date-year date) (iso-date-month date) (iso-date-day date)))
                     (timestr (if (eq prec :minute)
                                  (format nil "~2,'0d:~2,'0d" (iso-time-hour time) (iso-time-minute time))
                                  (format-iso-time time prec)))
                     (offstr (if (eq show-offset :never) "" (format-offset-ns offset)))
                     (tzstr (ecase show-tz
                              (:never "")
                              (:auto (format nil "[~a]" tz))
                              (:critical (format nil "[!~a]" tz))))
                     (calstr (format-calendar-annotation calendar cal-name)))
                (concatenate 'string datestr "T" timestr offstr tzstr calstr))))))))

;;; ===========================================================================
;;; install
;;; ===========================================================================
(defun install-temporal-zoneddatetime (realm)
  (let* ((op (realm-object-proto realm))
         (proto (make-object :proto op :class "Object"))
         (ctor (native-function realm "ZonedDateTime"
                 (lambda (this args) (declare (ignore this args))
                   (js-throw (make-native-error "TypeError" "Constructor ZonedDateTime requires 'new'")))
                 2)))
    (setf *temporal-zoneddatetime-proto* proto)

    ;; ---- constructor: (epochNanoseconds, timeZone, calendar?) ----
    (setf (js-object-construct ctor)
          (lambda (args nt)
            (let ((ns (to-bigint (arg 0 args)))
                  (tz-v (arg 1 args))
                  (cal-v (arg 2 args)))
              (unless (valid-epoch-ns-p ns)
                (js-throw (make-native-error "RangeError" "epochNanoseconds out of range")))
              ;; The constructor's timeZone must be a bare id string (UTC or a
              ;; minute-precision offset) — NOT an ISO datetime string.
              (unless (stringp tz-v)
                (js-throw (make-native-error "TypeError" "time zone must be a string")))
              (multiple-value-bind (tz-id offset) (constructor-time-zone tz-v)
                (let ((calendar (if (js-undefined-p cal-v) "iso8601"
                                    (if (stringp cal-v)
                                        (if (string-equal cal-v "iso8601") "iso8601"
                                            (js-throw (make-native-error "RangeError" "calendar must be iso8601")))
                                        (js-throw (make-native-error "TypeError" "calendar must be a string"))))))
                  (make-zoneddatetime realm ns tz-id offset calendar nt))))))
    (def-value ctor "prototype" proto :writable nil :configurable nil)
    (def-value proto "constructor" ctor)

    ;; ---- statics ----
    (def-method realm ctor "from" 1 (this args)
      (declare (ignore this))
      (to-temporal-zoneddatetime realm (arg 0 args) (arg 1 args)))
    (def-method realm ctor "compare" 2 (this args)
      (declare (ignore this))
      (let ((a (zdt-arg-ns realm (arg 0 args)))
            (b (zdt-arg-ns realm (arg 1 args))))
        (float (cond ((< a b) -1) ((> a b) 1) (t 0)) 1d0)))

    ;; ---- getters ----
    (macrolet ((lget (name &body body)
                 `(def-getter realm proto ,name
                    (lambda (this args) (declare (ignore args))
                      (multiple-value-bind (date time) (zdt-local-datetime this)
                        (declare (ignorable date time))
                        ,@body)))))
      (def-getter realm proto "calendarId"
        (lambda (this args) (declare (ignore args)) (zdt-calendar this)))
      (def-getter realm proto "timeZoneId"
        (lambda (this args) (declare (ignore args)) (zdt-tz this)))
      (lget "year" (float (iso-date-year date) 1d0))
      (lget "month" (float (iso-date-month date) 1d0))
      (lget "monthCode" (format nil "M~2,'0d" (iso-date-month date)))
      (lget "day" (float (iso-date-day date) 1d0))
      (lget "hour" (float (iso-time-hour time) 1d0))
      (lget "minute" (float (iso-time-minute time) 1d0))
      (lget "second" (float (iso-time-second time) 1d0))
      (lget "millisecond" (float (iso-time-millisecond time) 1d0))
      (lget "microsecond" (float (iso-time-microsecond time) 1d0))
      (lget "nanosecond" (float (iso-time-nanosecond time) 1d0))
      (lget "dayOfWeek" (float (iso-day-of-week date) 1d0))
      (lget "dayOfYear" (float (iso-day-of-year date) 1d0))
      (lget "weekOfYear" (multiple-value-bind (w y) (zdt-week-of-year date) (declare (ignore y)) (float w 1d0)))
      (lget "yearOfWeek" (multiple-value-bind (w y) (zdt-week-of-year date) (declare (ignore w)) (float y 1d0)))
      (lget "daysInWeek" 7d0)
      (lget "daysInMonth" (float (days-in-month (iso-date-year date) (iso-date-month date)) 1d0))
      (lget "daysInYear" (float (iso-days-in-year (iso-date-year date)) 1d0))
      (lget "monthsInYear" 12d0)
      (lget "inLeapYear" (js-bool (leap-year-p (iso-date-year date))))
      (lget "hoursInDay"
        ;; The start of today and the start of tomorrow in this zone; if either
        ;; boundary falls outside the representable range, RangeError. For a fixed
        ;; offset the day is always 24h long.
        (declare (ignore time))
        (let* ((offset (zdt-offset this))
               (today-start (- (* (iso-date->epoch-days date) +ns-per-day+) offset))
               (tomorrow-start (+ today-start +ns-per-day+)))
          (unless (and (valid-epoch-ns-p today-start) (valid-epoch-ns-p tomorrow-start))
            (js-throw (make-native-error "RangeError" "day boundary is out of range")))
          (float (/ (- tomorrow-start today-start) +ns-per-hour+) 1d0)))
      (lget "era" (declare (ignore date time)) *undefined*)
      (lget "eraYear" (declare (ignore date time)) *undefined*))
    (def-getter realm proto "epochMilliseconds"
      (lambda (this args) (declare (ignore args))
        (float (floor (zdt-ns this) +ns-per-ms+) 1d0)))
    (def-getter realm proto "epochNanoseconds"
      (lambda (this args) (declare (ignore args)) (zdt-ns this)))
    (def-getter realm proto "offsetNanoseconds"
      (lambda (this args) (declare (ignore args)) (float (zdt-offset this) 1d0)))
    (def-getter realm proto "offset"
      (lambda (this args) (declare (ignore args)) (format-offset-ns (zdt-offset this))))

    ;; ---- with ----
    (def-method realm proto "with" 1 (this args)
      (let ((slot (zdt-slot this)) (bag (arg 0 args)))
        (unless (js-object-p bag)
          (js-throw (make-native-error "TypeError" "with() argument must be an object")))
        ;; A Temporal-branded object (which carries its own calendar/time-zone
        ;; identity) is not a valid partial-fields bag.
        (when (or (getf (js-object-internal bag) :temporal-plaindate)
                  (getf (js-object-internal bag) :temporal-plaindatetime)
                  (getf (js-object-internal bag) :temporal-plaintime)
                  (getf (js-object-internal bag) :temporal-plainmonthday)
                  (getf (js-object-internal bag) :temporal-plainyearmonth)
                  (getf (js-object-internal bag) :temporal-zoneddatetime)
                  (getf (js-object-internal bag) :temporal-duration))
          (js-throw (make-native-error "TypeError" "with() argument must be a plain object")))
        ;; RejectObjectWithCalendarOrTimeZone (calendar then timeZone).
        (reject-calendar-or-timezone bag)
        (let* ((tz (getf slot :timezone)) (offset (getf slot :offset))
               (calendar (zdt-calendar this)))
          (multiple-value-bind (date time) (zdt-local-datetime this)
            (let ((fields (zdt-read-partial-fields bag)))
              ;; PrepareCalendarFields requires at least one recognized field.
              (unless (getf fields :any)
                (js-throw (make-native-error "TypeError" "with() needs at least one recognized field")))
              ;; Options read AFTER the fields: disambiguation, offset, overflow.
              (let* ((opts (get-options-object (arg 1 args)))
                     (disamb (get-disambiguation-option opts))
                     (offset-option (get-offset-option opts))
                     (overflow (get-temporal-overflow opts)))
                (declare (ignore disamb))
                (let* ((mc-present (getf fields :monthcode-present))
                       (month (zdt-resolve-month
                               (getf fields :month) (getf fields :monthcode)
                               (getf fields :monthcode-leap) mc-present))
                       (year (or (getf fields :year) (iso-date-year date)))
                       (month (or month (iso-date-month date)))
                       (day (or (getf fields :day) (iso-date-day date)))
                       (hour (or (getf fields :hour) (iso-time-hour time)))
                       (minute (or (getf fields :minute) (iso-time-minute time)))
                       (second (or (getf fields :second) (iso-time-second time)))
                       (ms (or (getf fields :millisecond) (iso-time-millisecond time)))
                       (us (or (getf fields :microsecond) (iso-time-microsecond time)))
                       (nsf (or (getf fields :nanosecond) (iso-time-nanosecond time)))
                       (newdate (create-iso-date-checked year month day overflow))
                       (newtime (regulate-time hour minute second ms us nsf overflow))
                       (used-offset (if (getf fields :offset-present) (getf fields :offset) offset))
                       (new-ns (interpret-iso-datetime-offset newdate newtime offset used-offset
                                                              :wall offset-option)))
                  (unless (valid-epoch-ns-p new-ns)
                    (js-throw (make-native-error "RangeError" "ZonedDateTime out of range")))
                  (make-zoneddatetime realm new-ns tz offset calendar))))))))

    ;; ---- withPlainTime ----
    (def-method realm proto "withPlainTime" 0 (this args)
      (let ((tz (zdt-tz this)) (offset (zdt-offset this)) (calendar (zdt-calendar this)))
        (multiple-value-bind (date time) (zdt-local-datetime this)
          (declare (ignore time))
          (let* ((v (arg 0 args))
                 (newtime (if (js-undefined-p v) (make-iso-time 0 0 0 0 0 0)
                              (to-temporal-time realm v)))
                 (new-ns (- (iso-datetime->epoch-ns date newtime) offset)))
            (unless (valid-epoch-ns-p new-ns)
              (js-throw (make-native-error "RangeError" "ZonedDateTime out of range")))
            (make-zoneddatetime realm new-ns tz offset calendar)))))

    ;; ---- withTimeZone ----
    (def-method realm proto "withTimeZone" 1 (this args)
      (let ((ns (zdt-ns this)) (calendar (zdt-calendar this)))
        (multiple-value-bind (tz-id offset) (to-time-zone-identifier (arg 0 args))
          (make-zoneddatetime realm ns tz-id offset calendar))))

    ;; ---- withCalendar ----
    (def-method realm proto "withCalendar" 1 (this args)
      (let ((slot (zdt-slot this)))
        (let ((calendar (zdt-canonicalize-calendar (arg 0 args))))
          (make-zoneddatetime realm (getf slot :ns) (getf slot :timezone)
                              (getf slot :offset) calendar))))

    ;; ---- add / subtract ----
    (labels ((add-dur (this args negate)
               (let* ((d (to-temporal-duration-record (arg 0 args)))
                      (overflow (get-temporal-overflow (get-options-object (arg 1 args)))))
                 (zdt-add this d (if negate -1 1) realm overflow))))
      (def-method realm proto "add" 1 (this args) (add-dur this args nil))
      (def-method realm proto "subtract" 1 (this args) (add-dur this args t)))

    ;; ---- until / since ----
    (labels ((diff (this args op)
               (let ((tz1 (zdt-tz this)) (cal1 (zdt-calendar this)))
                 (let ((other (arg 0 args)))
                   (let ((oz (coerce-to-zdt realm other)))
                     (unless (string= cal1 (getf oz :calendar))
                       (js-throw (make-native-error "RangeError"
                                   "cannot compute difference between different calendars")))
                     (let ((options (get-options-object (arg 1 args))))
                       (zdt-difference this (getf oz :ns) (getf oz :offset)
                                       (getf oz :timezone) tz1 op options realm)))))))
      (def-method realm proto "until" 1 (this args) (diff this args :until))
      (def-method realm proto "since" 1 (this args) (diff this args :since)))

    ;; ---- round ----
    (def-method realm proto "round" 1 (this args)
      (zdt-slot this)
      (let ((arg0 (arg 0 args)))
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
          (let ((max (ecase smallest
                       (:day 1) (:hour 24) (:minute 60) (:second 60)
                       (:millisecond 1000) (:microsecond 1000) (:nanosecond 1000))))
            (validate-rounding-increment increment max (eq smallest :day))
            (unless (eq smallest :day)
              (when (/= 0 (mod max increment))
                (js-throw (make-native-error "RangeError" "increment does not divide evenly")))))
          (zdt-round this smallest increment mode realm))))

    ;; ---- equals ----
    (def-method realm proto "equals" 1 (this args)
      (let ((ns1 (zdt-ns this)) (tz1 (zdt-tz this)) (cal1 (zdt-calendar this)))
        (let ((oz (coerce-to-zdt realm (arg 0 args))))
          (js-bool (and (= ns1 (getf oz :ns))
                        (string= tz1 (getf oz :timezone))
                        (string= cal1 (getf oz :calendar)))))))

    ;; ---- startOfDay ----
    (def-method realm proto "startOfDay" 0 (this args)
      (declare (ignore args))
      (let ((offset (zdt-offset this)) (tz (zdt-tz this)) (calendar (zdt-calendar this)))
        (multiple-value-bind (date time) (zdt-local-datetime this)
          (declare (ignore time))
          (let ((new-ns (- (* (iso-date->epoch-days date) +ns-per-day+) offset)))
            (unless (valid-epoch-ns-p new-ns)
              (js-throw (make-native-error "RangeError" "start of day is out of range")))
            (make-zoneddatetime realm new-ns tz offset calendar)))))

    ;; ---- getTimeZoneTransition ----
    (def-method realm proto "getTimeZoneTransition" 1 (this args)
      (zdt-slot this)
      (let ((v (arg 0 args)))
        ;; The direction option is read/validated (observable) even though fixed
        ;; zones have no transitions.
        (cond ((js-undefined-p v)
               (js-throw (make-native-error "TypeError" "direction option required")))
              ((stringp v)
               (unless (member v '("next" "previous") :test #'string=)
                 (js-throw (make-native-error "RangeError" "invalid direction"))))
              ((js-object-p v)
               (get-option-string v "direction"
                                  '(("next" . :next) ("previous" . :previous)) :required))
              (t (js-throw (make-native-error "TypeError" "invalid direction option")))))
      *null*)

    ;; ---- toInstant ----
    (def-method realm proto "toInstant" 0 (this args)
      (declare (ignore args))
      (make-temporal-instant realm (zdt-ns this)))

    ;; ---- toPlainDate / toPlainTime / toPlainDateTime ----
    (def-method realm proto "toPlainDate" 0 (this args)
      (declare (ignore args))
      (let ((calendar (zdt-calendar this)))
        (multiple-value-bind (date time) (zdt-local-datetime this)
          (declare (ignore time))
          (make-plain-date date calendar realm))))
    (def-method realm proto "toPlainTime" 0 (this args)
      (declare (ignore args))
      (multiple-value-bind (date time) (zdt-local-datetime this)
        (declare (ignore date))
        (make-temporal-plaintime realm time)))
    (def-method realm proto "toPlainDateTime" 0 (this args)
      (declare (ignore args))
      (multiple-value-bind (date time) (zdt-local-datetime this)
        (make-temporal-plaindatetime realm date time)))

    ;; ---- toString / toJSON / toLocaleString ----
    (def-method realm proto "toString" 0 (this args)
      (zdt-to-string this (arg 0 args) realm))
    (def-method realm proto "toJSON" 0 (this args)
      (declare (ignore args))
      (zdt-to-string this *undefined* realm t))
    (def-method realm proto "toLocaleString" 0 (this args)
      (declare (ignore args))
      (zdt-to-string this *undefined* realm t))

    ;; ---- valueOf ----
    (def-method realm proto "valueOf" 0 (this args)
      (declare (ignore args))
      (js-throw (make-native-error "TypeError"
                  "Cannot convert a Temporal.ZonedDateTime to a primitive; use compare() or equals()")))

    ;; ---- @@toStringTag ----
    (put proto (symbol-tostringtag realm) "Temporal.ZonedDateTime"
         :enumerable nil :writable nil :configurable t)

    (temporal-register realm "ZonedDateTime" ctor)
    ctor))

;;; ===========================================================================
;;; helpers (post-install)
;;; ===========================================================================
(defun constructor-time-zone (s)
  "ToTemporalTimeZoneIdentifier for the CONSTRUCTOR: only \"UTC\" or a bare
   minute-precision offset — an ISO datetime string is NOT accepted (RangeError).
   Returns (values id offset-ns)."
  (when (string-equal s "UTC") (return-from constructor-time-zone (values "UTC" 0)))
  (multiple-value-bind (off nx sub) (parse-offset-string s 0 (length s))
    (unless (and off (= nx (length s)))
      (js-throw (make-native-error "RangeError" "invalid time zone identifier")))
    (when sub
      (js-throw (make-native-error "RangeError" "sub-minute offset is not a valid time zone")))
    (values (format-offset-id off) off)))

(defun coerce-to-zdt (realm v)
  "Coerce V to a ZonedDateTime and return a plist (:ns :timezone :offset :calendar)
   describing it. Accepts a ZonedDateTime instance, a property bag, or a string."
  (let ((z (to-temporal-zoneddatetime realm v *undefined*)))
    (let ((s (getf (js-object-internal z) :temporal-zoneddatetime)))
      (list :ns (getf s :ns) :timezone (getf s :timezone) :offset (getf s :offset)
            :calendar (getf (js-object-internal z) :temporal-calendar "iso8601")))))

(defun zdt-arg-ns (realm v)
  "The epoch-ns of a ZonedDateTime argument (for compare)."
  (getf (coerce-to-zdt realm v) :ns))

(register-builtin-installer 'install-temporal-zoneddatetime)
