;;;; builtins/temporal-instant.lisp — Temporal.Instant.
;;;;
;;;; An Instant is a fixed point on the UTC timeline, stored as EXACT epoch
;;;; nanoseconds (a CL integer) in the :temporal-instant internal slot. Because
;;;; JS BigInt == CL integer here, epochNanoseconds simply returns that integer.
;;;; Everything is built on temporal-core (the kernel).
(in-package #:shuttle)

(defvar *temporal-instant-proto* nil)

(defun make-temporal-instant (realm ns &optional new-target)
  "CreateTemporalInstant: NS is an exact integer already validated in range."
  (declare (ignore realm))
  (let* ((proto (proto-from-newtarget new-target *temporal-instant-proto*))
         (o (make-object :proto proto :class "Object")))
    (setf (getf (js-object-internal o) :temporal-instant) ns)
    o))

(defun instant-ns (this)
  "RequireInternalSlot([[InitializedTemporalInstant]]) -> exact ns integer."
  (temporal-slot this :temporal-instant "Temporal.Instant"))

(defun to-temporal-instant (realm v)
  "ToTemporalInstant: an Instant instance -> its ns; a ZonedDateTime -> its ns
   (not built this round); a String -> parse. Any other primitive (number,
   bigint, boolean, undefined, null, symbol) or a non-branded object is a
   TypeError (the value is NOT coerced to string)."
  (declare (ignore realm))
  (cond
    ((and (js-object-p v)
          (not (eq (getf (js-object-internal v) :temporal-instant 'none) 'none)))
     (getf (js-object-internal v) :temporal-instant))
    ((and (js-object-p v) (getf (js-object-internal v) :temporal-zoneddatetime))
     (getf (getf (js-object-internal v) :temporal-zoneddatetime) :ns))
    ((js-object-p v)
     ;; An ordinary object: ToString via ToPrimitive, then parse.
     (parse-temporal-instant (to-string (to-primitive v :string))))
    ((stringp v) (parse-temporal-instant v))
    (t (js-throw (make-native-error "TypeError"
                   "cannot convert value to a Temporal.Instant")))))

(defun install-temporal-instant (realm)
  (let* ((op (realm-object-proto realm))
         (proto (make-object :proto op :class "Object"))
         (ctor (native-function realm "Instant"
                 (lambda (this args) (declare (ignore this args))
                   (js-throw (make-native-error "TypeError" "Constructor Instant requires 'new'")))
                 1)))
    (setf *temporal-instant-proto* proto)
    ;; ---- constructor ----
    (setf (js-object-construct ctor)
          (lambda (args nt)
            ;; ToBigInt(epochNanoseconds) — NOT a Temporal parse. Strings go
            ;; through the numeric BigInt grammar (SyntaxError on garbage).
            (let ((ns (to-bigint (arg 0 args))))
              (unless (valid-epoch-ns-p ns)
                (js-throw (make-native-error "RangeError" "epochNanoseconds out of range")))
              ;; GetPrototypeFromConstructor is observable (may throw).
              (let ((proto2 (proto-from-newtarget nt proto)))
                (let ((o (make-object :proto proto2 :class "Object")))
                  (setf (getf (js-object-internal o) :temporal-instant) ns)
                  o)))))
    (def-value ctor "prototype" proto :writable nil :configurable nil)
    (def-value proto "constructor" ctor)

    ;; ---- statics ----
    (def-method realm ctor "from" 1 (this args)
      (declare (ignore this))
      (make-temporal-instant realm (to-temporal-instant realm (arg 0 args))))
    (def-method realm ctor "fromEpochMilliseconds" 1 (this args)
      (declare (ignore this))
      (let ((n (to-number (arg 0 args))))
        (when (or (js-nan-p n) (= n *inf*) (= n *-inf*))
          (js-throw (make-native-error "RangeError" "epochMilliseconds must be a finite integer")))
        (let ((i (with-js-floats (ftruncate n))))
          (when (/= i n)
            (js-throw (make-native-error "RangeError" "epochMilliseconds must be an integer")))
        (let ((ns (* (truncate i) +ns-per-ms+)))
          (unless (valid-epoch-ns-p ns)
            (js-throw (make-native-error "RangeError" "epochMilliseconds out of range")))
          (make-temporal-instant realm ns)))))
    (def-method realm ctor "fromEpochNanoseconds" 1 (this args)
      (declare (ignore this))
      (let ((ns (to-bigint (arg 0 args))))
        (unless (valid-epoch-ns-p ns)
          (js-throw (make-native-error "RangeError" "epochNanoseconds out of range")))
        (make-temporal-instant realm ns)))
    (def-method realm ctor "compare" 2 (this args)
      (declare (ignore this))
      (let ((a (to-temporal-instant realm (arg 0 args)))
            (b (to-temporal-instant realm (arg 1 args))))
        (float (cond ((< a b) -1) ((> a b) 1) (t 0)) 1d0)))

    ;; ---- getters ----
    (def-getter realm proto "epochMilliseconds"
      (lambda (this args) (declare (ignore args))
        (float (floor (instant-ns this) +ns-per-ms+) 1d0)))
    (def-getter realm proto "epochNanoseconds"
      (lambda (this args) (declare (ignore args))
        (instant-ns this)))            ; CL integer == JS BigInt

    ;; ---- add / subtract (time-only durations) ----
    (labels ((add-duration (this args negate)
               (let* ((ns (instant-ns this))
                      (d (to-temporal-duration-record (arg 0 args))))
                 ;; Instant arithmetic disallows calendar/day units.
                 (dolist (f '(:years :months :weeks :days))
                   (unless (zerop (getf d f))
                     (js-throw (make-native-error "RangeError"
                                 "Instant add/subtract does not allow calendar or day units"))))
                 (let* ((delta (duration-time-ns d))
                        (result (+ ns (if negate (- delta) delta))))
                   (unless (valid-epoch-ns-p result)
                     (js-throw (make-native-error "RangeError" "Instant result out of range")))
                   (make-temporal-instant realm result)))))
      (def-method realm proto "add" 1 (this args) (add-duration this args nil))
      (def-method realm proto "subtract" 1 (this args) (add-duration this args t)))

    ;; ---- until / since ----
    (labels ((diff (this args op)
               (let* ((ns1 (instant-ns this))
                      (other (to-temporal-instant realm (arg 0 args)))
                      (options (get-options-object (arg 1 args))))
                 (multiple-value-bind (smallest largest increment mode)
                     (get-difference-settings op options
                       :nanosecond :second
                       '(:hour :minute :second :millisecond :microsecond :nanosecond)
                       '(:hour :minute :second :millisecond :microsecond :nanosecond)
                       #'instant-max-increment)
                   ;; Always compute in the until direction (other - this); MODE
                   ;; is already negated for :since by get-difference-settings, so
                   ;; round first then negate the whole result for :since.
                   ;; RoundNumberToIncrement (signed). MODE is already negated for
                   ;; :since by get-difference-settings; round the until-direction
                   ;; difference, then negate the whole result for :since.
                   (let* ((raw (- other ns1))
                          (unit-ns (unit->ns smallest))
                          (rounded (round-to-increment raw (* increment unit-ns) mode))
                          (final (if (eq op :since) (- rounded) rounded))
                          (d (ns->time-duration final largest)))
                     (make-temporal-duration realm d))))))
      (def-method realm proto "until" 1 (this args) (diff this args :until))
      (def-method realm proto "since" 1 (this args) (diff this args :since)))

    ;; ---- round ----
    ;; When passed an options object, ALL option properties are read (and cast)
    ;; before any algorithmic validation, in alphabetical key order:
    ;; roundingIncrement, roundingMode, smallestUnit. round("hour") is the
    ;; string shorthand (only smallestUnit).
    (def-method realm proto "round" 1 (this args)
      (let ((ns (instant-ns this))
            (arg0 (arg 0 args)))
        (when (js-undefined-p arg0)
          (js-throw (make-native-error "TypeError" "options required")))
        (multiple-value-bind (smallest increment mode)
            (if (stringp arg0)
                (let ((hit (assoc arg0 (unit-alist '(:hour :minute :second :millisecond :microsecond :nanosecond))
                                  :test #'string=)))
                  (unless hit (js-throw (make-native-error "RangeError" "invalid smallestUnit")))
                  (values (cdr hit) 1 :half-expand))
                (let* ((options (get-options-object arg0))
                       (increment (get-rounding-increment options))
                       (mode (get-rounding-mode options :half-expand))
                       (smallest (get-temporal-unit options "smallestUnit" :time :required
                                                    '(:hour :minute :second :millisecond :microsecond :nanosecond))))
                  (values smallest increment mode)))
          (let* ((unit-ns (unit->ns smallest))
                 (max (floor +ns-per-day+ unit-ns)))
            (validate-rounding-increment increment max t)
            (when (/= 0 (mod max increment))
              (js-throw (make-native-error "RangeError" "increment does not divide evenly")))
            (let ((rounded (round-to-increment-as-if-positive ns (* increment unit-ns) mode)))
              (unless (valid-epoch-ns-p rounded)
                (js-throw (make-native-error "RangeError" "rounded Instant out of range")))
              (make-temporal-instant realm rounded))))))

    ;; ---- equals ----
    (def-method realm proto "equals" 1 (this args)
      (let ((a (instant-ns this)) (b (to-temporal-instant realm (arg 0 args))))
        (js-bool (= a b))))

    ;; ---- toString / toJSON / toLocaleString ----
    (def-method realm proto "toString" 0 (this args)
      (instant-to-string realm (instant-ns this) (arg 0 args)))
    (def-method realm proto "toJSON" 0 (this args)
      (declare (ignore args))
      (instant-to-string realm (instant-ns this) *undefined* t))
    (def-method realm proto "toLocaleString" 0 (this args)
      (declare (ignore args))
      (instant-to-string realm (instant-ns this) *undefined* t))

    ;; ---- toZonedDateTimeISO ----
    ;; Dynamically dispatch to the realm's Temporal.ZonedDateTime if it is
    ;; registered (the concurrent ZDT type lights this up without another edit);
    ;; a clear TypeError otherwise.
    (def-method realm proto "toZonedDateTimeISO" 1 (this args)
      (let ((ns (instant-ns this)))   ; brand-check first
        (if (and (fboundp 'to-time-zone-identifier) (fboundp 'make-zoneddatetime))
            (multiple-value-bind (tz-id offset) (funcall 'to-time-zone-identifier (arg 0 args))
              (funcall 'make-zoneddatetime realm ns tz-id offset "iso8601"))
            (js-throw (make-native-error "TypeError" "Temporal.ZonedDateTime is not available")))))

    ;; ---- valueOf: Temporal types are never primitives ----
    (def-method realm proto "valueOf" 0 (this args)
      (declare (ignore args))
      (js-throw (make-native-error "TypeError"
                  "Cannot convert a Temporal.Instant to a primitive; use compare() or epochNanoseconds")))

    ;; ---- @@toStringTag ----
    (put proto (symbol-tostringtag realm) "Temporal.Instant"
         :enumerable nil :writable nil :configurable t)

    ;; register on the Temporal namespace
    (temporal-register realm "Instant" ctor)

    ;; ---- Date.prototype.toTemporalInstant ----
    (install-date-to-temporal-instant realm)))

;;; ---------------------------------------------------------------------------
;;; helpers
;;; ---------------------------------------------------------------------------
(defun unit->ns (unit)
  (ecase unit
    (:hour +ns-per-hour+) (:minute +ns-per-min+) (:second +ns-per-s+)
    (:millisecond +ns-per-ms+) (:microsecond +ns-per-us+) (:nanosecond 1)))

(defun instant-max-increment (unit)
  "Maximum rounding increment for an Instant difference at UNIT: the count of
   UNIT in the next-coarser unit (hours-in-day for hour, then 60/60/1000/1000/1000)."
  (ecase unit
    (:hour 24) (:minute 60) (:second 60)
    (:millisecond 1000) (:microsecond 1000) (:nanosecond 1000)))

(defun ns->time-duration (total-ns largest-unit)
  "Balance TOTAL-NS (signed exact integer) into a duration plist whose largest
   populated component is LARGEST-UNIT. Units coarser than LARGEST-UNIT stay 0;
   the balance cascades from LARGEST-UNIT down to nanoseconds."
  (let* ((sign (if (minusp total-ns) -1 1))
         (a (abs total-ns))
         (rank (position largest-unit '(:hour :minute :second :millisecond :microsecond :nanosecond)))
         (hours 0) (minutes 0) (seconds 0) (ms 0) (us 0) (ns 0))
    (when (<= rank 0) (multiple-value-setq (hours a) (floor a +ns-per-hour+)))
    (when (<= rank 1) (multiple-value-setq (minutes a) (floor a +ns-per-min+)))
    (when (<= rank 2) (multiple-value-setq (seconds a) (floor a +ns-per-s+)))
    (when (<= rank 3) (multiple-value-setq (ms a) (floor a +ns-per-ms+)))
    (when (<= rank 4) (multiple-value-setq (us a) (floor a +ns-per-us+)))
    (setf ns a)
    (list :years 0 :months 0 :weeks 0 :days 0
          :hours (* sign hours) :minutes (* sign minutes) :seconds (* sign seconds)
          :milliseconds (* sign ms) :microseconds (* sign us) :nanoseconds (* sign ns))))

(defun instant-to-string (realm ns options &optional json)
  "TemporalInstantToString. When JSON, no options are read (always Z, auto)."
  (declare (ignore realm))
  (if json
      (let* ((date-time (multiple-value-list (epoch-ns->iso-datetime ns)))
             (date (first date-time)) (time (second date-time)))
        (concatenate 'string
                     (format-iso-date-string (iso-date-year date) (iso-date-month date) (iso-date-day date))
                     "T" (format-iso-time time :auto) "Z"))
      (let* ((opts (get-options-object options))
             ;; SPEC ORDER: fractionalSecondDigits, roundingMode, smallestUnit,
             ;; timeZone.
             (digits (get-fractional-second-digits opts))
             (mode (get-rounding-mode opts :trunc))
             ;; Cast smallestUnit against ALL units (so a date unit is read, not
             ;; rejected, before timeZone is read); validate allowed afterwards.
             (smallest (get-temporal-unit opts "smallestUnit" :time nil
                                          '(:year :month :week :day :hour :minute
                                            :second :millisecond :microsecond :nanosecond)))
             (tz (%opt-get opts "timeZone")))
        (when (and smallest (not (member smallest '(:minute :second :millisecond :microsecond :nanosecond))))
          (js-throw (make-native-error "RangeError" "smallestUnit not allowed for Instant.toString")))
        ;; smallestUnit overrides fractionalSecondDigits. PREC is the number of
        ;; fractional digits to print (:auto/:minute/0..9); UNIT-NS is the
        ;; rounding increment the value is snapped to before formatting.
        (let* ((prec (cond ((null smallest) digits)
                           ((eq smallest :minute) :minute)
                           (t (ecase smallest
                                (:second 0) (:millisecond 3)
                                (:microsecond 6) (:nanosecond 9)))))
               (unit-ns (cond ((null smallest)
                               (if (eq digits :auto) 1 (expt 10 (- 9 digits))))
                              (t (ecase smallest
                                   (:minute +ns-per-min+) (:second +ns-per-s+)
                                   (:millisecond +ns-per-ms+) (:microsecond +ns-per-us+)
                                   (:nanosecond 1)))))
               (rounded (round-to-increment-as-if-positive ns unit-ns mode))
               (offset (cond ((js-undefined-p tz) 0)
                              ;; ToTemporalTimeZoneIdentifier: only a String
                              ;; (or a TimeZone-bearing object, none here) is
                              ;; accepted; other values are a TypeError.
                              ((stringp tz) (to-tz-offset-ns tz))
                              (t (js-throw (make-native-error "TypeError"
                                            "timeZone must be a string"))))))
          (multiple-value-bind (date time) (epoch-ns->iso-datetime (+ rounded offset))
            (concatenate 'string
                         (format-iso-date-string (iso-date-year date) (iso-date-month date) (iso-date-day date))
                         "T" (instant-format-time time prec)
                         (if (js-undefined-p tz) "Z" (format-offset-ns offset))))))))

(defun instant-format-time (time prec)
  "Format time for an Instant. PREC = :minute (drop seconds), :auto, or 0..9."
  (if (eq prec :minute)
      (format nil "~2,'0d:~2,'0d" (iso-time-hour time) (iso-time-minute time))
      (format-iso-time time prec)))

(defun to-tz-offset-ns (s)
  "ToTemporalTimeZoneIdentifier for the offset-only zones the corpus uses.
   Accepts: 'UTC' (any case) -> 0; a bare minute-precision offset (+HH:MM etc.,
   sub-minute rejected) -> that offset; a datetime string whose annotation names
   a time zone, or whose numeric offset is minute-precision (Z -> 0). Signals
   RangeError otherwise."
  (when (string-equal s "UTC") (return-from to-tz-offset-ns 0))
  ;; bare offset?
  (multiple-value-bind (off nx sub) (parse-offset-string s 0 (length s))
    (when (and off (= nx (length s)))
      ;; An offset time-zone identifier must be minute-precision in FORM — a
      ;; seconds/fractional component is invalid even if the value is aligned.
      (when sub
        (js-throw (make-native-error "RangeError" "sub-minute offset is not a valid time zone")))
      (return-from to-tz-offset-ns off)))
  ;; datetime form with optional [annotation] time zone.
  (let* ((br (position #\[ s)))
    (if br
        ;; annotation present -> the annotation names the zone.
        (let ((rb (position #\] s :start br)))
          (unless rb (js-throw (make-native-error "RangeError" "invalid time zone")))
          (let ((ann (subseq s (1+ br) rb)))
            (when (char= (char ann 0) #\!) (setf ann (subseq ann 1)))
            (to-tz-offset-ns ann)))
        ;; no annotation -> parse as datetime, use its offset (Z=0);
        ;; sub-minute offset rejected.
        (let ((r (parse-iso-datetime (string-trim '(#\Space) s) :datetime)))
          (let ((off (getf r :offset)))
            (unless (getf r :offset-present)
              (js-throw (make-native-error "RangeError" "bare date-time is not a time zone")))
            (when (getf r :offset-sub-minute)
              (js-throw (make-native-error "RangeError" "sub-minute offset is not a valid time zone")))
            off)))))

;;; ---------------------------------------------------------------------------
;;; Date.prototype.toTemporalInstant (8 tests)
;;; ---------------------------------------------------------------------------
(defun install-date-to-temporal-instant (realm)
  (let ((date-ctor (ignore-errors (js-get (realm-global realm) "Date"))))
    (when (js-object-p date-ctor)
      (let ((dp (js-get date-ctor "prototype")))
        (when (js-object-p dp)
          (def-method realm dp "toTemporalInstant" 0 (this args)
            (declare (ignore args))
            ;; thisTimeValue: the Date's [[DateValue]] (a double ms). NaN -> RangeError.
            (unless (and (js-object-p this) (string= (js-object-class this) "Date"))
              (js-throw (make-native-error "TypeError" "not a Date")))
            (let ((tv (js-object-primitive this)))
              (when (or (not (floatp tv)) (js-nan-p tv))
                (js-throw (make-native-error "RangeError" "Invalid Date")))
              (let ((ns (* (truncate (with-js-floats (ftruncate tv))) +ns-per-ms+)))
                (make-temporal-instant realm ns)))))))))

(register-builtin-installer 'install-temporal-instant)
