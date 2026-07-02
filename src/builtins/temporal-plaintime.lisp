;;;; builtins/temporal-plaintime.lisp — Temporal.PlainTime.
;;;;
;;;; A wall-clock time with no date/zone, stored as an iso-time struct in the
;;;; :temporal-plaintime internal slot. Built entirely on the temporal-core
;;;; kernel (iso-time records, the parser, rounding engine, options readers).
(in-package #:shuttle)

(defvar *temporal-plaintime-proto* nil)

(defun make-temporal-plaintime (realm time &optional new-target)
  "CreateTemporalTime: TIME is a valid in-range iso-time."
  (declare (ignore realm))
  (let* ((proto (proto-from-newtarget new-target *temporal-plaintime-proto*))
         (o (make-object :proto proto :class "Object")))
    (setf (getf (js-object-internal o) :temporal-plaintime) time)
    o))

(defun plaintime-time (this)
  "RequireInternalSlot([[InitializedTemporalTime]]) -> iso-time."
  (temporal-slot this :temporal-plaintime "Temporal.PlainTime"))

(defun valid-time-p (h m s ms us ns)
  (and (<= 0 h 23) (<= 0 m 59) (<= 0 s 59)
       (<= 0 ms 999) (<= 0 us 999) (<= 0 ns 999)))

(defun to-integer-with-truncation (v)
  "ToIntegerWithTruncation: ToNumber then truncate toward zero; a non-finite
   value is a RangeError."
  (let ((n (to-number v)))
    (when (or (js-nan-p n) (= n *inf*) (= n *-inf*))
      (js-throw (make-native-error "RangeError" "value must be a finite integer")))
    (truncate (with-js-floats (ftruncate n)))))

(defun regulate-time (h m s ms us ns overflow)
  "RegulateTime: :constrain clamps each field into range, :reject RangeErrors on
   any out-of-range field. Returns an iso-time."
  (ecase overflow
    (:constrain
     (make-iso-time (max 0 (min 23 h)) (max 0 (min 59 m)) (max 0 (min 59 s))
                    (max 0 (min 999 ms)) (max 0 (min 999 us)) (max 0 (min 999 ns))))
    (:reject
     (unless (valid-time-p h m s ms us ns)
       (js-throw (make-native-error "RangeError" "time field out of range")))
     (make-iso-time h m s ms us ns))))

;;; ToTemporalTimeRecord field read order = ALPHABETICAL:
;;; hour, microsecond, millisecond, minute, nanosecond, second.
(defparameter +plaintime-fields+
  '(("hour" . :hour) ("microsecond" . :microsecond) ("millisecond" . :millisecond)
    ("minute" . :minute) ("nanosecond" . :nanosecond) ("second" . :second)))

(defun to-temporal-time-record (bag &optional (completeness :complete))
  "ToTemporalTimeRecord: read the six time fields off BAG in alphabetical order,
   each ToIntegerWithTruncation. When :complete, a missing field defaults to 0;
   when :partial, a missing field is left NIL (used by with()). At least one
   field must be present in the :partial case. Returns a plist."
  (let ((out '()) (any nil))
    (dolist (pair +plaintime-fields+)
      (let ((v (js-get bag (car pair))))
        (if (js-undefined-p v)
            (when (eq completeness :complete) (setf (getf out (cdr pair)) 0))
            (progn (setf any t)
                   (setf (getf out (cdr pair)) (to-integer-with-truncation v))))))
    (when (and (eq completeness :partial) (not any))
      (js-throw (make-native-error "TypeError" "no valid time fields")))
    out))

(defun reject-calendar-or-timezone (bag)
  "RejectObjectWithCalendarOrTimeZone: reads calendar then timeZone; a present
   (non-undefined) value on either is a TypeError."
  (unless (js-undefined-p (js-get bag "calendar"))
    (js-throw (make-native-error "TypeError" "unexpected calendar property")))
  (unless (js-undefined-p (js-get bag "timeZone"))
    (js-throw (make-native-error "TypeError" "unexpected timeZone property"))))

(defun to-temporal-time (realm v &optional (overflow-opts *undefined*))
  "ToTemporalTime: a PlainTime instance -> its time (options.overflow still read);
   a property bag -> RejectCalendarOrTimeZone + ToTemporalTimeRecord + regulate;
   a string -> parse (then overflow read). Returns an iso-time."
  (cond
    ((and (js-object-p v)
          (not (eq (getf (js-object-internal v) :temporal-plaintime 'none) 'none)))
     ;; overflow option is still read (observable) but the value is unused.
     (get-temporal-overflow (get-options-object overflow-opts))
     (getf (js-object-internal v) :temporal-plaintime))
    ((and (js-object-p v) (getf (js-object-internal v) :temporal-plaindatetime))
     (get-temporal-overflow (get-options-object overflow-opts))
     (getf (getf (js-object-internal v) :temporal-plaindatetime) :time))
    ((js-object-p v)
     ;; NOTE: ToTemporalTime (used by from/compare/until/since/equals) does NOT
     ;; RejectObjectWithCalendarOrTimeZone — only with() does that (see below).
     ;; The bag must supply at least one recognized time field (else TypeError);
     ;; :partial enforces that, then missing fields default to 0.
     (let ((rec (to-temporal-time-record v :partial))
           (overflow (get-temporal-overflow (get-options-object overflow-opts))))
       (regulate-time (or (getf rec :hour) 0) (or (getf rec :minute) 0) (or (getf rec :second) 0)
                      (or (getf rec :millisecond) 0) (or (getf rec :microsecond) 0)
                      (or (getf rec :nanosecond) 0)
                      overflow)))
    ((stringp v)
     (let ((time (parse-temporal-time v)))
       (get-temporal-overflow (get-options-object overflow-opts))
       time))
    (t (js-throw (make-native-error "TypeError" "cannot convert value to a Temporal.PlainTime")))))

(defun install-temporal-plaintime (realm)
  (let* ((op (realm-object-proto realm))
         (proto (make-object :proto op :class "Object"))
         (ctor (native-function realm "PlainTime"
                 (lambda (this args) (declare (ignore this args))
                   (js-throw (make-native-error "TypeError" "Constructor PlainTime requires 'new'")))
                 0)))
    (setf *temporal-plaintime-proto* proto)
    ;; ---- constructor: (hour, minute, second, ms, us, ns), each ToIntegerWithTruncation ----
    (setf (js-object-construct ctor)
          (lambda (args nt)
            (flet ((f (i) (let ((v (arg i args)))
                            (if (js-undefined-p v) 0 (to-integer-with-truncation v)))))
              (let ((h (f 0)) (m (f 1)) (s (f 2)) (ms (f 3)) (us (f 4)) (ns (f 5)))
                (unless (valid-time-p h m s ms us ns)
                  (js-throw (make-native-error "RangeError" "time field out of range")))
                (let ((o (make-object :proto (proto-from-newtarget nt proto) :class "Object")))
                  (setf (getf (js-object-internal o) :temporal-plaintime)
                        (make-iso-time h m s ms us ns))
                  o)))))
    (def-value ctor "prototype" proto :writable nil :configurable nil)
    (def-value proto "constructor" ctor)

    ;; ---- statics ----
    (def-method realm ctor "from" 1 (this args)
      (declare (ignore this))
      (make-temporal-plaintime realm (to-temporal-time realm (arg 0 args) (arg 1 args))))
    (def-method realm ctor "compare" 2 (this args)
      (declare (ignore this))
      (let ((a (to-temporal-time realm (arg 0 args)))
            (b (to-temporal-time realm (arg 1 args))))
        (float (let ((na (iso-datetime->epoch-ns (make-iso-date 1970 1 1) a))
                     (nb (iso-datetime->epoch-ns (make-iso-date 1970 1 1) b)))
                 (cond ((< na nb) -1) ((> na nb) 1) (t 0)))
               1d0)))

    ;; ---- getters ----
    (macrolet ((tgetter (name accessor)
                 `(def-getter realm proto ,name
                    (lambda (this args) (declare (ignore args))
                      (float (,accessor (plaintime-time this)) 1d0)))))
      (tgetter "hour" iso-time-hour)
      (tgetter "minute" iso-time-minute)
      (tgetter "second" iso-time-second)
      (tgetter "millisecond" iso-time-millisecond)
      (tgetter "microsecond" iso-time-microsecond)
      (tgetter "nanosecond" iso-time-nanosecond))

    ;; ---- add / subtract (wrap mod 24h) ----
    (labels ((add-dur (this args negate)
               (let* ((time (plaintime-time this))
                      (d (validate-duration-range (to-temporal-duration-record (arg 0 args))))
                      (delta (duration-time-ns d))
                      (base (iso-datetime->epoch-ns (make-iso-date 1970 1 1) time))
                      (result-ns (mod (+ base (if negate (- delta) delta)) +ns-per-day+)))
                 (multiple-value-bind (day newtime) (balance-time 0 0 0 0 0 result-ns)
                   (declare (ignore day))
                   (make-temporal-plaintime realm newtime)))))
      (def-method realm proto "add" 1 (this args) (add-dur this args nil))
      (def-method realm proto "subtract" 1 (this args) (add-dur this args t)))

    ;; ---- with ----
    (def-method realm proto "with" 1 (this args)
      (let ((time (plaintime-time this))
            (bag (arg 0 args)))
        (unless (js-object-p bag)
          (js-throw (make-native-error "TypeError" "with() argument must be an object")))
        ;; RejectObjectWithCalendarOrTimeZone (calendar then timeZone) precedes
        ;; the field reads, which precede the options read.
        (reject-calendar-or-timezone bag)
        (let* ((partial (to-temporal-time-record bag :partial))
               (overflow (get-temporal-overflow (get-options-object (arg 1 args))))
               (h  (or (getf partial :hour) (iso-time-hour time)))
               (mi (or (getf partial :minute) (iso-time-minute time)))
               (s  (or (getf partial :second) (iso-time-second time)))
               (ms (or (getf partial :millisecond) (iso-time-millisecond time)))
               (us (or (getf partial :microsecond) (iso-time-microsecond time)))
               (ns (or (getf partial :nanosecond) (iso-time-nanosecond time))))
          (make-temporal-plaintime realm (regulate-time h mi s ms us ns overflow)))))

    ;; ---- until / since ----
    (labels ((diff (this args op)
               (let* ((t1 (plaintime-time this))
                      (t2 (to-temporal-time realm (arg 0 args)))
                      (options (get-options-object (arg 1 args))))
                 (multiple-value-bind (smallest largest increment mode)
                     (get-difference-settings op options
                       :nanosecond :hour
                       '(:hour :minute :second :millisecond :microsecond :nanosecond)
                       '(:hour :minute :second :millisecond :microsecond :nanosecond)
                       #'plaintime-max-increment)
                   (let* ((n1 (iso-datetime->epoch-ns (make-iso-date 1970 1 1) t1))
                          (n2 (iso-datetime->epoch-ns (make-iso-date 1970 1 1) t2))
                          (raw (- n2 n1))
                          (unit-ns (plaintime-unit->ns smallest))
                          (rounded (round-to-increment raw (* increment unit-ns) mode))
                          (final (if (eq op :since) (- rounded) rounded))
                          (d (plaintime-ns->duration final largest)))
                     (make-temporal-duration realm d))))))
      (def-method realm proto "until" 1 (this args) (diff this args :until))
      (def-method realm proto "since" 1 (this args) (diff this args :since)))

    ;; ---- round ----
    (def-method realm proto "round" 1 (this args)
      (let ((time (plaintime-time this))
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
          (let* ((unit-ns (plaintime-unit->ns smallest))
                 (max (floor +ns-per-day+ unit-ns)))
            ;; PlainTime.round: the increment must be < the count of smallestUnit
            ;; in a day (exclusive) AND divide it evenly.
            (validate-rounding-increment increment max nil)
            (when (/= 0 (mod max increment))
              (js-throw (make-native-error "RangeError" "increment does not divide evenly")))
            (let* ((base (iso-datetime->epoch-ns (make-iso-date 1970 1 1) time))
                   (rounded (mod (round-to-increment base (* increment unit-ns) mode) +ns-per-day+)))
              (multiple-value-bind (day newtime) (balance-time 0 0 0 0 0 rounded)
                (declare (ignore day))
                (make-temporal-plaintime realm newtime)))))))

    ;; ---- equals ----
    (def-method realm proto "equals" 1 (this args)
      (let ((a (plaintime-time this)) (b (to-temporal-time realm (arg 0 args))))
        (js-bool (and (= (iso-time-hour a) (iso-time-hour b))
                      (= (iso-time-minute a) (iso-time-minute b))
                      (= (iso-time-second a) (iso-time-second b))
                      (= (iso-time-millisecond a) (iso-time-millisecond b))
                      (= (iso-time-microsecond a) (iso-time-microsecond b))
                      (= (iso-time-nanosecond a) (iso-time-nanosecond b))))))

    ;; ---- toString / toJSON / toLocaleString ----
    (def-method realm proto "toString" 0 (this args)
      (plaintime-to-string realm (plaintime-time this) (arg 0 args)))
    (def-method realm proto "toJSON" 0 (this args)
      (declare (ignore args))
      (format-iso-time (plaintime-time this) :auto))
    (def-method realm proto "toLocaleString" 0 (this args)
      (declare (ignore args))
      (format-iso-time (plaintime-time this) :auto))

    ;; ---- valueOf: not a primitive ----
    (def-method realm proto "valueOf" 0 (this args)
      (declare (ignore args))
      (js-throw (make-native-error "TypeError"
                  "Cannot convert a Temporal.PlainTime to a primitive; use compare() or equals()")))

    ;; ---- @@toStringTag ----
    (put proto (symbol-tostringtag realm) "Temporal.PlainTime"
         :enumerable nil :writable nil :configurable t)

    (temporal-register realm "PlainTime" ctor)))

;;; ---------------------------------------------------------------------------
;;; helpers
;;; ---------------------------------------------------------------------------
(defun plaintime-unit->ns (unit)
  (ecase unit
    (:hour +ns-per-hour+) (:minute +ns-per-min+) (:second +ns-per-s+)
    (:millisecond +ns-per-ms+) (:microsecond +ns-per-us+) (:nanosecond 1)))

(defun plaintime-max-increment (unit)
  (ecase unit
    (:hour 24) (:minute 60) (:second 60)
    (:millisecond 1000) (:microsecond 1000) (:nanosecond 1000)))

(defun plaintime-ns->duration (total-ns largest-unit)
  "Balance a signed ns total into a time-only duration plist (reuses the same
   cascade as the Instant helper)."
  (ns->time-duration total-ns largest-unit))

(defun plaintime-to-string (realm time options)
  "TemporalTimeToString with precision/rounding options (fractionalSecondDigits,
   roundingMode, smallestUnit — read in that order)."
  (declare (ignore realm))
  (let* ((opts (get-options-object options))
         (digits (get-fractional-second-digits opts))
         (mode (get-rounding-mode opts :trunc))
         (smallest (get-temporal-unit opts "smallestUnit" :time nil
                                      '(:year :month :week :day :hour :minute
                                        :second :millisecond :microsecond :nanosecond))))
    (when (and smallest (not (member smallest '(:minute :second :millisecond :microsecond :nanosecond))))
      (js-throw (make-native-error "RangeError" "smallestUnit not allowed for PlainTime.toString")))
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
           (base (iso-datetime->epoch-ns (make-iso-date 1970 1 1) time))
           (rounded (mod (round-to-increment base unit-ns mode) +ns-per-day+)))
      (multiple-value-bind (day newtime) (balance-time 0 0 0 0 0 rounded)
        (declare (ignore day))
        (if (eq prec :minute)
            (format nil "~2,'0d:~2,'0d" (iso-time-hour newtime) (iso-time-minute newtime))
            (format-iso-time newtime prec))))))

(register-builtin-installer 'install-temporal-plaintime)
