;;;; builtins/temporal-now.lisp — Temporal.Now namespace.
;;;;
;;;; A non-constructor namespace object hung off Temporal. The clock reads the
;;;; system time via sb-ext:get-time-of-day -> exact epoch nanoseconds. Only
;;;; instant()/timeZoneId()/plainTimeISO() are fully live this round; the
;;;; date-bearing members defer until PlainDate/PlainDateTime/ZonedDateTime exist
;;;; (temporal-now-install-dated rewires them once the date types exist).
(in-package #:shuttle)

(defun now-epoch-ns ()
  "System clock as exact epoch nanoseconds."
  (multiple-value-bind (sec usec) (ignore-errors (sb-ext:get-time-of-day))
    (if sec
        (+ (* sec +ns-per-s+) (* usec +ns-per-us+))
        (* (- (get-universal-time) 2208988800) +ns-per-s+))))

(defun now-tz-offset (tz)
  "Offset-ns for a Temporal.Now time-zone argument: undefined -> 0 (system UTC);
   a String -> its offset (TypeError on a non-string). Uses the ZonedDateTime
   time-zone resolver so ISO-string / annotation forms behave identically."
  (cond ((js-undefined-p tz) 0)
        ((stringp tz) (nth-value 1 (to-time-zone-identifier tz)))
        (t (js-throw (make-native-error "TypeError" "timeZone must be a string")))))

(defun install-temporal-now (realm)
  (let* ((op (realm-object-proto realm))
         (now (make-object :proto op :class "Object")))
    ;; @@toStringTag = "Temporal.Now"
    (put now (symbol-tostringtag realm) "Temporal.Now"
         :enumerable nil :writable nil :configurable t)

    ;; instant() -> Temporal.Instant of the current time.
    (def-method realm now "instant" 0 (this args)
      (declare (ignore this args))
      (make-temporal-instant realm (now-epoch-ns)))

    ;; timeZoneId() -> the default time zone id (we run as UTC).
    (def-method realm now "timeZoneId" 0 (this args)
      (declare (ignore this args))
      "UTC")

    ;; plainTimeISO([timeZone]) -> the wall-clock time in the given zone
    ;; (default UTC). Only offset/UTC zones are supported (corpus fact).
    (def-method realm now "plainTimeISO" 0 (this args)
      (declare (ignore this))
      (let* ((tz (arg 0 args))
             (offset (cond ((js-undefined-p tz) 0)
                           ((stringp tz) (to-tz-offset-ns tz))
                           (t (js-throw (make-native-error "TypeError" "timeZone must be a string")))))
             (ns (+ (now-epoch-ns) offset)))
        (multiple-value-bind (date time) (epoch-ns->iso-datetime ns)
          (declare (ignore date))
          (make-temporal-plaintime realm time))))

    ;; plainDateTimeISO([timeZone]) -> the wall-clock date+time in the given zone.
    (def-method realm now "plainDateTimeISO" 0 (this args)
      (declare (ignore this))
      (let* ((tz (arg 0 args))
             (offset (now-tz-offset tz))
             (ns (+ (now-epoch-ns) offset)))
        (multiple-value-bind (date time) (epoch-ns->iso-datetime ns)
          (make-temporal-plaindatetime realm date time))))

    ;; plainDateISO([timeZone]) -> the wall-clock date in the given zone.
    (def-method realm now "plainDateISO" 0 (this args)
      (declare (ignore this))
      (let* ((tz (arg 0 args))
             (offset (now-tz-offset tz))
             (ns (+ (now-epoch-ns) offset)))
        (multiple-value-bind (date time) (epoch-ns->iso-datetime ns)
          (declare (ignore time))
          (make-plain-date date "iso8601" realm))))

    ;; zonedDateTimeISO([timeZone]) -> the current instant as a ZonedDateTime in
    ;; the given zone (default the system zone, "UTC").
    (def-method realm now "zonedDateTimeISO" 0 (this args)
      (declare (ignore this))
      (let ((tz (arg 0 args)))
        (multiple-value-bind (tz-id offset)
            (if (js-undefined-p tz) (values "UTC" 0) (to-time-zone-identifier tz))
          (make-zoneddatetime realm (now-epoch-ns) tz-id offset "iso8601"))))

    ;; Hang Now on the Temporal namespace (non-enumerable, writable, configurable).
    (temporal-register realm "Now" now)))

(register-builtin-installer 'install-temporal-now)
