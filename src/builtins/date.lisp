;;;; builtins/date.lisp — Date (constructor, now, parse, UTC, get/set accessors, toISOString/toString/toJSON).
;;;; See array-iteration.lisp for the convention + available helpers.
;;;;
;;;; Timezone: we assume local == UTC (offset 0). getTimezoneOffset -> 0, and all
;;;; local get/set accessors alias the UTC ones. This passes the UTC-based tests
;;;; and the getTimezoneOffset()==0 assumption; genuinely local-TZ / DST tests are
;;;; out of scope.
(in-package #:shuttle)

;;; ---------------------------------------------------------------------------
;;; Time-value arithmetic (ECMAScript 21.4.1). All values are CL doubles or NaN.
;;; ---------------------------------------------------------------------------
(defconstant +ms-per-day+    86400000d0)
(defconstant +ms-per-hour+   3600000d0)
(defconstant +ms-per-minute+ 60000d0)
(defconstant +ms-per-second+ 1000d0)

(defun date-finite-p (n) (and (floatp n) (not (js-nan-p n)) (/= n *inf*) (/= n *-inf*)))

(defun %floor (x) (with-js-floats (ffloor x)))

(defun js-mod (a b)
  "Mathematical modulo returning a value with the sign of B (ECMAScript modulo)."
  (with-js-floats (- a (* (ffloor (/ a b)) b))))

;;; Day number and time-within-day
(defun day (tv) (if (date-finite-p tv) (%floor (/ tv +ms-per-day+)) *nan*))
(defun time-within-day (tv) (if (date-finite-p tv) (js-mod tv +ms-per-day+) *nan*))

;;; Year handling
(defun days-in-year (y)
  (if (not (date-finite-p y)) *nan*
      (cond ((/= (mod (truncate y) 4) 0) 365d0)
            ((/= (mod (truncate y) 100) 0) 366d0)
            ((/= (mod (truncate y) 400) 0) 365d0)
            (t 366d0))))
(defun day-from-year (y)
  (with-js-floats
    (+ (* 365d0 (- y 1970d0))
       (ffloor (/ (- y 1969d0) 4d0))
       (- (ffloor (/ (- y 1901d0) 100d0)))
       (ffloor (/ (- y 1601d0) 400d0)))))
(defun time-from-year (y) (* +ms-per-day+ (day-from-year y)))

(defun year-from-time (tv)
  "Find the year Y such that TimeFromYear(Y) <= tv < TimeFromYear(Y+1)."
  (if (not (date-finite-p tv))
      *nan*
      (let* ((d (day tv))
             (y (+ 1970d0 (%floor (/ d 365.2425d0)))))
        (loop while (> (day-from-year y) d) do (decf y))
        (loop while (<= (day-from-year (1+ y)) d) do (incf y))
        y)))

(defun in-leap-year-p (tv)
  (= (days-in-year (year-from-time tv)) 366d0))
(defun day-within-year (tv) (- (day tv) (day-from-year (year-from-time tv))))

(defun month-from-time (tv)
  (if (not (date-finite-p tv)) (return-from month-from-time *nan*))
  (let ((d (day-within-year tv)) (leap (if (in-leap-year-p tv) 1 0)))
    (cond ((< d 31) 0d0)
          ((< d (+ 59 leap)) 1d0)
          ((< d (+ 90 leap)) 2d0)
          ((< d (+ 120 leap)) 3d0)
          ((< d (+ 151 leap)) 4d0)
          ((< d (+ 181 leap)) 5d0)
          ((< d (+ 212 leap)) 6d0)
          ((< d (+ 243 leap)) 7d0)
          ((< d (+ 273 leap)) 8d0)
          ((< d (+ 304 leap)) 9d0)
          ((< d (+ 334 leap)) 10d0)
          (t 11d0))))

(defun date-from-time (tv)
  (if (not (date-finite-p tv)) (return-from date-from-time *nan*))
  (let ((d (day-within-year tv)) (leap (if (in-leap-year-p tv) 1 0)))
    (case (truncate (month-from-time tv))
      (0 (+ d 1d0))
      (1 (- d 30d0))
      (2 (- d (+ 58 leap)))
      (3 (- d (+ 89 leap)))
      (4 (- d (+ 119 leap)))
      (5 (- d (+ 150 leap)))
      (6 (- d (+ 180 leap)))
      (7 (- d (+ 211 leap)))
      (8 (- d (+ 242 leap)))
      (9 (- d (+ 272 leap)))
      (10 (- d (+ 303 leap)))
      (11 (- d (+ 333 leap))))))

(defun week-day (tv) (if (date-finite-p tv) (js-mod (+ (day tv) 4d0) 7d0) *nan*))

(defun hours-from-time (tv) (if (date-finite-p tv) (js-mod (%floor (/ tv +ms-per-hour+)) 24d0) *nan*))
(defun min-from-time (tv) (if (date-finite-p tv) (js-mod (%floor (/ tv +ms-per-minute+)) 60d0) *nan*))
(defun sec-from-time (tv) (if (date-finite-p tv) (js-mod (%floor (/ tv +ms-per-second+)) 60d0) *nan*))
(defun ms-from-time (tv) (if (date-finite-p tv) (js-mod tv 1000d0) *nan*))

(defun make-time (hour min sec ms)
  (if (and (date-finite-p hour) (date-finite-p min) (date-finite-p sec) (date-finite-p ms))
      (with-js-floats
        (+ (* (ftruncate hour) +ms-per-hour+)
           (* (ftruncate min) +ms-per-minute+)
           (* (ftruncate sec) +ms-per-second+)
           (ftruncate ms)))
      *nan*))

(defun make-day (year month date)
  (if (and (date-finite-p year) (date-finite-p month) (date-finite-p date))
      (with-js-floats
        (let* ((y (ftruncate year)) (m (ftruncate month)) (dt (ftruncate date))
               (ym (+ y (ffloor (/ m 12d0))))
               (mn (js-mod m 12d0)))
          (if (not (date-finite-p ym))
              *nan*
              (let* ((first-day (day-from-year ym))
                     (leap (if (= (days-in-year ym) 366d0) 1 0))
                     (mdays #(0 31 59 90 120 151 181 212 243 273 304 334))
                     (add (+ (aref mdays (truncate mn)) (if (>= (truncate mn) 2) leap 0)))
                     (dayno (+ first-day add (- dt 1d0))))
                dayno))))
      *nan*))

(defun make-date (day time)
  (if (and (date-finite-p day) (date-finite-p time))
      (with-js-floats (+ (* day +ms-per-day+) time))
      *nan*))

(defun time-clip (tv)
  (cond ((not (floatp tv)) *nan*)
        ((not (date-finite-p tv)) *nan*)
        ((> (abs tv) 8.64d15) *nan*)
        (t (with-js-floats
             (let ((r (ftruncate tv)))
               (if (zerop r) 0d0 r))))))

;;; ---------------------------------------------------------------------------
;;; String formatting
;;; ---------------------------------------------------------------------------
(defparameter +day-names+ #("Sun" "Mon" "Tue" "Wed" "Thu" "Fri" "Sat"))
(defparameter +month-names+ #("Jan" "Feb" "Mar" "Apr" "May" "Jun"
                              "Jul" "Aug" "Sep" "Oct" "Nov" "Dec"))

(defun pad2 (n) (format nil "~2,'0d" (truncate n)))
(defun pad3 (n) (format nil "~3,'0d" (truncate n)))

(defun year-string-4 (y)
  "At least four digits, signed for negatives (used by toString/toDateString)."
  (let ((yi (truncate y)))
    (if (minusp yi)
        (format nil "-~4,'0d" (- yi))
        (format nil "~4,'0d" yi))))

(defun year-string-iso (y)
  "ISO expanded-year form: 4 digits, or +/-6 digits when out of [0,9999]."
  (let ((yi (truncate y)))
    (cond ((and (>= yi 0) (<= yi 9999)) (format nil "~4,'0d" yi))
          ((minusp yi) (format nil "-~6,'0d" (- yi)))
          (t (format nil "+~6,'0d" yi)))))

(defun date-string (tv)
  (format nil "~a ~a ~a ~a"
          (aref +day-names+ (truncate (week-day tv)))
          (aref +month-names+ (truncate (month-from-time tv)))
          (pad2 (date-from-time tv))
          (year-string-4 (year-from-time tv))))

(defun time-string (tv)
  (format nil "~a:~a:~a GMT"
          (pad2 (hours-from-time tv)) (pad2 (min-from-time tv)) (pad2 (sec-from-time tv))))

(defun timezone-string (tv)
  ;; TimeZoneString: signed 4-digit offset + descriptive name. TimeString already
  ;; contributes the trailing " GMT", so this begins at the offset. Offset 0 (UTC).
  (declare (ignore tv))
  "+0000 (Coordinated Universal Time)")

(defun to-date-string-full (tv)
  (if (date-finite-p tv)
      (format nil "~a ~a~a" (date-string tv) (time-string tv) (timezone-string tv))
      "Invalid Date"))

(defun utc-string (tv)
  (if (date-finite-p tv)
      (format nil "~a, ~a ~a ~a ~a:~a:~a GMT"
              (aref +day-names+ (truncate (week-day tv)))
              (pad2 (date-from-time tv))
              (aref +month-names+ (truncate (month-from-time tv)))
              (year-string-4 (year-from-time tv))
              (pad2 (hours-from-time tv)) (pad2 (min-from-time tv)) (pad2 (sec-from-time tv)))
      "Invalid Date"))

(defun iso-string (tv)
  (format nil "~a-~a-~aT~a:~a:~a.~aZ"
          (year-string-iso (year-from-time tv))
          (pad2 (+ 1 (month-from-time tv)))
          (pad2 (date-from-time tv))
          (pad2 (hours-from-time tv))
          (pad2 (min-from-time tv))
          (pad2 (sec-from-time tv))
          (pad3 (ms-from-time tv))))

;;; ---------------------------------------------------------------------------
;;; Parsing (Date.parse). Returns a time value or NaN.
;;; ---------------------------------------------------------------------------
(defun %digits (s start count)
  "Parse exactly COUNT decimal digits from S at START; (values int next) or NIL."
  (when (<= (+ start count) (length s))
    (let ((v 0))
      (dotimes (i count)
        (let ((c (char s (+ start i))))
          (unless (digit-char-p c) (return-from %digits nil))
          (setf v (+ (* v 10) (digit-char-p c)))))
      (values v (+ start count)))))

(defun parse-iso-date (s)
  "Parse the ECMAScript Date Time String Format; return time value or NIL (not this form)."
  (let ((n (length s)) (i 0) (year nil) (year-sign 1)
        (month 1) (day 1) (hour 0) (minute 0) (second 0) (ms 0)
        (has-time nil) (tz-offset nil))
    (block parse
      (when (and (< i n) (member (char s i) '(#\+ #\-)))
        (setf year-sign (if (char= (char s i) #\-) -1 1))
        (incf i)
        (multiple-value-bind (y ni) (%digits s i 6)
          (unless y (return-from parse nil))
          ;; "-000000" (negative zero expanded year) is invalid -> NaN
          (when (and (= year-sign -1) (zerop y)) (return-from parse *nan*))
          (setf year (* year-sign y) i ni)))
      (unless year
        (multiple-value-bind (y ni) (%digits s i 4)
          (unless y (return-from parse nil))
          (setf year y i ni)))
      (when (and (< i n) (char= (char s i) #\-))
        (multiple-value-bind (m ni) (%digits s (1+ i) 2)
          (unless m (return-from parse nil))
          (setf month m i ni)
          (when (and (< i n) (char= (char s i) #\-))
            (multiple-value-bind (d ni2) (%digits s (1+ i) 2)
              (unless d (return-from parse nil))
              (setf day d i ni2)))))
      (when (and (< i n) (or (char= (char s i) #\T) (char= (char s i) #\Space)))
        (setf has-time t)
        (incf i)
        (multiple-value-bind (h ni) (%digits s i 2)
          (unless (and h (< i n)) (return-from parse nil))
          (setf hour h i ni))
        (unless (and (< i n) (char= (char s i) #\:)) (return-from parse nil))
        (multiple-value-bind (mi ni) (%digits s (1+ i) 2)
          (unless mi (return-from parse nil))
          (setf minute mi i ni))
        (when (and (< i n) (char= (char s i) #\:))
          (multiple-value-bind (sec ni) (%digits s (1+ i) 2)
            (unless sec (return-from parse nil))
            (setf second sec i ni))
          (when (and (< i n) (char= (char s i) #\.))
            (multiple-value-bind (msv ni) (%digits s (1+ i) 3)
              (unless msv (return-from parse nil))
              (setf ms msv i ni))))
        (cond ((and (< i n) (char= (char s i) #\Z))
               (setf tz-offset 0) (incf i))
              ((and (< i n) (member (char s i) '(#\+ #\-)))
               (let ((sign (if (char= (char s i) #\-) -1 1)))
                 (multiple-value-bind (oh ni) (%digits s (1+ i) 2)
                   (unless oh (return-from parse nil))
                   (setf i ni)
                   (when (and (< i n) (char= (char s i) #\:)) (incf i))
                   (multiple-value-bind (om ni2) (%digits s i 2)
                     (unless om (return-from parse nil))
                     (setf tz-offset (* sign (+ (* oh 60) om)) i ni2)))))))
      (unless (= i n) (return-from parse nil))
      (when (or (< month 1) (> month 12) (< day 1) (> day 31)
                (> hour 24) (> minute 59) (> second 59))
        (return-from parse *nan*))
      (let* ((yr (float year 1d0))
             (dayn (make-day yr (float (1- month) 1d0) (float day 1d0)))
             (time (make-time (float hour 1d0) (float minute 1d0) (float second 1d0) (float ms 1d0)))
             (tv (make-date dayn time)))
        (when (and has-time tz-offset)
          (setf tv (- tv (* tz-offset +ms-per-minute+))))
        (time-clip tv)))))

(defun uiop-split (s)
  "Split S on whitespace and commas."
  (let ((out '()) (cur (make-string-output-stream)))
    (loop for c across s do
      (if (member c '(#\Space #\Tab #\, #\Newline #\Return))
          (let ((tok (get-output-stream-string cur)))
            (when (> (length tok) 0) (push tok out))
            (setf cur (make-string-output-stream)))
          (write-char c cur)))
    (let ((tok (get-output-stream-string cur)))
      (when (> (length tok) 0) (push tok out)))
    (nreverse out)))

(defun month-name-index (str)
  (position str +month-names+ :test #'string-equal))

(defun parse-utc-string (s)
  "Best-effort parse of toUTCString form: 'Wed, 01 Jan 1970 00:00:00 GMT'."
  (let ((toks (uiop-split s)))
    (handler-case
        (when (>= (length toks) 6)
          (let* ((dd (parse-integer (nth 1 toks)))
                 (mon (month-name-index (nth 2 toks)))
                 (yr (parse-integer (nth 3 toks)))
                 (hms (nth 4 toks))
                 (colons (loop for c across hms count (char= c #\:))))
            (when (and mon (= colons 2))
              (let* ((cp1 (position #\: hms))
                     (cp2 (position #\: hms :from-end t))
                     (hh (parse-integer hms :end cp1))
                     (mm (parse-integer hms :start (1+ cp1) :end cp2))
                     (ss (parse-integer hms :start (1+ cp2))))
                (time-clip (make-date (make-day (float yr 1d0) (float mon 1d0) (float dd 1d0))
                                      (make-time (float hh 1d0) (float mm 1d0) (float ss 1d0) 0d0)))))))
      (error () nil))))

(defun parse-tostring-form (s)
  "Best-effort parse of toString form: 'Thu Jan 01 1970 00:00:00 GMT+0000 (...)'"
  (let ((toks (uiop-split s)))
    (handler-case
        (when (>= (length toks) 6)
          (let* ((mon (month-name-index (nth 1 toks)))
                 (dd (parse-integer (nth 2 toks)))
                 (yr (parse-integer (nth 3 toks)))
                 (hms (nth 4 toks))
                 (tz (nth 5 toks)))
            (when (and mon (>= (length hms) 8))
              (let* ((hh (parse-integer hms :end 2))
                     (mm (parse-integer hms :start 3 :end 5))
                     (ss (parse-integer hms :start 6 :end 8))
                     (off 0)
                     (pp (or (position #\+ tz) (position #\- tz))))
                (when pp
                  (let ((sign (if (char= (char tz pp) #\-) -1 1)))
                    (setf off (* sign (+ (* 60 (parse-integer tz :start (1+ pp) :end (+ pp 3)))
                                         (parse-integer tz :start (+ pp 3) :end (+ pp 5)))))))
                (time-clip
                 (- (make-date (make-day (float yr 1d0) (float mon 1d0) (float dd 1d0))
                               (make-time (float hh 1d0) (float mm 1d0) (float ss 1d0) 0d0))
                    (* off +ms-per-minute+)))))))
      (error () nil))))

(defun date-parse (s)
  (let ((s (string-trim '(#\Space #\Tab #\Newline #\Return) s)))
    (let ((iso (parse-iso-date s)))
      (if (numberp iso)
          iso
          (or (parse-utc-string s) (parse-tostring-form s) *nan*)))))

;;; ---------------------------------------------------------------------------
;;; Instance helpers
;;; ---------------------------------------------------------------------------
(defun date-tv (this)
  "Read [[DateValue]] from a Date instance (guard non-Date receivers)."
  (if (and (js-object-p this) (string= (js-object-class this) "Date"))
      (js-object-primitive this)
      (js-throw (make-native-error "TypeError" "this is not a Date object"))))

(defun set-date-tv (this v)
  (unless (and (js-object-p this) (string= (js-object-class this) "Date"))
    (js-throw (make-native-error "TypeError" "this is not a Date object")))
  (setf (js-object-primitive this) v)
  v)

(defun current-time-ms ()
  "Milliseconds since Unix epoch. Uses the CL clock if available."
  (with-js-floats
    (multiple-value-bind (sec usec) (ignore-errors (sb-ext:get-time-of-day))
      (if sec
          (+ (* (float sec 1d0) 1000d0) (float (floor usec 1000) 1d0))
          (* (- (float (get-universal-time) 1d0) 2208988800d0) 1000d0)))))

(defun ordinary-to-primitive (o hint)
  "OrdinaryToPrimitive with the given resolved hint (:string / :number)."
  (let ((order (if (eq hint :string) '("toString" "valueOf") '("valueOf" "toString"))))
    (dolist (m order (js-throw (make-native-error "TypeError" "Cannot convert object to primitive value")))
      (let ((fn (js-get o m)))
        (when (js-callable-p fn)
          (let ((r (js-call fn o '()))) (unless (js-object-p r) (return r))))))))

;;; ---------------------------------------------------------------------------
;;; install-date
;;; ---------------------------------------------------------------------------
(defun install-date (realm)
  (let* ((op (realm-object-proto realm))
         (dp (make-object :proto op :class "Object")))  ; Date.prototype is an ordinary object
    (labels ((new-date-object (nt tv)
               (let* ((proto (let ((p (and (js-object-p nt) (js-get nt "prototype"))))
                               (if (js-object-p p) p dp)))
                      (o (make-object :proto proto :class "Date")))
                 (setf (js-object-primitive o) tv)
                 o))
             (fields-tv (args)
               (let* ((y (to-number (arg 0 args)))
                      (m (if (>= (length args) 2) (to-number (arg 1 args)) 0d0))
                      (d (if (>= (length args) 3) (to-number (arg 2 args)) 1d0))
                      (h (if (>= (length args) 4) (to-number (arg 3 args)) 0d0))
                      (mi (if (>= (length args) 5) (to-number (arg 4 args)) 0d0))
                      (s (if (>= (length args) 6) (to-number (arg 5 args)) 0d0))
                      (ms (if (>= (length args) 7) (to-number (arg 6 args)) 0d0))
                      (yr (if (and (date-finite-p y) (<= 0 (with-js-floats (ftruncate y)) 99))
                              (+ 1900d0 (with-js-floats (ftruncate y)))
                              y)))
                 (time-clip (make-date (make-day yr m d) (make-time h mi s ms))))))
      (let ((ctor (native-function realm "Date"
                    (lambda (this args) (declare (ignore this args))
                      (to-date-string-full (time-clip (current-time-ms)))) 7)))
        (setf (js-object-construct ctor)
              (lambda (args nt)
                (cond
                  ((null args) (new-date-object nt (time-clip (current-time-ms))))
                  ((= (length args) 1)
                   (let* ((v (arg 0 args))
                          (tv (cond
                                ((and (js-object-p v) (string= (js-object-class v) "Date"))
                                 (time-clip (js-object-primitive v)))
                                (t (let ((prim (to-primitive v)))
                                     (if (stringp prim)
                                         (date-parse prim)
                                         (time-clip (to-number prim))))))))
                     (new-date-object nt tv)))
                  (t (new-date-object nt (fields-tv args))))))
        (def-value ctor "prototype" dp :writable nil :configurable nil)
        (def-value dp "constructor" ctor)

        ;; ---- statics ---------------------------------------------------
        (def-method realm ctor "now" 0 (this args)
          (time-clip (current-time-ms)))
        (def-method realm ctor "parse" 1 (this args)
          (date-parse (to-string (arg 0 args))))
        (def-method realm ctor "UTC" 7 (this args)
          (fields-tv args))

        ;; ---- getters ---------------------------------------------------
        (macrolet ((getter (name extractor)
                     `(def-method realm dp ,name 0 (this args)
                        (let ((tv (date-tv this)))
                          (if (date-finite-p tv) (,extractor tv) *nan*)))))
          (def-method realm dp "getTime" 0 (this args) (date-tv this))
          (def-method realm dp "valueOf" 0 (this args) (date-tv this))
          (getter "getFullYear" year-from-time)
          (getter "getUTCFullYear" year-from-time)
          (getter "getMonth" month-from-time)
          (getter "getUTCMonth" month-from-time)
          (getter "getDate" date-from-time)
          (getter "getUTCDate" date-from-time)
          (getter "getDay" week-day)
          (getter "getUTCDay" week-day)
          (getter "getHours" hours-from-time)
          (getter "getUTCHours" hours-from-time)
          (getter "getMinutes" min-from-time)
          (getter "getUTCMinutes" min-from-time)
          (getter "getSeconds" sec-from-time)
          (getter "getUTCSeconds" sec-from-time)
          (getter "getMilliseconds" ms-from-time)
          (getter "getUTCMilliseconds" ms-from-time))
        (def-method realm dp "getTimezoneOffset" 0 (this args)
          (let ((tv (date-tv this))) (if (date-finite-p tv) 0d0 *nan*)))

        ;; ---- setters ---------------------------------------------------
        (def-method realm dp "setTime" 1 (this args)
          ;; thisTimeValue validation (throws for non-Date) precedes ToNumber(arg).
          (date-tv this)
          (set-date-tv this (time-clip (to-number (arg 0 args)))))

        ;; time-portion setters. INDEX (0=hours,1=min,2=sec,3=ms) is the leading
        ;; component this method sets. Slots < INDEX keep the existing value; the
        ;; slot at INDEX (arg 0) and following supplied args override.
        (flet ((set-time-part (this args index)
                 ;; Read the time value (t) FIRST (thisTimeValue), then coerce the
                 ;; args in order (observable via valueOf). The leading slot (at
                 ;; INDEX, i.e. arg 0) is ALWAYS ToNumber'd — even with zero args
                 ;; ToNumber(undefined)=NaN. Subsequent slots are coerced only when
                 ;; explicitly supplied. Per spec, if t is NaN the method returns
                 ;; NaN WITHOUT updating [[DateValue]] (a valueOf side-effect that
                 ;; set the date must survive).
                 (let* ((tv (date-tv this))
                        (supplied (make-array 4 :initial-element nil)))
                   ;; leading slot always coerced (arg 0 -> undefined when absent)
                   (setf (aref supplied index) (to-number (arg 0 args)))
                   (loop for j from (1+ index) below 4
                         for ai = (- j index)
                         while (< ai (length args))
                         do (setf (aref supplied j) (to-number (arg ai args))))
                   (if (not (date-finite-p tv))
                       *nan*
                       (let* ((h  (or (aref supplied 0) (hours-from-time tv)))
                              (mi (or (aref supplied 1) (min-from-time tv)))
                              (s  (or (aref supplied 2) (sec-from-time tv)))
                              (ms (or (aref supplied 3) (ms-from-time tv))))
                         (set-date-tv this
                                      (time-clip (make-date (day tv) (make-time h mi s ms)))))))))
          (def-method realm dp "setMilliseconds" 1 (this args) (set-time-part this args 3))
          (def-method realm dp "setUTCMilliseconds" 1 (this args) (set-time-part this args 3))
          (def-method realm dp "setSeconds" 2 (this args) (set-time-part this args 2))
          (def-method realm dp "setUTCSeconds" 2 (this args) (set-time-part this args 2))
          (def-method realm dp "setMinutes" 3 (this args) (set-time-part this args 1))
          (def-method realm dp "setUTCMinutes" 3 (this args) (set-time-part this args 1))
          (def-method realm dp "setHours" 4 (this args) (set-time-part this args 0))
          (def-method realm dp "setUTCHours" 4 (this args) (set-time-part this args 0)))

        ;; date-portion setters: setDate/setMonth/setFullYear
        (flet ((set-date-part (this args which)
                 ;; Read t FIRST (thisTimeValue). Then coerce every supplied arg in
                 ;; source order (observable via valueOf); leading slots are always
                 ;; coerced. setFullYear: if t is NaN use +0 as the time base and
                 ;; still write. setDate/setMonth: if t is NaN, return NaN WITHOUT
                 ;; writing [[DateValue]] (a valueOf side-effect must survive).
                 (let* ((tv (date-tv this))
                        (base (if (and (eq which :year) (not (date-finite-p tv))) 0d0 tv))
                        ;; Coerce supplied args left-to-right regardless of NaN base.
                        (a-year  (when (eq which :year) (to-number (arg 0 args))))
                        (a-mon   (cond ((eq which :year) (when (>= (length args) 2) (to-number (arg 1 args))))
                                       ((eq which :month) (to-number (arg 0 args)))
                                       (t nil)))
                        (a-date  (cond ((eq which :year) (when (>= (length args) 3) (to-number (arg 2 args))))
                                       ((eq which :month) (when (>= (length args) 2) (to-number (arg 1 args))))
                                       (t (to-number (arg 0 args))))))
                   (if (and (not (eq which :year)) (not (date-finite-p tv)))
                       ;; t is NaN and this is setDate/setMonth: don't write.
                       *nan*
                       (let* ((yr (if (eq which :year) a-year (year-from-time base)))
                              (mo (or a-mon (month-from-time base)))
                              (dt (or a-date (date-from-time base)))
                              (time (time-within-day base)))
                         (set-date-tv this (time-clip (make-date (make-day yr mo dt) time))))))))
          (def-method realm dp "setDate" 1 (this args) (set-date-part this args :date))
          (def-method realm dp "setUTCDate" 1 (this args) (set-date-part this args :date))
          (def-method realm dp "setMonth" 2 (this args) (set-date-part this args :month))
          (def-method realm dp "setUTCMonth" 2 (this args) (set-date-part this args :month))
          (def-method realm dp "setFullYear" 3 (this args) (set-date-part this args :year))
          (def-method realm dp "setUTCFullYear" 3 (this args) (set-date-part this args :year)))

        ;; ---- string conversions ---------------------------------------
        (def-method realm dp "toISOString" 0 (this args)
          (let ((tv (date-tv this)))
            (unless (date-finite-p tv)
              (js-throw (make-native-error "RangeError" "Invalid time value")))
            (iso-string tv)))
        (def-method realm dp "toJSON" 1 (this args)
          (let* ((o (to-object this))
                 (tv (to-primitive o :number)))
            (if (and (floatp tv) (not (date-finite-p tv)))
                *null*
                (let ((fn (js-get o "toISOString")))
                  (unless (js-callable-p fn)
                    (js-throw (make-native-error "TypeError" "toISOString is not callable")))
                  (js-call fn o '())))))
        (def-method realm dp "toString" 0 (this args)
          (to-date-string-full (date-tv this)))
        (def-method realm dp "toDateString" 0 (this args)
          (let ((tv (date-tv this)))
            (if (date-finite-p tv) (date-string tv) "Invalid Date")))
        (def-method realm dp "toTimeString" 0 (this args)
          (let ((tv (date-tv this)))
            (if (date-finite-p tv)
                (format nil "~a~a" (time-string tv) (timezone-string tv))
                "Invalid Date")))
        (def-method realm dp "toUTCString" 0 (this args)
          (utc-string (date-tv this)))
        ;; Annex B: Date.prototype.toGMTString is the *same* function object as toUTCString.
        (put dp "toGMTString" (js-get dp "toUTCString")
             :enumerable nil :writable t :configurable t)
        (def-method realm dp "toLocaleString" 0 (this args)
          (to-date-string-full (date-tv this)))
        (def-method realm dp "toLocaleDateString" 0 (this args)
          (let ((tv (date-tv this))) (if (date-finite-p tv) (date-string tv) "Invalid Date")))
        (def-method realm dp "toLocaleTimeString" 0 (this args)
          (let ((tv (date-tv this)))
            (if (date-finite-p tv) (format nil "~a~a" (time-string tv) (timezone-string tv)) "Invalid Date")))

        ;; ---- @@toPrimitive --------------------------------------------
        (when *symbol-to-primitive*
          (put dp *symbol-to-primitive*
               (native-function realm "[Symbol.toPrimitive]"
                 (lambda (this args)
                   (unless (js-object-p this)
                     (js-throw (make-native-error "TypeError" "not an object")))
                   (let* ((hint (arg 0 args))
                          (h (cond ((and (stringp hint) (string= hint "string")) :string)
                                   ((and (stringp hint) (string= hint "default")) :string)
                                   ((and (stringp hint) (string= hint "number")) :number)
                                   (t (js-throw (make-native-error "TypeError" "invalid hint"))))))
                     (ordinary-to-primitive this h)))
                 1)
               :enumerable nil :writable nil :configurable t))

        ;; ---- Annex B: getYear / setYear -------------------------------
        (def-method realm dp "getYear" 0 (this args)
          (let ((tv (date-tv this)))
            (if (date-finite-p tv) (- (year-from-time tv) 1900d0) *nan*)))
        (def-method realm dp "setYear" 1 (this args)
          (let* ((tv (date-tv this))
                 (t0 (if (date-finite-p tv) tv 0d0))
                 (y (to-number (arg 0 args))))
            (if (js-nan-p y)
                (set-date-tv this *nan*)
                (let* ((yi (with-js-floats (ftruncate y)))
                       (yr (if (<= 0 yi 99) (+ 1900d0 yi) y)))
                  (set-date-tv this
                               (time-clip (make-date (make-day yr (month-from-time t0) (date-from-time t0))
                                                     (time-within-day t0))))))))

        (define-global realm "Date" ctor)
        ;; Global constructors are non-enumerable data properties.
        (put (realm-global realm) "Date" ctor :enumerable nil :writable t :configurable t)))))

(register-builtin-installer 'install-date)
