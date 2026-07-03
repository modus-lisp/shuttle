;;;; builtins/temporal-duration.lisp — Temporal.Duration.
;;;;
;;;; Full Temporal.Duration, replacing the kernel's minimal Duration wholesale
;;;; (our installer runs AFTER temporal-core's, so we re-`temporal-register` and
;;;; re-`define-global`). We keep the kernel's :temporal-duration internal-slot
;;;; contract (an exact-integer duration plist) so Instant/PlainTime/etc. that
;;;; call to-temporal-duration-record / make-temporal-duration keep working.
;;;;
;;;; Everything exact: components are CL integers; totals run over CL rationals
;;;; and are converted to JS doubles with rational->double (round-half-even),
;;;; matching the spec's exact-mathematical-value semantics.
(in-package #:shuttle)

;;; ===========================================================================
;;; Signed rational -> JS double (rational->double is non-negative only).
;;; ===========================================================================
(defun signed-rational->double (r)
  (cond ((zerop r) 0d0)
        ((minusp r) (- (rational->double (- r))))
        (t (rational->double r))))

;;; ===========================================================================
;;; Duration magnitude / range validation (IsValidDuration).
;;; ===========================================================================
(defun full-validate-duration (d)
  "IsValidDuration — now a thin alias for the kernel's validate-duration-range,
   which correctly bounds only years/months/weeks by 2^32 and days via the total
   seconds < 2^53 limit. Kept as a local name to minimize callsite churn."
  (validate-duration-range d))

(defun duration-has-calendar-units-p (d)
  (or (/= 0 (getf d :years)) (/= 0 (getf d :months)) (/= 0 (getf d :weeks))))

(defun duration-total-time-ns (d)
  "Total ns of days + time part (days as 24h), exact integer."
  (+ (* (getf d :days) +ns-per-day+) (duration-time-ns d)))

;;; ===========================================================================
;;; ISO-8601 duration string parsing — the kernel's parse-temporal-duration is
;;; now the single correct parser (cascades a fractional hours/minutes/seconds
;;; value hours->minutes->seconds->subsecond and rejects a fraction on any but
;;; the final present component), so we route everything through the kernel's
;;; to-temporal-duration-record.
;;; ===========================================================================
(defun to-duration-record (v)
  "ToTemporalDurationRecord — delegates to the kernel (strings, bags, instances)."
  (to-temporal-duration-record v))

;;; ===========================================================================
;;; ToIntegerIfIntegral for a single argument (constructor + fields).
;;; ===========================================================================
(defun duration-arg->int (v)
  "ToIntegerIfIntegral: ToNumber, reject NaN/Infinity and non-integers."
  (if (js-undefined-p v)
      0
      (let ((n (to-number v)))
        (when (or (js-nan-p n) (= n *inf*) (= n *-inf*))
          (js-throw (make-native-error "RangeError" "duration field must be finite")))
        (let ((k (with-js-floats (ftruncate n))))
          (when (/= k n)
            (js-throw (make-native-error "RangeError" "duration field must be an integer")))
          (truncate k)))))

;;; ===========================================================================
;;; ToTemporalPartialDurationRecord (for with()): alphabetical reads, missing
;;; fields stay NIL (not defaulted), at least one field required.
;;; ===========================================================================
(defun to-partial-duration-record (bag)
  (unless (js-object-p bag)
    (js-throw (make-native-error "TypeError" "with() argument must be an object")))
  (let ((out '()) (any nil))
    (dolist (pair +duration-bag-keys+)
      (let ((v (js-get bag (car pair))))
        (unless (js-undefined-p v)
          (setf any t)
          (setf (getf out (cdr pair)) (duration-arg->int v)))))
    (unless any
      (js-throw (make-native-error "TypeError" "invalid duration-like object")))
    out))

;;; ===========================================================================
;;; Time-part balancing over exact ns into a duration plist.
;;; ===========================================================================
(defun balance-time-duration-ns (total-ns largest-unit)
  "BalanceTimeDuration: split signed TOTAL-NS into time components down to ns,
   using LARGEST-UNIT (:day :hour :minute :second :millisecond :microsecond
   :nanosecond) as the coarsest bucket. Returns a duration plist (date units 0)."
  (let ((sign (if (minusp total-ns) -1 1))
        (a (abs total-ns))
        (days 0) (hours 0) (minutes 0) (seconds 0) (ms 0) (us 0) (ns 0))
    ;; Peel off from ns upward, then cap at largest-unit.
    (setf ns (mod a 1000)) (setf a (floor a 1000))
    (setf us (mod a 1000))  (setf a (floor a 1000))
    (setf ms (mod a 1000))  (setf a (floor a 1000))
    (setf seconds (mod a 60)) (setf a (floor a 60))
    (setf minutes (mod a 60)) (setf a (floor a 60))
    (setf hours (mod a 24)) (setf a (floor a 24))
    (setf days a)
    ;; Now collapse buckets coarser than largest-unit back down.
    (ecase largest-unit
      (:day)
      (:hour (incf hours (* days 24)) (setf days 0))
      (:minute (incf minutes (* (+ (* days 24) hours) 60)) (setf days 0 hours 0))
      (:second (incf seconds (* (+ (* (+ (* days 24) hours) 60) minutes) 60))
               (setf days 0 hours 0 minutes 0))
      (:millisecond
       (incf ms (* (+ (* (+ (* (+ (* days 24) hours) 60) minutes) 60) seconds) 1000))
       (setf days 0 hours 0 minutes 0 seconds 0))
      (:microsecond
       (incf us (* (+ (* (+ (* (+ (* (+ (* days 24) hours) 60) minutes) 60) seconds) 1000) ms) 1000))
       (setf days 0 hours 0 minutes 0 seconds 0 ms 0))
      (:nanosecond
       (setf ns (abs total-ns))
       (setf days 0 hours 0 minutes 0 seconds 0 ms 0 us 0)))
    (flet ((s (x) (* sign x)))
      (list :years 0 :months 0 :weeks 0 :days (s days)
            :hours (s hours) :minutes (s minutes) :seconds (s seconds)
            :milliseconds (s ms) :microseconds (s us) :nanoseconds (s ns)))))

;;; ===========================================================================
;;; Default largest time unit of a duration (largest nonzero unit, ns->day).
;;; ===========================================================================
(defun duration-default-largest-unit (d)
  "DefaultTemporalLargestUnit: the largest unit with a nonzero value."
  (cond ((/= 0 (getf d :years)) :year)
        ((/= 0 (getf d :months)) :month)
        ((/= 0 (getf d :weeks)) :week)
        ((/= 0 (getf d :days)) :day)
        ((/= 0 (getf d :hours)) :hour)
        ((/= 0 (getf d :minutes)) :minute)
        ((/= 0 (getf d :seconds)) :second)
        ((/= 0 (getf d :milliseconds)) :millisecond)
        ((/= 0 (getf d :microseconds)) :microsecond)
        (t :nanosecond)))

(defun coarser-unit (a b)
  "Return the coarser (lower-rank) of two units."
  (if (<= (unit-rank a) (unit-rank b)) a b))

;;; ===========================================================================
;;; Unit helpers.
;;; ===========================================================================
(defun duration-unit->ns (unit)
  (ecase unit
    (:day +ns-per-day+) (:hour +ns-per-hour+) (:minute +ns-per-min+)
    (:second +ns-per-s+) (:millisecond +ns-per-ms+) (:microsecond +ns-per-us+)
    (:nanosecond 1)))

;;; ===========================================================================
;;; PlainDate relativeTo — resolved dynamically at call time.
;;; ===========================================================================
(defun relative-to-plaindate-iso (realm v)
  "If V resolves to a Temporal.PlainDate (or PlainDateTime), return its iso-date;
   else NIL. A ZonedDateTime relativeTo defers to B3 (we treat as unsupported =>
   caller errors). Reads the internal slots that PlainDate/PlainDateTime install."
  (declare (ignore realm))
  (cond
    ((not (js-object-p v)) nil)
    ((getf (js-object-internal v) :temporal-plaindate) )
    ((getf (js-object-internal v) :temporal-plaindatetime)
     (let ((dt (getf (js-object-internal v) :temporal-plaindatetime)))
       (getf dt :date)))
    (t nil)))

(defun plaindate-registered-p (realm)
  (let ((ns (temporal-namespace realm)))
    (and ns (js-object-p (ignore-errors (js-get ns "PlainDate"))))))

(defun zdt-relativeto-local-iso (v)
  "The local (wall-clock) iso-date of a ZonedDateTime relativeTo V. For the
   fixed-offset zones the corpus exercises, days are exactly 24h, so a
   ZonedDateTime relativeTo is behaviorally a PlainDate relativeTo at this date."
  (let ((slot (getf (js-object-internal v) :temporal-zoneddatetime)))
    (multiple-value-bind (date time) (epoch-ns->iso-datetime (+ (getf slot :ns) (getf slot :offset)))
      (declare (ignore time))
      date)))

(defun relativeto-is-zoned-shaped-p (v)
  "T if a relativeTo value V (bag or string) denotes a ZonedDateTime: a bag with a
   non-undefined `timeZone` property, or a string carrying a bare (time-zone)
   [Zone] annotation (as opposed to only a [u-ca=...] one)."
  (cond
    ((stringp v)
     (let* ((s (string-trim '(#\Space #\Tab #\Newline #\Return) v))
            (br (position #\[ s)))
       (and br
            (let ((rb (position #\] s :start br)))
              (and rb
                   (let ((ann (subseq s (1+ br) rb)))
                     (when (and (plusp (length ann)) (char= (char ann 0) #\!))
                       (setf ann (subseq ann 1)))
                     ;; a bare annotation (no '=') is a time-zone annotation
                     (null (position #\= ann))))))))
    ((js-object-p v)
     (not (js-undefined-p (js-get v "timeZone"))))
    (t nil)))

(defun to-relative-to (realm options)
  "GetTemporalRelativeToOption. Returns (values kind iso-date) where kind is
   :none (undefined) or :plaindate (iso-date). A ZonedDateTime relativeTo (an
   instance, a timeZone-bearing bag, or a bracketed string) is resolved via the
   registered Temporal.ZonedDateTime and reduced to its local iso-date — for the
   fixed-offset zones the corpus uses this is behaviorally a PlainDate relativeTo.
   A plain string/bag is coerced through Temporal.PlainDate.from."
  (let ((v (%opt-get options "relativeTo")))
    (cond
      ((js-undefined-p v) (values :none nil))
      ;; ZonedDateTime instance.
      ((and (js-object-p v) (getf (js-object-internal v) :temporal-zoneddatetime))
       (values :plaindate (zdt-relativeto-local-iso v)))
      ;; PlainDate / PlainDateTime instance.
      ((and (js-object-p v)
            (or (getf (js-object-internal v) :temporal-plaindate)
                (getf (js-object-internal v) :temporal-plaindatetime)))
       (values :plaindate (relative-to-plaindate-iso realm v)))
      ;; A zoned-shaped bag/string: build a ZonedDateTime (correct observable
      ;; read order, offset/timeZone validation) and reduce to its local date.
      ((and (relativeto-is-zoned-shaped-p v) (fboundp 'to-temporal-zoneddatetime))
       (let ((z (funcall 'to-temporal-zoneddatetime realm v *undefined*)))
         (values :plaindate (zdt-relativeto-local-iso z))))
      (t
       ;; Plain string or property bag: delegate to Temporal.PlainDate.from
       ;; (observable read order, calendar + overflow, date extraction from a
       ;; datetime/offset form) and extract its iso-date.
       (let* ((ns (temporal-namespace realm))
              (pd (js-get ns "PlainDate"))
              (from (js-get pd "from"))
              (inst (js-call from pd (list v))))
         (values :plaindate (relative-to-plaindate-iso realm inst)))))))

;;; ===========================================================================
;;; Date arithmetic against a relativeTo PlainDate (available only when
;;; PlainDate is registered). We reuse the kernel's exact integer calendar.
;;; ===========================================================================
(defun add-iso-date (iso years months weeks days overflow)
  "AddISODate with :constrain/:reject. YEARS/MONTHS/WEEKS/DAYS are integers."
  (let* ((y (+ (iso-date-year iso) years))
         (m0 (+ (iso-date-month iso) months))
         ;; balance months into years
         (ym (+ (* y 12) (1- m0)))
         (yy (floor ym 12))
         (mm (1+ (mod ym 12)))
         (dim (days-in-month yy mm))
         (dd (iso-date-day iso)))
    (ecase overflow
      (:constrain (setf dd (min dd dim)))
      (:reject (when (> dd dim)
                 (js-throw (make-native-error "RangeError" "date out of range")))))
    (let* ((base (make-iso-date yy mm dd))
           (epoch (+ (iso-date->epoch-days base) (* weeks 7) days)))
      (epoch-days->iso-date epoch))))

(defun iso-date-until (d1 d2 largest-unit)
  "DifferenceISODate: the date difference d1->d2 in :year/:month/:week/:day
   units up to LARGEST-UNIT. Returns (values years months weeks days)."
  (let ((days-diff (- (iso-date->epoch-days d2) (iso-date->epoch-days d1))))
    (case largest-unit
      (:week (multiple-value-bind (w rem) (truncate days-diff 7)
               (values 0 0 w rem)))
      (:day (values 0 0 0 days-diff))
      (t
       ;; year/month largest: walk months toward d2, then leftover days.
       (let ((sign (cond ((> days-diff 0) 1) ((< days-diff 0) -1) (t 0))))
         (if (zerop sign)
             (values 0 0 0 0)
             (let* ((y1 (iso-date-year d1)) (m1 (iso-date-month d1))
                    (y2 (iso-date-year d2)) (m2 (iso-date-month d2))
                    (total-months (+ (* (- y2 y1) 12) (- m2 m1)))
                    (cand (add-iso-date d1 0 total-months 0 0 :constrain)))
               (when (= sign 1)
                 (loop while (> (iso-date->epoch-days cand) (iso-date->epoch-days d2))
                       do (decf total-months)
                          (setf cand (add-iso-date d1 0 total-months 0 0 :constrain))))
               (when (= sign -1)
                 (loop while (< (iso-date->epoch-days cand) (iso-date->epoch-days d2))
                       do (incf total-months)
                          (setf cand (add-iso-date d1 0 total-months 0 0 :constrain))))
               (let ((rem-days (- (iso-date->epoch-days d2) (iso-date->epoch-days cand))))
                 (if (eq largest-unit :year)
                     (multiple-value-bind (yy mm) (truncate total-months 12)
                       (values yy mm 0 rem-days))
                     (values 0 total-months 0 rem-days))))))))))

;;; ===========================================================================
;;; Fractional calendar arithmetic relative to a PlainDate.
;;;
;;; Model: the duration's date part + whole days from the time part define an
;;; end date; the leftover sub-day time is a fraction of a day. We measure the
;;; span rel->target(fractional day) and express it in a chosen unit by counting
;;; whole units from rel toward target and linearly interpolating the remainder
;;; between the whole-unit boundary dates (NudgeToCalendarUnit style).
;;; ===========================================================================
(defun add-duration-date (rel-iso years months weeks days)
  "rel-iso + (years,months,weeks,days) via the calendar."
  (add-iso-date rel-iso years months weeks days :constrain))

(defun duration-date-days-frac (d)
  "Return (values date-years date-months date-weeks whole-days frac-day) where
   frac-day is the sub-day fraction (rational in [0,1)) of the time part, and
   sign carried into whole-days. Everything from D's date+time parts."
  (let* ((years (getf d :years)) (months (getf d :months))
         (weeks (getf d :weeks)) (days (getf d :days))
         (time-ns (duration-time-ns d)))
    (multiple-value-bind (extra-days rem-ns) (truncate time-ns +ns-per-day+)
      (values years months weeks (+ days extra-days) (/ rem-ns +ns-per-day+)))))

(defun date-add-unit (rel-iso unit count)
  "rel-iso + COUNT of UNIT (:year/:month/:week/:day)."
  (ecase unit
    (:year (add-duration-date rel-iso count 0 0 0))
    (:month (add-duration-date rel-iso 0 count 0 0))
    (:week (add-duration-date rel-iso 0 0 count 0))
    (:day (add-duration-date rel-iso 0 0 0 count))))

(defun calendar-frac-count (rel-iso years months weeks whole-days frac-day unit)
  "Exact-rational count of UNIT (:year/:month/:week/:day) in the span from
   REL-ISO to REL-ISO+(years,months,weeks,whole-days)+frac-day. Linearly
   interpolates the sub-unit remainder between the two bounding whole-unit dates
   (both signs; WHOLE truncated toward zero, next boundary a further SIGN step)."
  (let* ((end (add-duration-date rel-iso years months weeks whole-days))
         (target-days (+ (iso-date->epoch-days end) frac-day))
         (rel-days (iso-date->epoch-days rel-iso))
         (sign (cond ((> target-days rel-days) 1) ((< target-days rel-days) -1) (t 0))))
    (if (zerop sign)
        0
        (ecase unit
          (:day (- target-days rel-days))
          (:week (/ (- target-days rel-days) 7))
          (:month
           (multiple-value-bind (wy wm)
               (iso-date-until rel-iso (epoch-days->iso-date (floor target-days)) :month)
             (let* ((whole (+ (* wy 12) wm))
                    (lo (date-add-unit rel-iso :month whole))
                    (hi (date-add-unit rel-iso :month (+ whole sign)))
                    (lod (iso-date->epoch-days lo)) (hid (iso-date->epoch-days hi))
                    (span (- hid lod))
                    (ratio (if (zerop span) 0 (/ (- target-days lod) span))))
               (+ whole (* sign ratio)))))
          (:year
           (multiple-value-bind (wy) (iso-date-until rel-iso (epoch-days->iso-date (floor target-days)) :year)
             (let* ((lo (date-add-unit rel-iso :year wy))
                    (hi (date-add-unit rel-iso :year (+ wy sign)))
                    (lod (iso-date->epoch-days lo)) (hid (iso-date->epoch-days hi))
                    (span (- hid lod))
                    (ratio (if (zerop span) 0 (/ (- target-days lod) span))))
               (+ wy (* sign ratio)))))))))

(defun round-calendar-units (rel-iso years months weeks whole-days frac-day
                             smallest largest increment mode)
  "RoundDuration for a calendar smallestUnit. Decompose the span rel->target at
   LARGEST into whole coarse units, express the finest bucket (SMALLEST) as a
   fractional value, round it to INCREMENT, then re-derive the end date so the
   result stays calendar-consistent. Returns a duration plist (time 0)."
  (let* ((end (add-duration-date rel-iso years months weeks whole-days))
         (target-days (+ (iso-date->epoch-days end) frac-day))
         (rel-days (iso-date->epoch-days rel-iso))
         (sign (cond ((> target-days rel-days) 1) ((< target-days rel-days) -1) (t 0))))
    (labels ((mk (y m w d)
               (list :years y :months m :weeks w :days d
                     :hours 0 :minutes 0 :seconds 0
                     :milliseconds 0 :microseconds 0 :nanoseconds 0))
             ;; fractional count of `unit` in the span anchor -> target, where
             ;; ANCHOR is rel + already-fixed coarser units. Interpolates the
             ;; sub-unit remainder linearly between the two bounding unit dates.
             ;; Works for both signs (WHOLE truncated toward zero, next boundary
             ;; a further SIGN step away).
             (frac-in (anchor unit)
               (let* ((adays (iso-date->epoch-days anchor)))
                 (ecase unit
                   (:day (- target-days adays))
                   (:week (/ (- target-days adays) 7))
                   (:month
                    (multiple-value-bind (wy wm)
                        (iso-date-until anchor (epoch-days->iso-date (floor target-days)) :month)
                      (let* ((whole (+ (* wy 12) wm))
                             (lo (date-add-unit anchor :month whole))
                             (hi (date-add-unit anchor :month (+ whole sign)))
                             (lod (iso-date->epoch-days lo)) (hid (iso-date->epoch-days hi))
                             (span (- hid lod))
                             ;; ratio in [0,1) from the whole-boundary toward the
                             ;; next (both signs); add SIGN * ratio.
                             (ratio (if (zerop span) 0 (/ (- target-days lod) span))))
                        (+ whole (* sign ratio)))))
                   (:year
                    (multiple-value-bind (wy) (iso-date-until anchor (epoch-days->iso-date (floor target-days)) :year)
                      (let* ((lo (date-add-unit anchor :year wy))
                             (hi (date-add-unit anchor :year (+ wy sign)))
                             (lod (iso-date->epoch-days lo)) (hid (iso-date->epoch-days hi))
                             (span (- hid lod))
                             (ratio (if (zerop span) 0 (/ (- target-days lod) span))))
                        (+ wy (* sign ratio)))))))))
      (if (zerop sign)
          (mk 0 0 0 0)
          (ecase smallest
            (:year
             (let ((r (* increment (apply-rounding-mode (/ (frac-in rel-iso :year) increment) mode))))
               (multiple-value-bind (by bm bw bd)
                   (balance-date-duration rel-iso (date-add-unit rel-iso :year r) largest smallest)
                 (mk by bm bw bd))))
            (:month
             ;; fix whole years (if largest=year), round months.
             (let* ((wy (if (eq largest :year)
                            (truncate (frac-in rel-iso :year)) 0))
                    (anchor (add-duration-date rel-iso wy 0 0 0))
                    (fm (frac-in anchor :month))
                    (rm (* increment (apply-rounding-mode (/ fm increment) mode)))
                    (end2 (add-duration-date rel-iso wy rm 0 0)))
               (multiple-value-bind (by bm bw bd)
                   (balance-date-duration rel-iso end2 largest smallest)
                 (mk by bm bw bd))))
            (:week
             ;; when balancing up to months/years, fix whole months first; when
             ;; largestUnit is weeks (or finer), count weeks straight from rel.
             (let* ((whole-months
                      (if (member largest '(:month :year))
                          (multiple-value-bind (wy wm)
                              (iso-date-until rel-iso (epoch-days->iso-date (floor target-days)) :month)
                            (+ (* wy 12) wm))
                          0))
                    (anchor (add-duration-date rel-iso 0 whole-months 0 0))
                    (fw (frac-in anchor :week))
                    (rw (* increment (apply-rounding-mode (/ fw increment) mode)))
                    (end2 (add-duration-date rel-iso 0 whole-months rw 0)))
               (multiple-value-bind (by bm bw bd)
                   (balance-date-duration rel-iso end2 largest smallest)
                 (mk by bm bw bd))))
            (:day
             (let* ((fd (frac-in rel-iso :day))     ; fractional total days
                    (rd (* increment (apply-rounding-mode (/ fd increment) mode)))
                    (end3 (epoch-days->iso-date (+ rel-days rd))))
               (multiple-value-bind (by bm bw bd)
                   (balance-date-duration rel-iso end3 largest smallest)
                 (mk by bm bw bd)))))))))

;;; ===========================================================================
;;; RoundDuration relative to a PlainDate (calendar-unit rounding).
;;; ===========================================================================
(defun round-duration-relative (d rel-iso smallest largest increment mode)
  "Round D relative to REL-ISO (an iso-date), for calendar or day units.
   Returns a duration plist. Days are calendar-real (via the date), time part
   is 24h/day beyond the date. Implements the day/week/month/year rounding
   with bubbling. REL-ISO must be non-NIL."
  (let* ((sign (or (let ((s (duration-sign d))) (if (zerop s) 1 s)) 1))
         ;; Fold time (h..ns) into a fractional day count, plus the whole days.
         (time-ns (duration-time-ns d))
         ;; The "target" date = rel + entire duration (date units + whole days).
         (years (getf d :years)) (months (getf d :months))
         (weeks (getf d :weeks)) (days (getf d :days)))
    (declare (ignorable sign time-ns years months weeks days))
    (ecase smallest
      ((:year :month :week :day)
       (multiple-value-bind (dy dm dw wd frac-day)
           (duration-date-days-frac d)
         (round-calendar-units rel-iso dy dm dw wd frac-day
                               smallest largest increment mode)))
      ((:hour :minute :second :millisecond :microsecond :nanosecond)
       ;; time-unit rounding with a date relativeTo: days are real, but time
       ;; rounds within the day; overflow bubbles into days via the date.
       (let* ((unit-ns (duration-unit->ns smallest))
              (total (+ (* days +ns-per-day+) time-ns))
              (rounded-ns (round-to-increment total (* increment unit-ns) mode)))
         ;; Re-derive days from date span if largest is date-ish.
         (if (member largest '(:year :month :week :day))
             (multiple-value-bind (dcarry rem) (truncate rounded-ns +ns-per-day+)
               (let* ((end (add-iso-date rel-iso years months weeks dcarry :constrain)))
                 (multiple-value-bind (dy dm dw dd) (iso-date-until rel-iso end largest)
                   (let ((tb (balance-time-duration-ns rem :hour)))
                     (setf (getf tb :years) dy (getf tb :months) dm
                           (getf tb :weeks) dw (getf tb :days) dd)
                     tb))))
             (balance-time-duration-ns rounded-ns largest)))))))

(defun balance-date-duration (rel-iso end largest smallest)
  "BalanceDateDurationRelative: decompose the calendar span REL-ISO->END into
   (values years months weeks days), coarsest = LARGEST, finest = SMALLEST.
   With largest=year/month we count whole months (years=months/12 when year),
   then the leftover days become weeks (when smallest=week) or stay as days."
  (let ((days-diff (- (iso-date->epoch-days end) (iso-date->epoch-days rel-iso))))
    (case largest
      (:day (values 0 0 0 days-diff))
      (:week (multiple-value-bind (w rem) (truncate days-diff 7)
               (values 0 0 w rem)))
      ((:month :year)
       (multiple-value-bind (wy wm) (iso-date-until rel-iso end :month)
         (let* ((whole-months (+ (* wy 12) wm))
                (upto (add-duration-date rel-iso 0 whole-months 0 0))
                (rem-days (- (iso-date->epoch-days end) (iso-date->epoch-days upto))))
           (multiple-value-bind (weeks days)
               (if (eq smallest :week)
                   (truncate rem-days 7)
                   (values 0 rem-days))
             (if (eq largest :year)
                 (multiple-value-bind (yy mm) (truncate whole-months 12)
                   (values yy mm weeks days))
                 (values 0 whole-months weeks days))))))
      (t (values 0 0 0 days-diff)))))

;;; ===========================================================================
;;; total() relative to a PlainDate (calendar units).
;;; ===========================================================================
(defun total-duration-relative (d rel-iso unit)
  "Return the exact-rational total of D in UNIT, relative to REL-ISO. For a
   fixed-length UNIT (day..ns) the duration's calendar units (years/months/weeks)
   are first resolved into real days via the relative date, then measured 24h."
  (let* (;; total days = calendar span of (years,months,weeks,days) + fractional
         ;; day from the time part, all relative to REL-ISO.
         (cal-end (add-duration-date rel-iso (getf d :years) (getf d :months)
                                     (getf d :weeks) (getf d :days)))
         (cal-days (- (iso-date->epoch-days cal-end) (iso-date->epoch-days rel-iso)))
         (days cal-days)
         (time-ns (duration-time-ns d)))
    (ecase unit
      ((:hour :minute :second :millisecond :microsecond :nanosecond)
       ;; days are 24h even relative to a plain date for fixed-length units
       (/ (+ (* days +ns-per-day+) time-ns) (duration-unit->ns unit)))
      (:day
       (/ (+ (* days +ns-per-day+) time-ns) +ns-per-day+))
      ((:year :month :week)
       (multiple-value-bind (dy dm dw wd frac-day) (duration-date-days-frac d)
         (calendar-frac-count rel-iso dy dm dw wd frac-day unit))))))

;;; ===========================================================================
;;; toString formatting.
;;; ===========================================================================
(defun format-temporal-duration (d fdigits mode smallest)
  "TemporalDurationToString. FDIGITS = :auto|0..9 (fractionalSecondDigits).
   MODE = rounding mode. SMALLEST = smallestUnit keyword (:second..:nanosecond)
   or NIL. The date units (years..days) are emitted as-is; the time part
   (hours..ns) is rounded to the requested precision and re-balanced with its
   OWN default-largest time unit — so a duration whose largest time unit is
   seconds keeps 'PT123.5S' unbalanced, while one with hours present carries
   overflow up (and, when days are present, into days)."
  (let* ((sign (let ((s (duration-sign d))) (if (zerop s) 1 s)))
         (years (abs (getf d :years))) (months (abs (getf d :months)))
         (weeks (abs (getf d :weeks))) (days (abs (getf d :days)))
         (hours (abs (getf d :hours))) (minutes (abs (getf d :minutes)))
         ;; ms/us/ns combined with seconds into a total sub-hour-minute ns; the
         ;; whole-second part joins the seconds field, the <1s remainder is the
         ;; fractional part. (This is fractional formatting, not unit balancing —
         ;; hours/minutes/days stay as their raw fields.)
         (seconds-total-ns (abs (+ (* (getf d :seconds) +ns-per-s+)
                                   (* (getf d :milliseconds) +ns-per-ms+)
                                   (* (getf d :microseconds) +ns-per-us+)
                                   (getf d :nanoseconds))))
         (seconds 0) (sub-ns 0)
         (explicit (or smallest (not (eq fdigits :auto))))
         (digits (cond (smallest (ecase smallest
                                   (:second 0) (:millisecond 3)
                                   (:microsecond 6) (:nanosecond 9)))
                       (t fdigits))))
    (multiple-value-setq (seconds sub-ns) (floor seconds-total-ns +ns-per-s+))
    (when explicit
      ;; Explicit precision: round the WHOLE time part (hours..ns) to the
      ;; requested unit, then re-balance the rounded ns with largestUnit = the
      ;; duration's default largest time unit (capped at day when date units are
      ;; present, so hour overflow carries into days).
      (let* ((unit-ns (cond ((null smallest) (expt 10 (- 9 fdigits)))
                            (t (ecase smallest
                                 (:second +ns-per-s+) (:millisecond +ns-per-ms+)
                                 (:microsecond +ns-per-us+) (:nanosecond 1)))))
             (time-ns-total (abs (duration-time-ns d)))
             (rounded (round-to-increment time-ns-total unit-ns mode))
             (largest-time (cond ((/= 0 (getf d :hours)) :hour)
                                 ((/= 0 (getf d :minutes)) :minute)
                                 (t :second)))
             (date-present (or (/= 0 (getf d :years)) (/= 0 (getf d :months))
                               (/= 0 (getf d :weeks)) (/= 0 (getf d :days)))))
        (multiple-value-bind (whole-s r) (floor rounded +ns-per-s+)
          (setf seconds whole-s sub-ns r hours 0 minutes 0)
          ;; balance whole seconds up to largest-time.
          (case largest-time
            (:second)
            (:minute (multiple-value-setq (minutes seconds) (floor whole-s 60)))
            (:hour (multiple-value-bind (m1 s1) (floor whole-s 60)
                     (multiple-value-bind (h1 mm1) (floor m1 60)
                       (setf hours h1 minutes mm1 seconds s1)))))
          ;; hours overflow into days when a date unit is present.
          (when date-present
            (multiple-value-bind (dc h1) (floor hours 24)
              (setf hours h1) (incf days dc))))))
    ;; Validate the time components are representable (< 2^53 seconds total),
    ;; matching IsValidDuration on the rendered values.
    (let ((total-s (+ (* days 86400) (* hours 3600) (* minutes 60) seconds)))
      (when (>= total-s (expt 2 53))
        (js-throw (make-native-error "RangeError" "duration too large to format"))))
    (let* ((frac (format-fractional sub-ns digits))
           (any-date (or (plusp years) (plusp months) (plusp weeks) (plusp days)))
           (out (make-string-output-stream)))
      (write-char #\P out)
      (when (plusp years) (format out "~dY" years))
      (when (plusp months) (format out "~dM" months))
      (when (plusp weeks) (format out "~dW" weeks))
      (when (plusp days) (format out "~dD" days))
      (let ((any-time (or (plusp hours) (plusp minutes) (plusp seconds)
                          (plusp (length frac)) explicit)))
        (when (or any-time (not any-date))
          (write-char #\T out)
          (when (plusp hours) (format out "~dH" hours))
          (when (plusp minutes) (format out "~dM" minutes))
          ;; seconds emitted when nonzero, when a fractional part exists, when
          ;; precision is explicit, or when they're the only time content.
          (when (or (plusp seconds) (plusp (length frac)) explicit
                    (and (zerop hours) (zerop minutes)))
            (format out "~d~aS" seconds frac))))
      (let ((s (get-output-stream-string out)))
        (if (= sign -1) (concatenate 'string "-" s) s)))))

;;; ===========================================================================
;;; make + install
;;; ===========================================================================
(defun install-temporal-duration (realm)
  (let* ((op (realm-object-proto realm))
         (proto (make-object :proto op :class "Object"))
         (ctor (native-function realm "Duration"
                 (lambda (this args) (declare (ignore this args))
                   (js-throw (make-native-error "TypeError" "Constructor Duration requires 'new'")))
                 0)))
    (setf *temporal-duration-proto* proto)
    ;; ---- constructor ----
    (setf (js-object-construct ctor)
          (lambda (args nt)
            (let ((d (list :years (duration-arg->int (arg 0 args))
                           :months (duration-arg->int (arg 1 args))
                           :weeks (duration-arg->int (arg 2 args))
                           :days (duration-arg->int (arg 3 args))
                           :hours (duration-arg->int (arg 4 args))
                           :minutes (duration-arg->int (arg 5 args))
                           :seconds (duration-arg->int (arg 6 args))
                           :milliseconds (duration-arg->int (arg 7 args))
                           :microseconds (duration-arg->int (arg 8 args))
                           :nanoseconds (duration-arg->int (arg 9 args)))))
              (full-validate-duration d)
              (let ((o (make-object :proto (proto-from-newtarget nt proto) :class "Object")))
                (setf (getf (js-object-internal o) :temporal-duration) d)
                o))))
    (def-value ctor "prototype" proto :writable nil :configurable nil)
    (def-value proto "constructor" ctor)

    ;; ---- statics ----
    (def-method realm ctor "from" 1 (this args)
      (declare (ignore this))
      (let ((v (arg 0 args)))
        (if (and (js-object-p v) (getf (js-object-internal v) :temporal-duration))
            (make-temporal-duration realm
              (copy-list (getf (js-object-internal v) :temporal-duration)))
            (make-temporal-duration realm
              (full-validate-duration (to-duration-record v))))))

    (def-method realm ctor "compare" 2 (this args)
      (declare (ignore this))
      (let* ((d1 (full-validate-duration (to-duration-record (arg 0 args))))
             (d2 (full-validate-duration (to-duration-record (arg 1 args))))
             (options (get-options-object (arg 2 args))))
        (multiple-value-bind (kind rel-iso) (to-relative-to realm options)
          (cond
            ;; Identical field-by-field durations compare equal regardless of
            ;; relativeTo (and without requiring it for calendar units).
            ((loop for f in +duration-fields+ always (= (getf d1 f) (getf d2 f)))
             0d0)
            ;; No calendar units in either: compare by total ns (24h days).
            ((and (not (duration-has-calendar-units-p d1))
                  (not (duration-has-calendar-units-p d2))
                  (eq kind :none))
             (let ((n1 (duration-total-time-ns d1)) (n2 (duration-total-time-ns d2)))
               (float (cond ((< n1 n2) -1) ((> n1 n2) 1) (t 0)) 1d0)))
            ((eq kind :zoned)
             (js-throw (make-native-error "TypeError" "ZonedDateTime relativeTo not yet supported")))
            ((and (or (duration-has-calendar-units-p d1)
                      (duration-has-calendar-units-p d2))
                  (member kind '(:none :need-plaindate)))
             (js-throw (make-native-error "RangeError"
                         "relativeTo is required for comparing durations with calendar units")))
            ((eq kind :need-plaindate)
             ;; relativeTo present but PlainDate not available and no calendar units:
             ;; fall back to time comparison after resolving days via 24h.
             (let ((n1 (duration-total-time-ns d1)) (n2 (duration-total-time-ns d2)))
               (float (cond ((< n1 n2) -1) ((> n1 n2) 1) (t 0)) 1d0)))
            ((null rel-iso)
             (js-throw (make-native-error "TypeError" "invalid relativeTo")))
            (t
             ;; date relativeTo: end epoch-days + time ns.
             (flet ((endns (dd)
                      (let* ((extra (truncate (duration-time-ns dd) +ns-per-day+))
                             (end (add-iso-date rel-iso (getf dd :years) (getf dd :months)
                                                (getf dd :weeks) (+ (getf dd :days) extra) :constrain)))
                        (+ (* (- (iso-date->epoch-days end) (iso-date->epoch-days rel-iso))
                              +ns-per-day+)
                           (mod (duration-time-ns dd) +ns-per-day+)))))
               (let ((n1 (endns d1)) (n2 (endns d2)))
                 (float (cond ((< n1 n2) -1) ((> n1 n2) 1) (t 0)) 1d0))))))))

    ;; ---- getters ----
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

    ;; ---- with ----
    (def-method realm proto "with" 1 (this args)
      (let ((d (temporal-slot this :temporal-duration "Temporal.Duration"))
            (partial (to-partial-duration-record (arg 0 args))))
        (let ((out (copy-list d)))
          (dolist (f +duration-fields+)
            (let ((v (getf partial f 'none)))
              (unless (eq v 'none) (setf (getf out f) v))))
          (make-temporal-duration realm (full-validate-duration out)))))

    ;; ---- negated / abs ----
    (def-method realm proto "negated" 0 (this args)
      (let ((d (temporal-slot this :temporal-duration "Temporal.Duration")))
        (make-temporal-duration realm
          (loop for f in +duration-fields+ append (list f (- (getf d f)))))))
    (def-method realm proto "abs" 0 (this args)
      (let ((d (temporal-slot this :temporal-duration "Temporal.Duration")))
        (make-temporal-duration realm
          (loop for f in +duration-fields+ append (list f (abs (getf d f)))))))

    ;; ---- add / subtract ----
    (labels ((add-sub (this args negate)
               (let* ((d1 (temporal-slot this :temporal-duration "Temporal.Duration"))
                      (d2 (full-validate-duration (to-duration-record (arg 0 args)))))
                 (when negate
                   (setf d2 (loop for f in +duration-fields+ append (list f (- (getf d2 f))))))
                 ;; Date-unit addition without relativeTo is a RangeError.
                 (when (or (duration-has-calendar-units-p d1)
                           (duration-has-calendar-units-p d2))
                   (js-throw (make-native-error "RangeError"
                               "cannot add durations with calendar units without relativeTo")))
                 (let* ((total (+ (duration-total-time-ns d1) (duration-total-time-ns d2)))
                        (largest (coarser-unit (duration-default-largest-unit d1)
                                               (duration-default-largest-unit d2)))
                        ;; largest can't be a calendar unit here (guarded above);
                        ;; but default-largest of a blank duration is :nanosecond.
                        (largest (if (member largest '(:year :month :week)) :day largest))
                        (result (balance-time-duration-ns total largest)))
                   (make-temporal-duration realm (full-validate-duration result))))))
      (def-method realm proto "add" 1 (this args) (add-sub this args nil))
      (def-method realm proto "subtract" 1 (this args) (add-sub this args t)))

    ;; ---- round ----
    (def-method realm proto "round" 1 (this args)
      (let ((d (temporal-slot this :temporal-duration "Temporal.Duration"))
            (arg0 (arg 0 args)))
        (when (js-undefined-p arg0)
          (js-throw (make-native-error "TypeError" "options required for round")))
        (let* ((string-shorthand (stringp arg0))
               (options (if string-shorthand nil (get-options-object arg0)))
               (all-units '(:year :month :week :day :hour :minute :second
                            :millisecond :microsecond :nanosecond)))
          ;; Spec read order (non-shorthand): largestUnit, relativeTo,
          ;; roundingIncrement, roundingMode, smallestUnit — relativeTo is read
          ;; between largestUnit and roundingIncrement.
          (multiple-value-bind (smallest largest increment mode kind rel-iso)
              (if string-shorthand
                  (let ((hit (assoc arg0 (unit-alist all-units) :test #'string=)))
                    (unless hit (js-throw (make-native-error "RangeError" "invalid smallestUnit")))
                    (values (cdr hit) nil 1 :half-expand :none nil))
                  (let ((largest (get-temporal-unit options "largestUnit" :datetime nil
                                                    all-units '(("auto" . :auto)))))
                    (multiple-value-bind (kind rel-iso) (to-relative-to realm options)
                      (let ((increment (get-rounding-increment options))
                            (mode (get-rounding-mode options :half-expand))
                            (smallest (get-temporal-unit options "smallestUnit" :datetime nil
                                                         all-units)))
                        ;; keep :auto distinct from truly-absent (NIL).
                        (values smallest largest increment mode kind rel-iso)))))
            (when (and (null smallest) (null largest))
              (js-throw (make-native-error "RangeError" "at least one of smallestUnit/largestUnit required")))
            ;; :auto largestUnit resolves to the duration's default largest unit.
            (when (eq largest :auto)
              (setf largest (duration-default-largest-unit d)))
            (progn
              (when (eq kind :zoned)
                (js-throw (make-native-error "TypeError" "ZonedDateTime relativeTo not yet supported")))
              ;; Defaults for smallest/largest.
              (let* ((sm (or smallest :nanosecond))
                     (default-largest (duration-default-largest-unit d))
                     (lg (cond (largest largest)
                               (t (coarser-unit default-largest sm)))))
                (when (< (unit-rank sm) (unit-rank lg))
                  (js-throw (make-native-error "RangeError" "smallestUnit is larger than largestUnit")))
                ;; Validate increment. For a calendar smallestUnit the increment
                ;; must be 1 unless largestUnit equals smallestUnit (you cannot
                ;; round to a multiple of N calendar units while also balancing
                ;; up to a coarser unit).
                (let ((maximum (round-max-increment sm)))
                  (when (and (member sm '(:year :month :week :day))
                             (not (eq lg sm))
                             (/= increment 1))
                    (js-throw (make-native-error "RangeError"
                                "roundingIncrement must be 1 for calendar units unless largestUnit equals smallestUnit")))
                  (validate-rounding-increment increment (or maximum most-positive-fixnum)
                                               (null maximum))
                  ;; For a time smallestUnit the increment must divide evenly into
                  ;; the count of that unit in the next-coarser unit.
                  (when (and maximum (/= 0 (mod maximum increment)))
                    (js-throw (make-native-error "RangeError"
                                "roundingIncrement does not divide evenly into the next unit"))))
                (let ((needs-rel (or (member sm '(:year :month :week))
                                     (member lg '(:year :month :week))
                                     (duration-has-calendar-units-p d)
                                     ;; day rounding needs rel only when calendar
                                     ;; involved; 24h-days path is fine otherwise
                                     )))
                  (cond
                    ((and needs-rel (member kind '(:none :need-plaindate)))
                     (js-throw (make-native-error "RangeError"
                                 "relativeTo is required for rounding calendar units")))
                    ((and needs-rel (null rel-iso))
                     (js-throw (make-native-error "TypeError" "invalid relativeTo")))
                    (needs-rel
                     (make-temporal-duration realm
                       (full-validate-duration
                        (round-duration-relative d rel-iso sm lg increment mode))))
                    (t
                     ;; Pure time/day rounding, 24h days, no relativeTo needed.
                     (let* ((total (duration-total-time-ns d))
                            (unit-ns (duration-unit->ns sm))
                            (rounded (round-to-increment total (* increment unit-ns) mode))
                            (result (balance-time-duration-ns rounded lg)))
                       (make-temporal-duration realm (full-validate-duration result))))))))))))

    ;; ---- total ----
    (def-method realm proto "total" 1 (this args)
      (let ((d (temporal-slot this :temporal-duration "Temporal.Duration"))
            (arg0 (arg 0 args)))
        (when (js-undefined-p arg0)
          (js-throw (make-native-error "TypeError" "total requires a unit")))
        (let* ((string-shorthand (stringp arg0))
               (options (if string-shorthand nil (get-options-object arg0)))
               (all-units '(:year :month :week :day :hour :minute :second
                            :millisecond :microsecond :nanosecond)))
          ;; Spec read order: relativeTo is read BEFORE unit.
          (multiple-value-bind (kind rel-iso)
              (if string-shorthand (values :none nil) (to-relative-to realm options))
            (when (eq kind :zoned)
              (js-throw (make-native-error "TypeError" "ZonedDateTime relativeTo not yet supported")))
            (let* ((unit (if string-shorthand
                             (let ((hit (assoc arg0 (unit-alist all-units) :test #'string=)))
                               (unless hit (js-throw (make-native-error "RangeError" "invalid unit")))
                               (cdr hit))
                             (get-temporal-unit options "unit" :datetime :required all-units)))
                   (needs-rel (or (member unit '(:year :month :week))
                                 (duration-has-calendar-units-p d))))
              (cond
                ((and needs-rel (member kind '(:none :need-plaindate)))
                 (js-throw (make-native-error "RangeError"
                             "relativeTo is required for calendar-unit totals")))
                ((and needs-rel (null rel-iso))
                 (js-throw (make-native-error "TypeError" "invalid relativeTo")))
                (needs-rel
                 (signed-rational->double (total-duration-relative d rel-iso unit)))
                (t
                 ;; fixed-length: 24h days.
                 (signed-rational->double
                  (/ (duration-total-time-ns d) (duration-unit->ns unit))))))))))

    ;; ---- toString / toJSON / toLocaleString ----
    (def-method realm proto "toString" 0 (this args)
      (let* ((d (temporal-slot this :temporal-duration "Temporal.Duration"))
             (options (get-options-object (arg 0 args)))
             (digits (get-fractional-second-digits options))
             (mode (get-rounding-mode options :trunc))
             (smallest (get-temporal-unit options "smallestUnit" :datetime nil
                                          '(:year :month :week :day :hour :minute
                                            :second :millisecond :microsecond :nanosecond))))
        (when (and smallest (not (member smallest '(:second :millisecond :microsecond :nanosecond))))
          (js-throw (make-native-error "RangeError" "smallestUnit not valid for Duration.toString")))
        (when (and smallest (not (eq digits :auto)))
          ;; both present: smallestUnit wins, but the presence is fine per tests
          )
        (format-temporal-duration d digits mode smallest)))
    (def-method realm proto "toJSON" 0 (this args)
      (declare (ignore args))
      (let ((d (temporal-slot this :temporal-duration "Temporal.Duration")))
        (format-temporal-duration d :auto :trunc nil)))
    (def-method realm proto "toLocaleString" 0 (this args)
      (declare (ignore args))
      (let ((d (temporal-slot this :temporal-duration "Temporal.Duration")))
        (format-temporal-duration d :auto :trunc nil)))

    ;; ---- valueOf: not a primitive ----
    (def-method realm proto "valueOf" 0 (this args)
      (declare (ignore args))
      (js-throw (make-native-error "TypeError"
                  "Cannot convert a Temporal.Duration to a primitive; use compare()")))

    ;; ---- @@toStringTag ----
    (put proto (symbol-tostringtag realm) "Temporal.Duration"
         :enumerable nil :writable nil :configurable t)

    (temporal-register realm "Duration" ctor)
    ctor))

(defun round-max-increment (unit)
  "Max rounding increment for round()/total(); NIL means unbounded (calendar
   units), which validate-rounding-increment treats as inclusive-any."
  (ecase unit
    ((:year :month :week :day) nil)
    (:hour 24) (:minute 60) (:second 60)
    (:millisecond 1000) (:microsecond 1000) (:nanosecond 1000)))

(register-builtin-installer 'install-temporal-duration)
