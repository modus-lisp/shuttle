;;;; temporal-calendars.lisp — the calendars Temporal speaks besides iso8601.
;;;;
;;;; EVERY CALENDAR IS A BIJECTION BETWEEN A DAY NUMBER AND ITS OWN FIELDS.  The
;;;; ISO code in temporal-core.lisp already pivots on exact epoch days
;;;; (ISO-DATE->EPOCH-DAYS / EPOCH-DAYS->ISO-DATE), and that is the whole seam a
;;;; calendar needs: given a day number, say what year/month/day you call it;
;;;; given your own year/month/day, say which day number that is.  Arithmetic,
;;;; comparison, durations and every other Temporal operation stay in day numbers
;;;; and never learn that a second calendar exists.
;;;;
;;;; So a calendar here is NOT a date type.  It is a pair of conversions plus the
;;;; shape questions Temporal asks about a year (how many months, how long is a
;;;; month, is it a leap year) and the era naming a year carries.
;;;;
;;;; MONTH CODES ARE THE SPEC'S WAY OF NAMING A MONTH WITHOUT COUNTING IT.  In a
;;;; lunisolar calendar the same ordinal month is a different month in a leap year,
;;;; so "M05" names the fifth month and "M05L" the leap month that follows it.  For
;;;; every calendar here the code is positional ("M01".."M13"), but the conversion
;;;; goes through CAL-MONTH-CODE / CAL-MONTH-FROM-CODE so the lunisolar calendars
;;;; can differ without their callers changing.
;;;;
;;;; CLOS, not structs: these are redefined while an image is live.
(in-package #:shuttle)

;;; ===========================================================================
;;; The protocol
;;; ===========================================================================
(defclass calendar ()
  ((id :initarg :id :reader cal-id :type string
       :documentation "The canonical calendar identifier, e.g. \"gregory\"."))
  (:documentation "A calendar: day-number <-> (era, year, month, day) plus the
   shape of a year."))

(defgeneric cal-year-month-day (cal days)
  (:documentation "The calendar's own (values year month day) for epoch DAYS."))

(defgeneric cal-days-from-ymd (cal year month day)
  (:documentation "Epoch day number for the calendar's own YEAR MONTH DAY.
   MONTH is 1-based in this calendar's own month ordering."))

(defgeneric cal-months-in-year (cal year)
  (:documentation "How many months YEAR has in this calendar."))

(defgeneric cal-days-in-month (cal year month)
  (:documentation "How many days MONTH of YEAR has."))

(defgeneric cal-leap-year-p (cal year)
  (:documentation "Whether YEAR is a leap year by this calendar's own rule."))

(defgeneric cal-era-fields (cal days)
  (:documentation "(values era era-year) for epoch DAYS, or (values NIL NIL) for a
   calendar with no eras.  Takes the DAY, not the year: a Japanese era begins on an
   accession date, so 1989-01-07 is Showa 64 while 1989-01-08 is Heisei 1 -- a year
   alone cannot name the era it is in."))

(defgeneric cal-year-from-era (cal era era-year)
  (:documentation "Arithmetic year for ERA + ERA-YEAR, or NIL if ERA is unknown."))

(defgeneric cal-month-code (cal year month)
  (:documentation "The month code string naming MONTH of YEAR."))

(defgeneric cal-month-from-code (cal year code)
  (:documentation "The month number CODE names in YEAR, or NIL if there is none."))

(defgeneric cal-eras-of (cal)
  (:documentation "Every era name this calendar accepts, most recent first.
   Used to answer `Temporal.Calendar' era queries and to validate input."))

;;; Defaults: positional month codes, no eras, year length from the months.
(defmethod cal-month-code ((cal calendar) year month)
  (declare (ignore year))
  (format nil "M~2,'0d" month))

(defmethod cal-month-from-code ((cal calendar) year code)
  ;; "M01".."M13" only; a trailing L is a leap month and belongs to the lunisolar
  ;; subclasses, so it is NOT silently accepted here.
  (when (and (stringp code) (= (length code) 3)
             (char-equal (char code 0) #\M)
             (digit-char-p (char code 1)) (digit-char-p (char code 2)))
    (let ((n (parse-integer code :start 1 :junk-allowed t)))
      (when (and n (<= 1 n (cal-months-in-year cal year))) n))))

(defmethod cal-era-fields ((cal calendar) days) (declare (ignore days)) (values nil nil))
(defmethod cal-year-from-era ((cal calendar) era era-year)
  (declare (ignore era era-year)) nil)
(defmethod cal-eras-of ((cal calendar)) nil)

(defun cal-days-in-year (cal year)
  "How many days YEAR has: asked of the months, so no calendar repeats the rule."
  (loop for m from 1 to (cal-months-in-year cal year)
        sum (cal-days-in-month cal year m)))

(defun cal-day-of-year (cal year month day)
  "1-based day-of-year for YEAR MONTH DAY."
  (+ day (loop for m from 1 below month sum (cal-days-in-month cal year m))))

;;; ===========================================================================
;;; The registry
;;; ===========================================================================
(defvar *calendars* (make-hash-table :test 'equal)
  "Canonical calendar id -> CALENDAR instance.")

(defvar *calendar-aliases* (make-hash-table :test 'equal)
  "Accepted spelling -> canonical calendar id.  BCP 47 keeps obsolete spellings
   working (`islamicc' for islamic-civil), and CLDR canonicalisation folds
   `ethiopic-amete-alem' to `ethioaa'.")

(defun register-calendar (cal &rest aliases)
  "Register CAL under its own id plus ALIASES.  Returns CAL."
  (setf (gethash (cal-id cal) *calendars*) cal)
  (dolist (a aliases) (setf (gethash (string-downcase a) *calendar-aliases*) (cal-id cal)))
  cal)

(defun find-calendar (id)
  "The CALENDAR for ID (case-insensitive, aliases resolved), or NIL.
   Case folding is ASCII-only: calendar ids are BCP 47 subtags, and a Turkish
   dotless i must not make `ISLAMIC' fail to match."
  (when (stringp id)
    (let* ((lower (string-downcase id))
           (canon (or (gethash lower *calendar-aliases*) lower)))
      (gethash canon *calendars*))))

(defun calendar-id-supported-p (id)
  (and (find-calendar id) t))

;;; ===========================================================================
;;; iso8601 — the calendar every other one is measured against
;;; ===========================================================================
(defclass iso-calendar (calendar) ())

(defmethod cal-year-month-day ((cal iso-calendar) days)
  (let ((iso (epoch-days->iso-date days)))
    (values (iso-date-year iso) (iso-date-month iso) (iso-date-day iso))))

(defmethod cal-days-from-ymd ((cal iso-calendar) year month day)
  (iso-date->epoch-days (make-iso-date year month day)))

(defmethod cal-months-in-year ((cal iso-calendar) year) (declare (ignore year)) 12)
(defmethod cal-days-in-month ((cal iso-calendar) year month) (days-in-month year month))
(defmethod cal-leap-year-p ((cal iso-calendar) year) (leap-year-p year))

;;; ===========================================================================
;;; The Gregorian family: the ISO year shape, wearing a different year number
;;; ===========================================================================
;;; gregory, buddhist, roc and japanese all divide the year exactly as ISO does --
;;; same months, same leap rule, same day numbers.  They differ only in what they
;;; CALL a year: an offset from the ISO year (buddhist +543, roc -1911) and an era
;;; that renumbers it.  So they share one class and differ by two slots, and none
;;; of them re-derives the month arithmetic.
(defclass gregorian-like (calendar)
  ((year-offset :initarg :year-offset :initform 0 :reader cal-year-offset
                :documentation "calendar year = ISO year + this.")
   (eras :initarg :eras :initform nil :reader cal-era-table
         :documentation "Era descriptors, most recent first.  See CAL-ERA.")))

(defmethod cal-year-month-day ((cal gregorian-like) days)
  (let ((iso (epoch-days->iso-date days)))
    (values (+ (iso-date-year iso) (cal-year-offset cal))
            (iso-date-month iso)
            (iso-date-day iso))))

(defmethod cal-days-from-ymd ((cal gregorian-like) year month day)
  (iso-date->epoch-days
   (make-iso-date (- year (cal-year-offset cal)) month day)))

(defmethod cal-months-in-year ((cal gregorian-like) year) (declare (ignore year)) 12)

(defmethod cal-days-in-month ((cal gregorian-like) year month)
  (days-in-month (- year (cal-year-offset cal)) month))

(defmethod cal-leap-year-p ((cal gregorian-like) year)
  (leap-year-p (- year (cal-year-offset cal))))

;;; An era descriptor is (name aliases start-year reverse-p), where START-YEAR is
;;; the calendar year in which the era begins and REVERSE-P marks an era that
;;; counts BACKWARDS from its end (bce year 1 is the year before ce year 1).
(defmethod cal-era-fields ((cal gregorian-like) days)
  (multiple-value-bind (year) (cal-year-month-day cal days)
    (dolist (e (cal-era-table cal) (values nil nil))
      (destructuring-bind (name aliases start reverse-p) e
        (declare (ignore aliases))
        (cond ((null start)
               ;; A calendar with ONE era covering every year: the era year is just
               ;; the year (buddhist BE 2569 is year 2569), including at and below
               ;; zero, where there is nothing to count backwards from.
               (return (values name year)))
              (reverse-p
               (when (< year start) (return (values name (- start year)))))
              ((>= year start)
               (return (values name (+ (- year start) 1)))))))))

(defmethod cal-year-from-era ((cal gregorian-like) era era-year)
  (let ((want (and (stringp era) (string-downcase era))))
    (dolist (e (cal-era-table cal) nil)
      (destructuring-bind (name aliases start reverse-p) e
        (when (or (equal want name) (member want aliases :test #'equal))
          (return (cond ((null start) era-year)
                        (reverse-p (- start era-year))
                        (t (+ start (- era-year 1))))))))))

(defmethod cal-eras-of ((cal gregorian-like))
  (mapcar #'first (cal-era-table cal)))

;;; ---------------------------------------------------------------------------
;;; japanese: the same years, cut into eras by an emperor's accession
;;; ---------------------------------------------------------------------------
;;; The Japanese eras do not start on 1 January -- Reiwa begins 2019-05-01 -- so a
;;; year is not enough to name the era and CAL-ERA on a year alone would be wrong
;;; for the months on the far side of the boundary.  This subclass carries the era
;;; START DATE and resolves the era from the day number instead.  Before Meiji the
;;; calendar reports Gregorian ce/bce, which is what ICU does.
(defclass japanese-calendar (gregorian-like) ())

(defparameter +japanese-eras+
  ;; (name aliases iso-year iso-month iso-day)   most recent first
  '(("reiwa"  ()      2019 5  1)
    ("heisei" ()      1989 1  8)
    ("showa"  ()      1926 12 25)
    ("taisho" ()      1912 7  30)
    ("meiji"  ()      1868 9  8))
  "Japanese era starts, as ICU has them.  An era's first year is year 1 even when
   it is a partial year: 1989-01-07 is Showa 64 and 1989-01-08 is Heisei 1.")

(defmethod cal-era-fields ((cal japanese-calendar) days)
  (dolist (e +japanese-eras+ (call-next-method))   ; before Meiji: fall back to ce/bce
    (destructuring-bind (name aliases y m d) e
      (declare (ignore aliases))
      (when (>= days (iso-date->epoch-days (make-iso-date y m d)))
        (let ((iso (epoch-days->iso-date days)))
          (return (values name (+ (- (iso-date-year iso) y) 1))))))))

(defmethod cal-year-from-era ((cal japanese-calendar) era era-year)
  ;; An era year maps to exactly one calendar year even though the era started
  ;; mid-year: Heisei 1 is 1989 (its January days and its December days alike).
  (let ((want (and (stringp era) (string-downcase era))))
    (dolist (e +japanese-eras+ (call-next-method))
      (destructuring-bind (name aliases y m d) e
        (declare (ignore m d))
        (when (or (equal want name) (member want aliases :test #'equal))
          (return (+ y (- era-year 1))))))))

(defmethod cal-eras-of ((cal japanese-calendar))
  (append (mapcar #'first +japanese-eras+) (call-next-method)))

;;; ===========================================================================
;;; Registration
;;; ===========================================================================
(defun %register-builtin-calendars ()
  (clrhash *calendars*)
  (clrhash *calendar-aliases*)
  (register-calendar (make-instance 'iso-calendar :id "iso8601"))
  (register-calendar
   (make-instance 'gregorian-like :id "gregory" :year-offset 0
                  ;; ce counts up from year 1; bce counts back from year 0, so
                  ;; bce 1 IS year 0 -- the year before ce 1, there being no year 0
                  ;; in the era numbering even though there is one in the arithmetic.
                  :eras '(("ce" ("ad") 1 nil)
                          ("bce" ("bc") 1 t)))
   "gregorian")
  (register-calendar
   (make-instance 'gregorian-like :id "buddhist" :year-offset 543
                  :eras '(("be" () nil nil))))
  (register-calendar
   (make-instance 'gregorian-like :id "roc" :year-offset -1911
                  :eras '(("roc" ("minguo") 1 nil)
                          ("broc" ("before-roc") 1 t)))
   "minguo")
  (register-calendar
   (make-instance 'japanese-calendar :id "japanese" :year-offset 0
                  :eras '(("ce" ("ad") 1 nil)
                          ("bce" ("bc") 1 t))))
  (values))

(%register-builtin-calendars)

;;; ===========================================================================
;;; Fixed-day epochs
;;; ===========================================================================
;;; Each calendar below is anchored by the day its year 1 began, expressed in this
;;; file's epoch (days since 1970-01-01).  The literature quotes these as R.D.
;;; ("fixed") day numbers counting from Gregorian 0001-01-01, so the conversion is
;;; R.D. - 719163, and that subtraction is written out per constant rather than
;;; folded away -- an epoch off by one silently shifts an entire calendar, and the
;;; arithmetic that produced it should stay readable.
(defconstant +rd-epoch-offset+ 719163
  "R.D. day number of 1970-01-01, the origin this file counts from.")

(defmacro define-rd-epoch (name rd doc)
  `(defconstant ,name (- ,rd +rd-epoch-offset+) ,doc))

(define-rd-epoch +coptic-epoch+   103605 "Coptic 1 Thout 1 = Julian 284-08-29.")
(define-rd-epoch +ethiopic-epoch+   2796 "Ethiopic 1 Meskerem 1 = Julian 8-08-29.")
(define-rd-epoch +islamic-epoch+  227015 "1 Muharram 1 AH = Julian 622-07-16 (Friday).")
(define-rd-epoch +persian-epoch+  226896 "1 Farvardin 1 AP = Julian 622-03-19.")

;;; ===========================================================================
;;; Coptic and Ethiopic: twelve months of thirty, and a short thirteenth
;;; ===========================================================================
;;; One shape, three identities.  Coptic and Ethiopic differ only in when their
;;; year 1 was; `ethioaa' is the Ethiopic calendar counted from the Alexandrian
;;; creation era instead, which is the same year plus 5500 -- so it is a year
;;; offset, not a third calendar.
(defclass coptic-like (calendar)
  ((epoch :initarg :epoch :reader cal-epoch)
   (year-offset :initarg :year-offset :initform 0 :reader cal-year-offset)
   (era-name :initarg :era-name :reader cal-era-name)))

(defmethod cal-months-in-year ((cal coptic-like) year) (declare (ignore year)) 13)

(defmethod cal-leap-year-p ((cal coptic-like) year)
  ;; Every fourth year, with no century exception -- the Julian rule, which is why
  ;; these calendars drift against the Gregorian one by a day each century.
  (= 3 (mod (- year (cal-year-offset cal)) 4)))

(defmethod cal-days-in-month ((cal coptic-like) year month)
  (if (= month 13) (if (cal-leap-year-p cal year) 6 5) 30))

(defmethod cal-days-from-ymd ((cal coptic-like) year month day)
  (let ((y (- year (cal-year-offset cal))))
    (+ (cal-epoch cal) -1
       (* 365 (- y 1))
       (floor y 4)
       (* 30 (- month 1))
       day)))

(defmethod cal-year-month-day ((cal coptic-like) days)
  ;; The 1461-day estimate lands a year out at a year boundary, and the thirteenth
  ;; month is 5 days long or 6 -- so the year is STEPPED to the one that actually
  ;; contains DAYS, and the months are walked with CAL-DAYS-IN-MONTH rather than
  ;; divided by 30.  Dividing gave a 6th epagomenal day to years that have only 5.
  (let* ((d (- days (cal-epoch cal)))
         (y (+ (cal-year-offset cal) (1+ (floor (- (* 4 d) 1) 1461)))))
    (loop while (< days (cal-days-from-ymd cal y 1 1)) do (decf y))
    (loop while (>= days (cal-days-from-ymd cal (1+ y) 1 1)) do (incf y))
    (let ((doy (- days (cal-days-from-ymd cal y 1 1)))
          (month 1))
      (loop for dim = (cal-days-in-month cal y month)
            while (>= doy dim) do (decf doy dim) (incf month))
      (values y month (1+ doy)))))

(defmethod cal-era-fields ((cal coptic-like) days)
  (values (cal-era-name cal) (nth-value 0 (cal-year-month-day cal days))))

(defmethod cal-year-from-era ((cal coptic-like) era era-year)
  (when (and (stringp era) (string-equal era (cal-era-name cal))) era-year))

(defmethod cal-eras-of ((cal coptic-like)) (list (cal-era-name cal)))

;;; ===========================================================================
;;; Islamic, tabular: a 30-year cycle, no sighting required
;;; ===========================================================================
;;; The civil and tbla variants are the SAME arithmetic one day apart -- they
;;; disagree only about whether year 1 began on the Thursday or the Friday.
(defclass islamic-tabular (calendar)
  ((epoch :initarg :epoch :reader cal-epoch)))

(defmethod cal-months-in-year ((cal islamic-tabular) year) (declare (ignore year)) 12)

(defmethod cal-leap-year-p ((cal islamic-tabular) year)
  ;; 11 leap years per 30-year cycle.  ASKED OF THE DAY-COUNT FORMULA rather than
  ;; stated separately: the two have to agree exactly, and when they did not, the
  ;; 30th of the twelfth month existed by one rule and not the other -- a date ICU
  ;; reports as 1188-12-30 came back here as 1188-13-1.
  (/= (floor (+ 3 (* 11 (1+ year))) 30)
      (floor (+ 3 (* 11 year)) 30)))

(defmethod cal-days-in-month ((cal islamic-tabular) year month)
  (cond ((oddp month) 30)
        ((and (= month 12) (cal-leap-year-p cal year)) 30)
        (t 29)))

(defmethod cal-days-from-ymd ((cal islamic-tabular) year month day)
  (+ (cal-epoch cal) -1
     (* 354 (- year 1))
     (floor (+ 3 (* 11 year)) 30)
     (* 29 (- month 1))
     (floor month 2)
     day))

(defmethod cal-year-month-day ((cal islamic-tabular) days)
  (let* ((d (- days (cal-epoch cal)))
         (y (floor (+ (* 30 d) 10646) 10631)))
    ;; The estimate can land a year out at a cycle edge; step it rather than
    ;; trusting the division.
    (loop while (< days (cal-days-from-ymd cal y 1 1)) do (decf y))
    (loop while (>= days (cal-days-from-ymd cal (1+ y) 1 1)) do (incf y))
    (let* ((doy (- days (cal-days-from-ymd cal y 1 1)))
           (month 1))
      (loop for dim = (cal-days-in-month cal y month)
            while (>= doy dim) do (decf doy dim) (incf month))
      (values y month (1+ doy)))))

;;; Two eras, meeting at year 1: AH counts forward from the Hijra and BH counts
;;; backwards from it, so BH 1 is the year before AH 1 -- the same shape as
;;; bce/ce, and the same absence of a year zero in the naming.
(defmethod cal-era-fields ((cal islamic-tabular) days)
  (let ((y (nth-value 0 (cal-year-month-day cal days))))
    (if (plusp y) (values "ah" y) (values "bh" (- 1 y)))))

(defmethod cal-year-from-era ((cal islamic-tabular) era era-year)
  (cond ((not (stringp era)) nil)
        ((string-equal era "ah") era-year)
        ((string-equal era "bh") (- 1 era-year))))

(defmethod cal-eras-of ((cal islamic-tabular)) '("ah" "bh"))

;;; ===========================================================================
;;; Persian (Solar Hijri), arithmetic
;;; ===========================================================================
;;; Six months of 31, five of 30, and a last month of 29 that gains a day in a
;;; leap year.  The leap rule is the 2820-year cycle, which is what ICU computes.
(defclass persian-calendar (calendar) ())

(defmethod cal-months-in-year ((cal persian-calendar) year) (declare (ignore year)) 12)

(defmethod cal-leap-year-p ((cal persian-calendar) year)
  (let ((y (if (plusp year) (- year 474) (- year 473))))
    (< (mod (* (+ (mod y 2820) 474 38) 682) 2816) 682)))

(defmethod cal-days-in-month ((cal persian-calendar) year month)
  (cond ((<= month 6) 31)
        ((<= month 11) 30)
        ((cal-leap-year-p cal year) 30)
        (t 29)))

(defmethod cal-days-from-ymd ((cal persian-calendar) year month day)
  (let* ((y (if (plusp year) (- year 474) (- year 473)))
         (cycle-year (+ (mod y 2820) 474)))
    (+ +persian-epoch+ -1
       (* 1029983 (floor y 2820))
       (* 365 (- cycle-year 1))
       (floor (- (* 682 cycle-year) 110) 2816)
       (if (<= month 7) (* 31 (- month 1)) (+ (* 30 (- month 1)) 6))
       day)))

(defmethod cal-year-month-day ((cal persian-calendar) days)
  (let ((y (+ 475 (floor (- days +persian-epoch+) 366))))
    (loop while (< days (cal-days-from-ymd cal y 1 1)) do (decf y))
    (loop while (>= days (cal-days-from-ymd cal (1+ y) 1 1)) do (incf y))
    (let* ((doy (- days (cal-days-from-ymd cal y 1 1)))
           (month 1))
      (loop for dim = (cal-days-in-month cal y month)
            while (>= doy dim) do (decf doy dim) (incf month))
      (values y month (1+ doy)))))

(defmethod cal-era-fields ((cal persian-calendar) days)
  (values "ap" (nth-value 0 (cal-year-month-day cal days))))

(defmethod cal-year-from-era ((cal persian-calendar) era era-year)
  (when (and (stringp era) (string-equal era "ap")) era-year))

(defmethod cal-eras-of ((cal persian-calendar)) '("ap"))

;;; ===========================================================================
;;; Indian national (Saka)
;;; ===========================================================================
;;; Defined BY the Gregorian calendar rather than by an epoch: its year starts on
;;; 22 March and its leap years are exactly the Gregorian leap years, so it is
;;; written here in those terms instead of with a fixed-day constant it would only
;;; have to convert back.
(defclass indian-calendar (calendar) ())

(defmethod cal-months-in-year ((cal indian-calendar) year) (declare (ignore year)) 12)

(defmethod cal-leap-year-p ((cal indian-calendar) year) (leap-year-p (+ year 78)))

(defmethod cal-days-in-month ((cal indian-calendar) year month)
  (cond ((= month 1) (if (cal-leap-year-p cal year) 31 30))
        ((<= month 6) 31)
        (t 30)))

(defun %indian-new-year-days (saka-year)
  "The day 1 Chaitra of SAKA-YEAR falls on: 21 March in a Gregorian leap year,
   22 March otherwise."
  (let ((g (+ saka-year 78)))
    (iso-date->epoch-days (make-iso-date g 3 (if (leap-year-p g) 21 22)))))

(defmethod cal-days-from-ymd ((cal indian-calendar) year month day)
  (+ (%indian-new-year-days year)
     (loop for m from 1 below month sum (cal-days-in-month cal year m))
     (- day 1)))

(defmethod cal-year-month-day ((cal indian-calendar) days)
  (let ((y (- (iso-date-year (epoch-days->iso-date days)) 78)))
    (loop while (< days (%indian-new-year-days y)) do (decf y))
    (loop while (>= days (%indian-new-year-days (1+ y))) do (incf y))
    (let* ((doy (- days (%indian-new-year-days y)))
           (month 1))
      (loop for dim = (cal-days-in-month cal y month)
            while (>= doy dim) do (decf doy dim) (incf month))
      (values y month (1+ doy)))))

(defmethod cal-era-fields ((cal indian-calendar) days)
  (values "shaka" (nth-value 0 (cal-year-month-day cal days))))

(defmethod cal-year-from-era ((cal indian-calendar) era era-year)
  (when (and (stringp era) (string-equal era "shaka")) era-year))

(defmethod cal-eras-of ((cal indian-calendar)) '("shaka"))

;;; ===========================================================================
(defun %register-arithmetic-calendars ()
  (register-calendar (make-instance 'coptic-like :id "coptic"
                                    :epoch +coptic-epoch+ :era-name "am"))
  (register-calendar (make-instance 'coptic-like :id "ethiopic"
                                    :epoch +ethiopic-epoch+ :era-name "am"))
  (register-calendar (make-instance 'coptic-like :id "ethioaa"
                                    :epoch +ethiopic-epoch+ :year-offset 5500
                                    :era-name "aa")
                     "ethiopic-amete-alem")
  (register-calendar (make-instance 'islamic-tabular :id "islamic-civil"
                                    :epoch +islamic-epoch+)
                     "islamicc")
  (register-calendar (make-instance 'islamic-tabular :id "islamic-tbla"
                                    :epoch (- +islamic-epoch+ 1)))
  (register-calendar (make-instance 'persian-calendar :id "persian"))
  (register-calendar (make-instance 'indian-calendar :id "indian"))
  (values))

(%register-arithmetic-calendars)
