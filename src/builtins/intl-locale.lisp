;;;; builtins/intl-locale.lisp — Intl.Locale. Built ON the intl-core kernel
;;;; (parse-unicode-locale-id / canonicalize / add-/remove-likely-subtags /
;;;; the GetOption family). Instances carry their canonical [[Locale]] string in
;;;; the :initialized-locale internal slot (which the kernel's
;;;; CanonicalizeLocaleList unwraps).
(in-package #:shuttle)

(defvar *intl-locale-proto* nil)

;;; ===========================================================================
;;; Internal-slot access
;;; ===========================================================================
(defun locale-this-tag (this)
  "RequireInternalSlot [[InitializedLocale]] -> the [[Locale]] string, or TypeError."
  (let ((v (and (js-object-p this) (js-object-internal this)
                (getf (js-object-internal this) :initialized-locale))))
    (unless (stringp v)
      (js-throw (make-native-error "TypeError" "receiver is not an Intl.Locale")))
    v))

;;; ===========================================================================
;;; Option validators (produce a subtag string or throw RangeError)
;;; ===========================================================================
(defun %opt-language (s)
  (unless (and (language-subtag-p s)
               ;; must be JUST a language subtag (no dashes / extlang / grandfathered)
               (not (find #\- s)))
    (js-throw (make-native-error "RangeError" "invalid language option")))
  (%lc s))

(defun %opt-script (s)
  (unless (script-subtag-p s)
    (js-throw (make-native-error "RangeError" "invalid script option")))
  (titlecase s))

(defun %opt-region (s)
  (unless (region-subtag-p s)
    (js-throw (make-native-error "RangeError" "invalid region option")))
  (if (%all #'%digit-p s) s (string-upcase s)))

(defun %opt-variants (s)
  "One or more '-'-joined unicode_variant_subtag, no dups. Returns lowercase
   '-'-joined string."
  (let ((parts (split-dash s)))
    (unless (and parts (every #'variant-subtag-p parts)
                 (= (length parts) (length (remove-duplicates parts :test #'string-equal))))
      (js-throw (make-native-error "RangeError" "invalid variants option")))
    (format nil "~{~a~^-~}" (mapcar #'%lc parts))))

(defun %opt-firstday (s)
  "WeekdayToString(fw): digit 1..7 -> mon..sun, 0 -> sun; strings \"1\"..\"7\",\"0\"
   likewise; other strings pass through. Then validate as a type sequence
   (alnum{3,8})('-'alnum{3,8})* . Returns the value string (lowercased) or RangeError."
  (let ((mapped
          (cond ((member s '("1" "mon") :test #'string=) "mon")
                ((member s '("2" "tue") :test #'string=) "tue")
                ((member s '("3" "wed") :test #'string=) "wed")
                ((member s '("4" "thu") :test #'string=) "thu")
                ((member s '("5" "fri") :test #'string=) "fri")
                ((member s '("6" "sat") :test #'string=) "sat")
                ((member s '("7" "0" "sun") :test #'string=) "sun")
                (t s))))
    (%opt-uvalue mapped "firstDayOfWeek")))

(defun %opt-uvalue (s key)
  "Validate a Unicode-extension keyword value: type = (alnum{3,8})('-'alnum{3,8})*."
  (let ((parts (split-dash s)))
    (unless (and parts (every (lambda (p) (and (<= 3 (length p) 8) (%all #'%alnum-p p))) parts))
      (js-throw (make-native-error "RangeError" (format nil "invalid ~a option" key))))
    (%lc s)))

;;; ===========================================================================
;;; ApplyOptionsToTag + ApplyUnicodeExtensionToTag
;;; ===========================================================================
(defun locale-apply-options (tag opts)
  "Given a base TAG string (already canonicalized once) and the read OPTS plist
   (:language :script :region :variants :calendar :collation :hourcycle
   :casefirst :numeric :numberingsystem), build the merged + re-canonicalized
   [[Locale]] string. Signals RangeError on invalid tag/option."
  ;; 1. Structural validity of the tag.
  (unless (structurally-valid-locale-id-p tag)
    (unless (assoc tag +grandfathered-alias+ :test #'string-equal)
      (js-throw (make-native-error "RangeError" (format nil "invalid language tag: ~a" tag)))))
  ;; canonicalize the base tag once, re-parse.
  (let* ((canon (canonicalize-unicode-locale-id tag))
         (lid (parse-unicode-locale-id canon)))
    (unless lid (js-throw (make-native-error "RangeError" "invalid language tag")))
    ;; 2. base-name overrides
    (when (getf opts :language) (setf (locale-id-language lid) (getf opts :language)))
    (when (getf opts :script) (setf (locale-id-script lid) (getf opts :script)))
    (when (getf opts :region) (setf (locale-id-region lid) (getf opts :region)))
    (when (getf opts :variants)
      (setf (locale-id-variants lid) (split-dash (getf opts :variants))))
    ;; 3. Unicode-extension keyword overrides -> update the -u- extension.
    (let ((uext (loop for (k . v) in
                      (list (cons "ca" (getf opts :calendar))
                            (cons "co" (getf opts :collation))
                            (cons "hc" (getf opts :hourcycle))
                            (cons "kf" (getf opts :casefirst))
                            (cons "kn" (getf opts :numeric))
                            (cons "fw" (getf opts :firstdayofweek))
                            (cons "nu" (getf opts :numberingsystem)))
                      when v collect (cons k v))))
      (when uext (locale-set-u-keywords lid uext)))
    ;; 4. re-canonicalize the whole thing. Serialize first, then run the
    ;; string-level canonicalizer so grandfathered whole-tag replacements
    ;; (e.g. cel-gaulish -> xtg, formed by applying variants to "cel") apply.
    (canonicalize-unicode-locale-id (lid->string (canonicalize-lid lid)))))

(defun locale-set-u-keywords (lid overrides)
  "Merge OVERRIDES (alist key -> value-string, value \"\" == bare key) into the
   -u- extension of LID, replacing existing keywords of the same key."
  (let* ((uentry (assoc #\u (locale-id-extensions lid)))
         (payload (if uentry (cdr uentry) (list :attrs '() :keywords '())))
         (keywords (getf payload :keywords)))
    (dolist (ov overrides)
      (let* ((key (car ov)) (val (cdr ov))
             (types (if (string= val "") '() (split-dash val))))
        (setf keywords (remove key keywords :key #'car :test #'string=))
        (setf keywords (append keywords (list (cons key types))))))
    (let ((new-payload (list :attrs (getf payload :attrs) :keywords keywords)))
      (if uentry
          (setf (cdr uentry) new-payload)
          (setf (locale-id-extensions lid)
                (append (locale-id-extensions lid) (list (cons #\u new-payload))))))))

;;; The keyword value stored above is a raw string; canonicalize-u-payload later
;;; expects (key . (types...)). We stored (key . (types...)) — good.

;;; ===========================================================================
;;; Getters — read one -u- keyword value / base subtag from [[Locale]]
;;; ===========================================================================
(defun locale-u-keyword-value (lid key)
  "Return the canonical value string for -u-KEY-... (\"\" for a bare key), or NIL."
  (let* ((uentry (assoc #\u (locale-id-extensions lid)))
         (kw (and uentry (assoc key (getf (cdr uentry) :keywords) :test #'string=))))
    (when kw
      (if (cdr kw) (format nil "~{~a~^-~}" (cdr kw)) ""))))

(defun locale-base-subtag (lid which)
  (ecase which
    (:language (locale-id-language lid))
    (:script (locale-id-script lid))
    (:region (locale-id-region lid))
    (:variants (when (locale-id-variants lid)
                 (format nil "~{~a~^-~}" (locale-id-variants lid))))))

;;; ===========================================================================
;;; install-intl_locale
;;; ===========================================================================
(defun install-intl_locale (realm)
  (let* ((op (realm-object-proto realm))
         (proto (make-object :proto op :class "Object"))
         (ctor (native-function realm "Locale"
                 (lambda (this args) (declare (ignore this args))
                   (js-throw (make-native-error "TypeError" "Constructor Locale requires 'new'")))
                 1)))
    (setf *intl-locale-proto* proto)
    ;; ---- [[Construct]] ----
    (setf (js-object-construct ctor)
          (lambda (args nt)
            (when (js-undefined-p nt)
              (js-throw (make-native-error "TypeError" "Intl.Locale requires new")))
            (let ((tagv (arg 0 args)) (optv (arg 1 args)))
              ;; tag must be a String or Object (incl. Locale instance).
              (unless (or (stringp tagv) (js-object-p tagv))
                (js-throw (make-native-error "TypeError" "locale tag must be a string or object")))
              (let ((tag (if (and (js-object-p tagv) (locale-instance-tag tagv))
                             (locale-instance-tag tagv)
                             (to-string tagv)))
                    (opts (coerce-options-to-object optv)))
                ;; Read options in spec getter ORDER.
                (let* ((o-language (locale-opt-string opts "language" #'%opt-language))
                       (o-script   (locale-opt-string opts "script" #'%opt-script))
                       (o-region   (locale-opt-string opts "region" #'%opt-region))
                       (o-variants (locale-opt-string opts "variants" #'%opt-variants))
                       (o-calendar (locale-opt-string opts "calendar"
                                     (lambda (s) (%opt-uvalue s "calendar"))))
                       (o-collation (locale-opt-string opts "collation"
                                      (lambda (s) (%opt-uvalue s "collation"))))
                       (o-firstday (locale-opt-string opts "firstDayOfWeek" #'%opt-firstday))
                       (o-hourcycle (get-option opts "hourCycle" :string
                                                '("h11" "h12" "h23" "h24") :undefined))
                       (o-casefirst (get-option opts "caseFirst" :string
                                                '("upper" "lower" "false") :undefined))
                       (o-numeric-raw (js-get opts "numeric"))
                       (o-numeric-present (not (js-undefined-p o-numeric-raw)))
                       (o-numeric (and o-numeric-present (js-truthy o-numeric-raw)))
                       (o-numbering (locale-opt-string opts "numberingSystem"
                                      (lambda (s) (%opt-uvalue s "numberingSystem")))))
                  (let ((merged
                          (locale-apply-options tag
                            (list :language o-language :script o-script :region o-region
                                  :variants o-variants :calendar o-calendar :collation o-collation
                                  :hourcycle (unless (eq o-hourcycle :undefined) o-hourcycle)
                                  :casefirst (cond ((eq o-casefirst :undefined) nil)
                                                   (t o-casefirst))
                                  :firstdayofweek o-firstday
                                  :numeric (when o-numeric-present (if o-numeric "" "false"))
                                  :numberingsystem o-numbering))))
                    (let ((obj (make-object :proto (proto-from-newtarget nt proto) :class "Object")))
                      (setf (getf (js-object-internal obj) :initialized-locale) merged)
                      obj)))))))
    (def-value ctor "prototype" proto :writable nil :configurable nil)
    (def-value proto "constructor" ctor)
    ;; ---- getters ----
    (macrolet ((base-getter (name which)
                 `(def-getter realm proto ,name
                    (lambda (this args) (declare (ignore args))
                      (let* ((tag (locale-this-tag this))
                             (lid (parse-unicode-locale-id tag))
                             (v (locale-base-subtag lid ,which)))
                        (if v v *undefined*)))))
               (u-getter (name key)
                 `(def-getter realm proto ,name
                    (lambda (this args) (declare (ignore args))
                      (let* ((tag (locale-this-tag this))
                             (lid (parse-unicode-locale-id tag))
                             (v (locale-u-keyword-value lid ,key)))
                        (if v v *undefined*))))))
      (base-getter "language" :language)
      (base-getter "script" :script)
      (base-getter "region" :region)
      (base-getter "variants" :variants)
      (u-getter "calendar" "ca")
      (u-getter "collation" "co")
      (u-getter "hourCycle" "hc")
      (u-getter "caseFirst" "kf")
      (u-getter "numberingSystem" "nu"))
    ;; baseName
    (def-getter realm proto "baseName"
      (lambda (this args) (declare (ignore args))
        (base-name-string (parse-unicode-locale-id (locale-this-tag this)))))
    ;; numeric -> boolean (present kn && value != "false")
    (def-getter realm proto "numeric"
      (lambda (this args) (declare (ignore args))
        (let* ((lid (parse-unicode-locale-id (locale-this-tag this)))
               (v (locale-u-keyword-value lid "kn")))
          (js-bool (and v (not (string= v "false")))))))
    ;; firstDayOfWeek (string id) — returns the fw value or undefined
    (def-getter realm proto "firstDayOfWeek"
      (lambda (this args) (declare (ignore args))
        (let* ((lid (parse-unicode-locale-id (locale-this-tag this)))
               (v (locale-u-keyword-value lid "fw")))
          (if (and v (plusp (length v))) v *undefined*))))
    ;; ---- methods ----
    (def-method realm proto "toString" 0 (this args)
      (locale-this-tag this))
    (def-method realm proto "maximize" 0 (this args)
      (locale-transform realm proto this #'add-likely-subtags))
    (def-method realm proto "minimize" 0 (this args)
      (locale-transform realm proto this #'remove-likely-subtags))
    ;; ---- info methods (mostly shape) ----
    (def-method realm proto "getCalendars" 0 (this args)
      (locale-this-tag this)
      (make-array-object (list "gregory")))
    (def-method realm proto "getCollations" 0 (this args)
      (locale-this-tag this)
      (make-array-object (list "emoji" "pinyin")))
    (def-method realm proto "getHourCycles" 0 (this args)
      (locale-this-tag this)
      (make-array-object (list "h23")))
    (def-method realm proto "getNumberingSystems" 0 (this args)
      (locale-this-tag this)
      (make-array-object (list "latn")))
    (def-method realm proto "getTimeZones" 0 (this args)
      (let* ((lid (parse-unicode-locale-id (locale-this-tag this))))
        (if (locale-id-region lid)
            (make-array-object (list "America/New_York" "Europe/London"))
            *undefined*)))
    (def-method realm proto "getTextInfo" 0 (this args)
      (locale-this-tag this)
      (let ((o (make-object :proto (realm-object-proto realm) :class "Object")))
        (put o "direction" "ltr")
        o))
    (def-method realm proto "getWeekInfo" 0 (this args)
      (let* ((lid (parse-unicode-locale-id (locale-this-tag this)))
             (fw (locale-u-keyword-value lid "fw"))
             (day (or (cdr (assoc fw '(("mon" . 1) ("tue" . 2) ("wed" . 3) ("thu" . 4)
                                       ("fri" . 5) ("sat" . 6) ("sun" . 7)) :test #'equal))
                      1))
             (o (make-object :proto (realm-object-proto realm) :class "Object")))
        (put o "firstDay" (float day 1d0))
        (put o "weekend" (make-array-object (list 6d0 7d0)))
        o))
    ;; @@toStringTag
    (put proto (symbol-tostringtag realm) "Intl.Locale"
         :enumerable nil :writable nil :configurable t)
    (intl-register realm "Locale" ctor)
    ctor))

(defun locale-opt-string (opts key validator)
  "GetOption(opts,key,\"string\",...): read + ToString + validate, or :undefined."
  (let ((v (js-get opts key)))
    (if (js-undefined-p v)
        nil
        (funcall validator (to-string v)))))

(defun locale-transform (realm proto this fn)
  "maximize/minimize: parse [[Locale]], run FN on the base subtags (preserving
   extensions + privateuse), re-canonicalize, return a new Intl.Locale."
  (let* ((tag (locale-this-tag this))
         (lid (parse-unicode-locale-id tag))
         (transformed (funcall fn lid)))
    ;; FN returns a fresh lid with updated base subtags; keep ext/privateuse.
    (setf (locale-id-extensions transformed) (locale-id-extensions lid)
          (locale-id-privateuse transformed) (locale-id-privateuse lid))
    (let* ((str (lid->string (canonicalize-lid transformed)))
           (obj (make-object :proto proto :class "Object")))
      (declare (ignore realm))
      (setf (getf (js-object-internal obj) :initialized-locale) str)
      obj)))

(register-builtin-installer 'install-intl_locale)
