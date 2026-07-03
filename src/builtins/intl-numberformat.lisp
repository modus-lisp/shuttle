;;;; builtins/intl-numberformat.lisp — Intl.NumberFormat (ECMA-402 incl. V3).
;;;; Built ON the intl-core kernel (canonicalize-locale-list / resolve-locale /
;;;; GetOption family / +numbering-system-digits+ / intl-register).
;;;;
;;;; The whole numeric pipeline uses EXACT CL RATIONALS for rounding (never
;;;; float round-trips): a JS Number is converted to its shortest round-tripping
;;;; decimal (via %shortest-exp) then to a rational; a numeric String is parsed
;;;; exactly (ToIntlMathematicalValue); BigInt is already exact. All rounding /
;;;; increment / significant-digit math is on rationals, only rendered to digits
;;;; at the end.
;;;;
;;;; EXPORTED number-formatting helpers (PluralRules / DurationFormat reuse):
;;;;   (make-number-format realm locales options) -> nf JS object (internal slots)
;;;;   (nf-format-to-string nf x)   -> formatted string
;;;;   (nf-format-to-parts nf x)    -> list of (type . value) part conses
;;;;   (nf-resolved-plist nf)       -> the resolved-options plist
;;;;   (mv-from-value v)            -> ToIntlMathematicalValue: rational | :nan |
;;;;                                    :+inf | :-inf | :neg-zero
;;;;   (format-numeric-string resolved mv) -> the digit/pattern string for MV
(in-package #:shuttle)

(defvar *intl-numberformat-proto* nil)
(defvar *nf-legacy-symbol* nil
  "[[FallbackSymbol]] used by the ChainNumberFormat legacy constructor path.")

;;; Complete numbering-system digit table (superset of the kernel's), so digit
;;; substitution works for every system the harness enumerates.
(defparameter +nf-all-digits+
  '(
    ("adlm" . "𞥐𞥑𞥒𞥓𞥔𞥕𞥖𞥗𞥘𞥙")
    ("ahom" . "𑜰𑜱𑜲𑜳𑜴𑜵𑜶𑜷𑜸𑜹")
    ("arab" . "٠١٢٣٤٥٦٧٨٩")
    ("arabext" . "۰۱۲۳۴۵۶۷۸۹")
    ("bali" . "᭐᭑᭒᭓᭔᭕᭖᭗᭘᭙")
    ("beng" . "০১২৩৪৫৬৭৮৯")
    ("bhks" . "𑱐𑱑𑱒𑱓𑱔𑱕𑱖𑱗𑱘𑱙")
    ("brah" . "𑁦𑁧𑁨𑁩𑁪𑁫𑁬𑁭𑁮𑁯")
    ("cakm" . "𑄶𑄷𑄸𑄹𑄺𑄻𑄼𑄽𑄾𑄿")
    ("cham" . "꩐꩑꩒꩓꩔꩕꩖꩗꩘꩙")
    ("deva" . "०१२३४५६७८९")
    ("diak" . "𑥐𑥑𑥒𑥓𑥔𑥕𑥖𑥗𑥘𑥙")
    ("fullwide" . "０１２３４５６７８９")
    ("gara" . "𐵀𐵁𐵂𐵃𐵄𐵅𐵆𐵇𐵈𐵉")
    ("gong" . "𑶠𑶡𑶢𑶣𑶤𑶥𑶦𑶧𑶨𑶩")
    ("gonm" . "𑵐𑵑𑵒𑵓𑵔𑵕𑵖𑵗𑵘𑵙")
    ("gujr" . "૦૧૨૩૪૫૬૭૮૯")
    ("gukh" . "𖄰𖄱𖄲𖄳𖄴𖄵𖄶𖄷𖄸𖄹")
    ("guru" . "੦੧੨੩੪੫੬੭੮੯")
    ("hanidec" . "〇一二三四五六七八九")
    ("hmng" . "𖭐𖭑𖭒𖭓𖭔𖭕𖭖𖭗𖭘𖭙")
    ("hmnp" . "𞅀𞅁𞅂𞅃𞅄𞅅𞅆𞅇𞅈𞅉")
    ("java" . "꧐꧑꧒꧓꧔꧕꧖꧗꧘꧙")
    ("kali" . "꤀꤁꤂꤃꤄꤅꤆꤇꤈꤉")
    ("kawi" . "𑽐𑽑𑽒𑽓𑽔𑽕𑽖𑽗𑽘𑽙")
    ("khmr" . "០១២៣៤៥៦៧៨៩")
    ("knda" . "೦೧೨೩೪೫೬೭೮೯")
    ("krai" . "𖵰𖵱𖵲𖵳𖵴𖵵𖵶𖵷𖵸𖵹")
    ("lana" . "᪀᪁᪂᪃᪄᪅᪆᪇᪈᪉")
    ("lanatham" . "᪐᪑᪒᪓᪔᪕᪖᪗᪘᪙")
    ("laoo" . "໐໑໒໓໔໕໖໗໘໙")
    ("latn" . "0123456789")
    ("lepc" . "᱀᱁᱂᱃᱄᱅᱆᱇᱈᱉")
    ("limb" . "᥆᥇᥈᥉᥊᥋᥌᥍᥎᥏")
    ("mathbold" . "𝟎𝟏𝟐𝟑𝟒𝟓𝟔𝟕𝟖𝟗")
    ("mathdbl" . "𝟘𝟙𝟚𝟛𝟜𝟝𝟞𝟟𝟠𝟡")
    ("mathmono" . "𝟶𝟷𝟸𝟹𝟺𝟻𝟼𝟽𝟾𝟿")
    ("mathsanb" . "𝟬𝟭𝟮𝟯𝟰𝟱𝟲𝟳𝟴𝟵")
    ("mathsans" . "𝟢𝟣𝟤𝟥𝟦𝟧𝟨𝟩𝟪𝟫")
    ("mlym" . "൦൧൨൩൪൫൬൭൮൯")
    ("modi" . "𑙐𑙑𑙒𑙓𑙔𑙕𑙖𑙗𑙘𑙙")
    ("mong" . "᠐᠑᠒᠓᠔᠕᠖᠗᠘᠙")
    ("mroo" . "𖩠𖩡𖩢𖩣𖩤𖩥𖩦𖩧𖩨𖩩")
    ("mtei" . "꯰꯱꯲꯳꯴꯵꯶꯷꯸꯹")
    ("mymr" . "၀၁၂၃၄၅၆၇၈၉")
    ("mymrepka" . "𑛚𑛛𑛜𑛝𑛞𑛟𑛠𑛡𑛢𑛣")
    ("mymrpao" . "𑛐𑛑𑛒𑛓𑛔𑛕𑛖𑛗𑛘𑛙")
    ("mymrshan" . "႐႑႒႓႔႕႖႗႘႙")
    ("mymrtlng" . "꧰꧱꧲꧳꧴꧵꧶꧷꧸꧹")
    ("nagm" . "𞓰𞓱𞓲𞓳𞓴𞓵𞓶𞓷𞓸𞓹")
    ("newa" . "𑑐𑑑𑑒𑑓𑑔𑑕𑑖𑑗𑑘𑑙")
    ("nkoo" . "߀߁߂߃߄߅߆߇߈߉")
    ("olck" . "᱐᱑᱒᱓᱔᱕᱖᱗᱘᱙")
    ("onao" . "𞗱𞗲𞗳𞗴𞗵𞗶𞗷𞗸𞗹𞗺")
    ("orya" . "୦୧୨୩୪୫୬୭୮୯")
    ("osma" . "𐒠𐒡𐒢𐒣𐒤𐒥𐒦𐒧𐒨𐒩")
    ("outlined" . "𜳰𜳱𜳲𜳳𜳴𜳵𜳶𜳷𜳸𜳹")
    ("rohg" . "𐴰𐴱𐴲𐴳𐴴𐴵𐴶𐴷𐴸𐴹")
    ("saur" . "꣐꣑꣒꣓꣔꣕꣖꣗꣘꣙")
    ("segment" . "🯰🯱🯲🯳🯴🯵🯶🯷🯸🯹")
    ("shrd" . "𑇐𑇑𑇒𑇓𑇔𑇕𑇖𑇗𑇘𑇙")
    ("sind" . "𑋰𑋱𑋲𑋳𑋴𑋵𑋶𑋷𑋸𑋹")
    ("sinh" . "෦෧෨෩෪෫෬෭෮෯")
    ("sora" . "𑃰𑃱𑃲𑃳𑃴𑃵𑃶𑃷𑃸𑃹")
    ("sund" . "᮰᮱᮲᮳᮴᮵᮶᮷᮸᮹")
    ("sunu" . "𑯰𑯱𑯲𑯳𑯴𑯵𑯶𑯷𑯸𑯹")
    ("takr" . "𑛀𑛁𑛂𑛃𑛄𑛅𑛆𑛇𑛈𑛉")
    ("talu" . "᧐᧑᧒᧓᧔᧕᧖᧗᧘᧙")
    ("tamldec" . "௦௧௨௩௪௫௬௭௮௯")
    ("telu" . "౦౧౨౩౪౫౬౭౮౯")
    ("thai" . "๐๑๒๓๔๕๖๗๘๙")
    ("tibt" . "༠༡༢༣༤༥༦༧༨༩")
    ("tirh" . "𑓐𑓑𑓒𑓓𑓔𑓕𑓖𑓗𑓘𑓙")
    ("tnsa" . "𖫀𖫁𖫂𖫃𖫄𖫅𖫆𖫇𖫈𖫉")
    ("tols" . "𑷠𑷡𑷢𑷣𑷤𑷥𑷦𑷧𑷨𑷩")
    ("vaii" . "꘠꘡꘢꘣꘤꘥꘦꘧꘨꘩")
    ("wara" . "𑣠𑣡𑣢𑣣𑣤𑣥𑣦𑣧𑣨𑣩")
    ("wcho" . "𞋰𞋱𞋲𞋳𞋴𞋵𞋶𞋷𞋸𞋹")
    ))


(defun nf-digits-for (nu)
  (or (cdr (assoc nu +nf-all-digits+ :test #'string=))
      (cdr (assoc nu +numbering-system-digits+ :test #'string=))
      "0123456789"))


;;; ===========================================================================
;;; Internal-slot access
;;; ===========================================================================
(defun nf-slots (this)
  "RequireInternalSlot [[InitializedNumberFormat]] -> the internal plist, else NIL."
  (and (js-object-p this) (js-object-internal this)
       (getf (js-object-internal this) :nf)))

(defun require-nf (this)
  "UnwrapNumberFormat + RequireInternalSlot: THIS itself, or a wrapped object
   carrying the NF under the [[FallbackSymbol]]."
  (or (nf-slots this)
      (and (js-object-p this) *nf-legacy-symbol*
           (let ((inner (js-get this *nf-legacy-symbol*)))
             (and (js-object-p inner) (nf-slots inner))))
      (js-throw (make-native-error "TypeError" "receiver is not an Intl.NumberFormat"))))

(defun nf-resolved-plist (nf) (getf nf :resolved))
(defun nf-get (nf key) (getf (getf nf :resolved) key))

;;; ===========================================================================
;;; Currency / unit data
;;; ===========================================================================
;;; CurrencyDigits: minor-unit counts that are not the default 2.
(defparameter +currency-digits+
  '(("BHD" . 3) ("BIF" . 0) ("CLF" . 4) ("CLP" . 0) ("DJF" . 0) ("GNF" . 0)
    ("IQD" . 3) ("ISK" . 0) ("JOD" . 3) ("JPY" . 0) ("KMF" . 0) ("KRW" . 0)
    ("KWD" . 3) ("LYD" . 3) ("OMR" . 3) ("PYG" . 0) ("RWF" . 0) ("TND" . 3)
    ("UGX" . 0) ("UYI" . 0) ("UYW" . 4) ("VND" . 0) ("VUV" . 0) ("XAF" . 0)
    ("XOF" . 0) ("XPF" . 0)))

(defun currency-digits (currency)
  (or (cdr (assoc currency +currency-digits+ :test #'string=)) 2))

;;; en currency symbol/name (narrowSymbol == symbol for these). Fallback: code.
(defparameter +currency-symbol+
  '(("USD" . "$") ("EUR" . "€") ("GBP" . "£") ("JPY" . "¥") ("CNY" . "CN¥")
    ("AUD" . "A$") ("CAD" . "CA$") ("HKD" . "HK$") ("INR" . "₹") ("KRW" . "₩")
    ("BRL" . "R$") ("MXN" . "MX$") ("NZD" . "NZ$") ("CHF" . "CHF") ("XDR" . "XDR")))
(defparameter +currency-narrow+
  '(("USD" . "$") ("EUR" . "€") ("GBP" . "£") ("JPY" . "¥") ("CNY" . "¥")
    ("AUD" . "$") ("CAD" . "$") ("HKD" . "$") ("INR" . "₹") ("KRW" . "₩")
    ("BRL" . "R$") ("MXN" . "$") ("NZD" . "$")))
(defparameter +currency-name+
  '(("USD" . ("US dollar" . "US dollars")) ("EUR" . ("euro" . "euros"))
    ("GBP" . ("British pound" . "British pounds")) ("JPY" . ("Japanese yen" . "Japanese yen"))
    ("CNY" . ("Chinese yuan" . "Chinese yuan"))))

(defun currency-symbol (currency display)
  (cond ((string= display "code") currency)
        ((string= display "narrowSymbol")
         (or (cdr (assoc currency +currency-narrow+ :test #'string=))
             (cdr (assoc currency +currency-symbol+ :test #'string=))
             currency))
        ((string= display "name") nil) ; handled via plural name
        (t ;; symbol
         (or (cdr (assoc currency +currency-symbol+ :test #'string=)) currency))))

;;; Unit display names (en). Each: (singular-short . plural-short) etc. We map
;;; simple sanctioned units + build compound "per" forms.
(defparameter +unit-names+
  ;; unit -> (:short-s :short-p :narrow-s :narrow-p :long-s :long-p)
  '(("acre" "ac" "ac" "ac" "ac" "acre" "acres")
    ("bit" "bit" "bit" "bit" "bit" "bit" "bits")
    ("byte" "byte" "byte" "B" "B" "byte" "bytes")
    ("celsius" "°C" "°C" "°" "°" "degree Celsius" "degrees Celsius")
    ("centimeter" "cm" "cm" "cm" "cm" "centimeter" "centimeters")
    ("day" "day" "days" "d" "d" "day" "days")
    ("degree" "deg" "deg" "°" "°" "degree" "degrees")
    ("fahrenheit" "°F" "°F" "°" "°" "degree Fahrenheit" "degrees Fahrenheit")
    ("fluid-ounce" "fl oz" "fl oz" "fl oz" "fl oz" "fluid ounce" "fluid ounces")
    ("foot" "ft" "ft" "ft" "ft" "foot" "feet")
    ("gallon" "gal" "gal" "gal" "gal" "gallon" "gallons")
    ("gigabit" "Gb" "Gb" "Gb" "Gb" "gigabit" "gigabits")
    ("gigabyte" "GB" "GB" "GB" "GB" "gigabyte" "gigabytes")
    ("gram" "g" "g" "g" "g" "gram" "grams")
    ("hectare" "ha" "ha" "ha" "ha" "hectare" "hectares")
    ("hour" "hr" "hr" "h" "h" "hour" "hours")
    ("inch" "in" "in" "in" "in" "inch" "inches")
    ("kilobit" "kb" "kb" "kb" "kb" "kilobit" "kilobits")
    ("kilobyte" "kB" "kB" "kB" "kB" "kilobyte" "kilobytes")
    ("kilogram" "kg" "kg" "kg" "kg" "kilogram" "kilograms")
    ("kilometer" "km" "km" "km" "km" "kilometer" "kilometers")
    ("liter" "L" "L" "L" "L" "liter" "liters")
    ("megabit" "Mb" "Mb" "Mb" "Mb" "megabit" "megabits")
    ("megabyte" "MB" "MB" "MB" "MB" "megabyte" "megabytes")
    ("meter" "m" "m" "m" "m" "meter" "meters")
    ("microsecond" "μs" "μs" "μs" "μs" "microsecond" "microseconds")
    ("mile" "mi" "mi" "mi" "mi" "mile" "miles")
    ("mile-scandinavian" "smi" "smi" "smi" "smi" "mile-scandinavian" "miles-scandinavian")
    ("milliliter" "mL" "mL" "mL" "mL" "milliliter" "milliliters")
    ("millimeter" "mm" "mm" "mm" "mm" "millimeter" "millimeters")
    ("millisecond" "ms" "ms" "ms" "ms" "millisecond" "milliseconds")
    ("minute" "min" "min" "min" "min" "minute" "minutes")
    ("month" "mth" "mths" "m" "m" "month" "months")
    ("nanosecond" "ns" "ns" "ns" "ns" "nanosecond" "nanoseconds")
    ("ounce" "oz" "oz" "oz" "oz" "ounce" "ounces")
    ("percent" "%" "%" "%" "%" "percent" "percent")
    ("petabyte" "PB" "PB" "PB" "PB" "petabyte" "petabytes")
    ("pound" "lb" "lb" "lb" "lb" "pound" "pounds")
    ("second" "sec" "sec" "s" "s" "second" "seconds")
    ("stone" "st" "st" "st" "st" "stone" "stone")
    ("terabit" "Tb" "Tb" "Tb" "Tb" "terabit" "terabits")
    ("terabyte" "TB" "TB" "TB" "TB" "terabyte" "terabytes")
    ("week" "wk" "wks" "w" "w" "week" "weeks")
    ("yard" "yd" "yd" "yd" "yd" "yard" "yards")
    ("year" "yr" "yrs" "y" "y" "year" "years")))

(defparameter +sanctioned-units+
  (mapcar #'first +unit-names+))

(defun sanctioned-unit-p (u) (member u +sanctioned-units+ :test #'string=))

;;; ===========================================================================
;;; IsWellFormedCurrencyCode / IsWellFormedUnitIdentifier
;;; ===========================================================================
(defun well-formed-currency-p (s)
  (and (stringp s) (= (length s) 3) (every #'%alpha-p s)))

(defun well-formed-unit-p (s)
  "IsWellFormedUnitIdentifier: a sanctioned simple unit, or 'X-per-Y' where X,Y
   are sanctioned simple units."
  (let ((pos (search "-per-" s)))
    (if pos
        (let ((num (subseq s 0 pos)) (den (subseq s (+ pos 5))))
          (and (sanctioned-unit-p num) (sanctioned-unit-p den)
               (not (search "-per-" den)))) ; only one per
        (sanctioned-unit-p s))))

;;; ===========================================================================
;;; SetNumberFormatDigitOptions  (ECMA-402 V3)
;;; ===========================================================================
(defun set-nf-digit-options (opts resolved mnfd-default mxfd-default notation)
  "Reads minimum/maximumFractionDigits, minimum/maximumSignificantDigits,
   roundingIncrement, roundingMode, roundingPriority, trailingZeroDisplay into
   RESOLVED (a plist accumulator, modified via setf and returned)."
  (declare (ignore notation))
  (let* ((mnid (get-number-option opts "minimumIntegerDigits" 1 21 1))
         (mnfd (js-get opts "minimumFractionDigits"))
         (mxfd (js-get opts "maximumFractionDigits"))
         (mnsd (js-get opts "minimumSignificantDigits"))
         (mxsd (js-get opts "maximumSignificantDigits"))
         (rinc (get-number-option opts "roundingIncrement" 1 5000 1))
         (rmode (get-option opts "roundingMode" :string
                            '("ceil" "floor" "expand" "trunc" "halfCeil" "halfFloor"
                              "halfExpand" "halfTrunc" "halfEven") "halfExpand"))
         (rpri (get-option opts "roundingPriority" :string
                           '("auto" "morePrecision" "lessPrecision") "auto"))
         (tzd (get-option opts "trailingZeroDisplay" :string
                          '("auto" "stripIfInteger") "auto")))
    ;; roundingIncrement must be in the sanctioned set.
    (unless (member rinc '(1 2 5 10 20 25 50 100 200 250 500 1000 2000 2500 5000))
      (js-throw (make-native-error "RangeError" "invalid roundingIncrement")))
    (setf (getf resolved :minimum-integer-digits) mnid
          (getf resolved :rounding-increment) rinc
          (getf resolved :rounding-mode) rmode
          (getf resolved :rounding-priority) rpri
          (getf resolved :trailing-zero-display) tzd)
    (let* ((has-sd (not (and (js-undefined-p mnsd) (js-undefined-p mxsd))))
           (has-fd (not (and (js-undefined-p mnfd) (js-undefined-p mxfd))))
           (need-sd nil) (need-fd nil))
      (when (or has-sd has-fd (string/= rpri "auto"))
        (setf (getf resolved :user-digits) t))
      ;; roundingIncrement != 1 hard constraints (V3):
      ;; roundingType must be fractionDigits — i.e. no significant digits and
      ;; roundingPriority must be "auto".
      (when (/= rinc 1)
        (when (or has-sd (string/= rpri "auto"))
          (js-throw (make-native-error "TypeError"
                     "roundingIncrement requires fractionDigits rounding"))))
      ;; needSd / needFd per roundingPriority
      (cond
        ((string= rpri "morePrecision") (setf need-sd t need-fd t))
        ((string= rpri "lessPrecision") (setf need-sd t need-fd t))
        (t ;; auto
         (setf need-sd has-sd)
         (setf need-fd (or (not has-sd) has-fd))))
      ;; Significant digits
      (when need-sd
        (let ((rmnsd (default-number-option mnsd 1 21 1))
              (rmxsd (default-number-option mxsd 1 21 21)))
          (when has-sd
            (setf rmnsd (default-number-option mnsd 1 21 1))
            (setf rmxsd (default-number-option mxsd (max 1 rmnsd) 21 21))
            (when (> rmnsd rmxsd)
              (js-throw (make-native-error "RangeError" "min > max significant digits"))))
          (setf (getf resolved :min-significant) rmnsd
                (getf resolved :max-significant) rmxsd)))
      ;; Fraction digits
      (when need-fd
        (multiple-value-bind (rmnfd rmxfd)
            (resolve-fraction-digits mnfd mxfd mnfd-default mxfd-default (/= rinc 1))
          ;; With roundingIncrement != 1, mnfd must equal mxfd.
          (when (and (/= rinc 1) (/= rmnfd rmxfd))
            (js-throw (make-native-error "RangeError"
                       "minimumFractionDigits must equal maximumFractionDigits with roundingIncrement")))
          (setf (getf resolved :min-fraction) rmnfd
                (getf resolved :max-fraction) rmxfd)))
      ;; Determine the effective rounding type for the pipeline.
      (setf (getf resolved :round-type)
            (cond
              ((string= rpri "morePrecision") :morePrecision)
              ((string= rpri "lessPrecision") :lessPrecision)
              (has-sd :significant)
              (t :fraction)))))
  resolved)

(defun resolve-fraction-digits (mnfd mxfd mnfd-default mxfd-default &optional inc-set)
  "Return (values mnfd mxfd) resolved per SetNumberFormatDigitOptions."
  (let ((rmnfd (unless (js-undefined-p mnfd) (default-number-option mnfd 0 100 0)))
        (rmxfd (unless (js-undefined-p mxfd) (default-number-option mxfd 0 100 0))))
    ;; With a non-unit roundingIncrement, an unspecified fraction bound collapses
    ;; onto the other so that mnfd == mxfd (spec: mxfdDefault = mnfdDefault).
    (when inc-set
      (cond ((and rmnfd (null rmxfd)) (setf rmxfd rmnfd))
            ((and rmxfd (null rmnfd)) (setf rmnfd rmxfd))
            ((and (null rmnfd) (null rmxfd))
             (setf rmnfd mnfd-default rmxfd mnfd-default))))
    (cond
      ((and (null rmnfd) (null rmxfd))
       (values mnfd-default (max mnfd-default mxfd-default)))
      ((null rmxfd)
       ;; only mnfd given
       (values rmnfd (max rmnfd mxfd-default)))
      ((null rmnfd)
       ;; only mxfd given
       (when (< rmxfd 0) (js-throw (make-native-error "RangeError" "bad mxfd")))
       (values (min mnfd-default rmxfd) rmxfd))
      (t
       (when (> rmnfd rmxfd)
         (js-throw (make-native-error "RangeError" "minimumFractionDigits > maximumFractionDigits")))
       (values rmnfd rmxfd)))))

;;; ===========================================================================
;;; ToIntlMathematicalValue
;;; ===========================================================================
(defun number->rational-mv (x)
  "A double float X -> exact rational, or a keyword for special values."
  (cond
    ((/= x x) :nan)
    ((= x sb-ext:double-float-positive-infinity) :+inf)
    ((= x sb-ext:double-float-negative-infinity) :-inf)
    ((and (zerop x) (minusp (float-sign x))) :neg-zero)
    ((zerop x) 0)
    (t
     (multiple-value-bind (sig e) (%shortest-exp (abs x))
       (let* ((n (parse-integer sig))
              (scale (- e (1- (length sig))))
              (mag (if (>= scale 0)
                       (* n (expt 10 scale))
                       (/ n (expt 10 (- scale))))))
         (if (minusp x) (- mag) mag))))))

(defun string->rational-mv (s)
  "StringIntlMV: parse a StrDecimalLiteral exactly to a rational, or keyword.
   Handles Infinity/-Infinity, decimal, exponent, hex/oct/bin integer literals."
  (let ((s (string-trim +js-ws+ s)))
    (cond
      ((string= s "") 0)
      ((string= s "Infinity") :+inf)
      ((string= s "+Infinity") :+inf)
      ((string= s "-Infinity") :-inf)
      ((and (>= (length s) 2) (char= (char s 0) #\0) (member (char s 1) '(#\x #\X)))
       (or (and (> (length s) 2) (ignore-errors (parse-integer s :start 2 :radix 16))) :nan))
      ((and (>= (length s) 2) (char= (char s 0) #\0) (member (char s 1) '(#\o #\O)))
       (or (and (> (length s) 2) (ignore-errors (parse-integer s :start 2 :radix 8))) :nan))
      ((and (>= (length s) 2) (char= (char s 0) #\0) (member (char s 1) '(#\b #\B)))
       (or (and (> (length s) 2) (ignore-errors (parse-integer s :start 2 :radix 2))) :nan))
      (t (parse-decimal-rational s)))))

(defun parse-decimal-rational (s)
  "Parse a decimal literal [+-]?digits(.digits)?([eE][+-]?digits)? exactly."
  (let ((i 0) (n (length s)) (sign 1))
    (when (and (< i n) (member (char s i) '(#\+ #\-)))
      (when (char= (char s i) #\-) (setf sign -1))
      (incf i))
    (let ((frac-digits 0) (mant 0) (any nil))
      (loop while (and (< i n) (digit-char-p (char s i)))
            do (setf mant (+ (* mant 10) (digit-char-p (char s i))) any t) (incf i))
      (when (and (< i n) (char= (char s i) #\.))
        (incf i)
        (loop while (and (< i n) (digit-char-p (char s i)))
              do (setf mant (+ (* mant 10) (digit-char-p (char s i))) any t)
                 (incf frac-digits) (incf i)))
      (unless any (return-from parse-decimal-rational :nan))
      (let ((exp 0))
        (when (and (< i n) (member (char s i) '(#\e #\E)))
          (incf i)
          (let ((esign 1) (eany nil))
            (when (and (< i n) (member (char s i) '(#\+ #\-)))
              (when (char= (char s i) #\-) (setf esign -1)) (incf i))
            (loop while (and (< i n) (digit-char-p (char s i)))
                  do (setf exp (+ (* exp 10) (digit-char-p (char s i))) eany t) (incf i))
            (unless eany (return-from parse-decimal-rational :nan))
            (setf exp (* esign exp))))
        (unless (= i n) (return-from parse-decimal-rational :nan))
        (let* ((scale (- exp frac-digits))
               (mag (if (>= scale 0) (* mant (expt 10 scale)) (/ mant (expt 10 (- scale))))))
          (let ((v (* sign mag)))
            (if (and (zerop v) (= sign -1)) :neg-zero v)))))))

(defun mv-from-value (v)
  "ToIntlMathematicalValue(v): -> rational | :nan | :+inf | :-inf | :neg-zero.
   Number, BigInt, or numeric String accepted exactly; others via ToNumber."
  (cond
    ((stringp v) (string->rational-mv v))
    ((js-bigint-p v) (if (and (zerop v)) 0 v))
    ((floatp v) (number->rational-mv v))
    (t (let ((p (to-primitive v :number)))
         (cond ((stringp p) (string->rational-mv p))
               ((js-bigint-p p) p)
               (t (number->rational-mv (to-number p))))))))

;;; ===========================================================================
;;; Rounding machinery (all on rationals)
;;; ===========================================================================
(defun nf-round-to-increment (x mode)
  "Round rational X to the nearest integer per MODE (roundingMode string)."
  (multiple-value-bind (q r) (truncate x)
    (if (zerop r)
        q
        (let* ((neg (minusp x))
               (rr (abs r)))                 ; 0<rr<1 fractional part magnitude
          (flet ((up () (if neg (1- q) (1+ q)))  ; away from zero magnitude-wise
                 (down () q))                     ; toward zero
            ;; Note q is trunc toward zero already; "up" adds magnitude.
            (cond
              ((string= mode "trunc") (down))
              ((string= mode "ceil") (if neg (down) (up)))
              ((string= mode "floor") (if neg (up) (down)))
              ((string= mode "expand") (up))
              (t ;; half-* modes: compare rr to 1/2
               (cond
                 ((< rr 1/2) (down))
                 ((> rr 1/2) (up))
                 (t ;; exactly half
                  (cond
                    ((string= mode "halfTrunc") (down))
                    ((string= mode "halfExpand") (up))
                    ((string= mode "halfCeil") (if neg (down) (up)))
                    ((string= mode "halfFloor") (if neg (up) (down)))
                    ((string= mode "halfEven")
                     (if (evenp q) (down) (up)))
                    (t (up))))))))))))

(defvar *rounding-negative* nil
  "Bound to T while formatting a negative value so directional rounding modes
   (ceil/floor/halfCeil/halfFloor) act on the true sign, not the magnitude.")

(defun effective-mode (mode)
  "Swap ceil<->floor (and half variants) when formatting a negative magnitude,
   since rounding runs on the absolute value."
  (if (not *rounding-negative*)
      mode
      (cond ((string= mode "ceil") "floor")
            ((string= mode "floor") "ceil")
            ((string= mode "halfCeil") "halfFloor")
            ((string= mode "halfFloor") "halfCeil")
            (t mode))))

(defun apply-rounding (mag round-type resolved)
  "MAG is a non-negative rational. Returns (values rounded-rational
   effective-min-fraction effective-max-fraction significant-p exponent), where
   the result is expressed for rendering. We produce a scaled rounded rational
   plus the fraction-digit bounds that govern trailing zeros.
   Returns: (values rounded-value min-frac max-frac)."
  (let ((mode (effective-mode (getf resolved :rounding-mode)))
        (inc (getf resolved :rounding-increment)))
    (labels
        ((round-fraction (m maxf)
           ;; round m to maxf fraction digits (increment applied in those units)
           (let* ((scale (expt 10 maxf))
                  (scaled (* m scale))
                  (rounded (if (= inc 1)
                               (nf-round-to-increment scaled mode)
                               (* inc (nf-round-to-increment (/ scaled inc) mode)))))
             (/ rounded scale)))
         (round-significant (m maxs)
           (if (zerop m)
               (values 0 0)
             (let* ((e (floor (log-int-floor m)))         ; position of MSD
                    ;; number of digits before decimal chosen so we keep maxs sig digits
                    (shift (- maxs 1 e))
                    (scale (expt 10 (abs shift)))
                    (scaled (if (>= shift 0) (* m scale) (/ m scale)))
                    (rounded (nf-round-to-increment scaled mode))
                    (val (if (>= shift 0) (/ rounded scale) (* rounded scale))))
               ;; rounding may bump digit count (e.g. 9.99 -> 10.0); recompute e
               (values val e)))))
      (ecase (getf resolved :round-type)
        (:fraction
         (let ((v (round-fraction mag (getf resolved :max-fraction))))
           (values v (getf resolved :min-fraction) (getf resolved :max-fraction) nil)))
        (:significant
         (multiple-value-bind (v e) (round-significant mag (getf resolved :max-significant))
           (declare (ignore e))
           (values v nil nil t)))
        ((:morePrecision :lessPrecision)
         ;; Compare the ROUNDING POSITION (exponent of least-significant digit)
         ;; each MAX constraint would produce; morePrecision picks the smaller
         ;; (more precise) position, lessPrecision the larger.
         (let* ((maxf (getf resolved :max-fraction))
                (maxs (getf resolved :max-significant))
                (e (if (zerop mag) 0 (log-int-floor mag)))
                (frac-pos (- maxf))            ; fraction: least digit at 10^-maxf
                (sig-pos (+ (- e maxs) 1))     ; significant: least digit at 10^(e-maxs+1)
                (use-frac
                  (if (eq (getf resolved :round-type) :morePrecision)
                      (<= frac-pos sig-pos)     ; frac reaches at least as deep
                      (>= frac-pos sig-pos))))
           (if use-frac
               (values (round-fraction mag maxf)
                       (getf resolved :min-fraction) maxf nil)
               (values (round-significant mag maxs) nil nil t))))))))

(defun log-int-floor (m)
  "floor(log10(m)) for a positive rational M, computed exactly: the integer E
   with 10^E <= M < 10^(E+1)."
  (cond
    ((>= m 1)
     (let ((e 0) (v 1))
       (loop while (<= (* v 10) m) do (setf v (* v 10)) (incf e))
       e))
    (t
     (let ((e 0) (v 1))
       (loop while (> v m) do (setf v (/ v 10)) (decf e))
       e))))

(defun significant-fraction-count (v maxs)
  (declare (ignore maxs))
  ;; count fraction digits actually present in V (a rational rounded to sig digits)
  (if (zerop v) 0
      (let ((denom (denominator v)))
        (if (= denom 1) 0
            ;; denom is a power of 2*5; count decimal places
            (let ((places 0) (d denom))
              (loop while (> d 1) do
                (cond ((zerop (mod d 10)) (setf d (/ d 10)))
                      ((zerop (mod d 2)) (setf d (/ d 5)) (incf places))
                      ((zerop (mod d 5)) (setf d (/ d 2)) (incf places))
                      (t (return))))
              (loop while (> d 1) do (setf d (floor d 10)) (incf places))
              places)))))

;;; ===========================================================================
;;; Rendering: rational -> digit string with min/max integer/fraction digits
;;; ===========================================================================
(defun render-decimal (value min-int min-frac max-frac significant-p resolved)
  "VALUE is a non-negative rounded rational. Return a plain ASCII decimal string
   (western digits, '.' as decimal, no grouping/sign). Applies min integer digits,
   trailing-zero rules."
  (declare (ignore max-frac))
  (let* ((tzd (getf resolved :trailing-zero-display))
         (int-part 0) (frac-str ""))
    (multiple-value-bind (q r) (truncate value)
      (setf int-part q)
      (when (plusp r)
        ;; r is a rational in [0,1); express as decimal digits exactly
        (setf frac-str (rational-fraction-digits r))))
    (let ((int-str (format nil "~d" int-part)))
      ;; min integer digits (pad left with 0)
      (when (< (length int-str) min-int)
        (setf int-str (concatenate 'string
                                   (make-string (- min-int (length int-str)) :initial-element #\0)
                                   int-str)))
      ;; fraction: enforce min-frac (pad) unless significant path drives it.
      (cond
        (significant-p
         (let* ((minsig (getf resolved :min-significant))
                (maxsig (getf resolved :max-significant)))
           (setf frac-str (adjust-significant-fraction int-part frac-str minsig maxsig))))
        (t
         (when min-frac
           (when (< (length frac-str) min-frac)
             (setf frac-str (concatenate 'string frac-str
                                         (make-string (- min-frac (length frac-str)) :initial-element #\0)))))))
      ;; trailingZeroDisplay stripIfInteger: if the value is an integer, drop fraction.
      (when (and (string= tzd "stripIfInteger") (zerop (truncate (* value 1))))
        nil)
      (when (and (string= tzd "stripIfInteger")
                 (integerp value))
        (setf frac-str ""))
      (if (plusp (length frac-str))
          (concatenate 'string int-str "." frac-str)
          int-str))))

(defun rational-fraction-digits (r)
  "R in [0,1) rational whose denominator divides a power of 10 (after rounding).
   Return the fractional digit string (no trailing-zero stripping)."
  (let ((digits '()) (x r))
    (loop while (and (plusp x)) do
      (setf x (* x 10))
      (multiple-value-bind (d rem) (truncate x)
        (push (code-char (+ (char-code #\0) d)) digits)
        (setf x rem))
      (when (> (length digits) 100) (return)))
    (coerce (nreverse digits) 'string)))

(defun adjust-significant-fraction (int-part frac-str minsig maxsig)
  "Given the integer part and current fraction string, pad the fraction so that
   the count of significant digits reaches MINSIG (min pads with trailing 0)."
  (declare (ignore maxsig))
  (let* ((int-str (format nil "~d" int-part))
         (nonzero-int (not (string= int-str "0")))
         ;; count of significant digits already present
         (cur-sig
           (cond
             (nonzero-int (+ (length int-str) (length frac-str)))
             ;; int is 0: significant digits are those in frac AFTER the leading
             ;; zeros; but if the whole value is exactly 0, the single "0" counts.
             ((every (lambda (c) (char= c #\0)) frac-str)
              (if (zerop (length frac-str)) 1 1))   ; value is zero -> 1 sig digit
             (t (let ((lead (or (position-if (lambda (c) (char/= c #\0)) frac-str) 0)))
                  (- (length frac-str) lead))))))
    (when (< cur-sig minsig)
      (setf frac-str (concatenate 'string frac-str
                                  (make-string (- minsig cur-sig) :initial-element #\0))))
    frac-str))

;;; ===========================================================================
;;; Compact notation (en) — short/long
;;; ===========================================================================
(defparameter +compact-short+
  '((3 . "K") (6 . "M") (9 . "B") (12 . "T")))
(defparameter +compact-long+
  '((3 . "thousand") (6 . "million") (9 . "billion") (12 . "trillion")))

;;; ===========================================================================
;;; The core numeric formatter -> list of parts
;;; ===========================================================================
(defun format-numeric-parts (resolved mv)
  "Return a list of (type . value) part conses for MV per RESOLVED."
  (let* ((style (getf resolved :style))
         (notation (getf resolved :notation))
         (sign-display (getf resolved :sign-display))
         (nu (getf resolved :numbering-system))
         (digits (nf-digits-for nu))
         (parts '()))
    ;; sign determination
    (let* ((negative (or (eq mv :-inf) (eq mv :neg-zero)
                         (and (rationalp mv) (minusp mv))))
           (is-zero (or (eq mv :neg-zero) (and (rationalp mv) (zerop mv))))
           (is-nan (eq mv :nan))
           (nan-or-inf (member mv '(:nan :+inf :-inf))))
      ;; percent scaling ( :neg-zero -> exact 0 magnitude, sign tracked separately)
      (let ((work (if (eq mv :neg-zero) 0 mv)))
        (when (and (string= style "percent") (rationalp work))
          (setf work (* work 100)))
        (let* ((mag (cond (nan-or-inf work) (t (abs work))))
               ;; render the number core FIRST so signDisplay can inspect the
               ;; rounded result (e.g. -0.0001 -> "0" is treated as zero).
               (number-parts
                 (let ((*rounding-negative* negative))
                   (cond
                     (is-nan (list (cons "nan" "NaN")))
                     ((member work '(:+inf :-inf)) (list (cons "infinity" "∞")))
                     (t (render-number-core resolved mag digits notation)))))
               ;; Is the displayed numeric value zero (all digits 0)?
               (rendered-zero
                 (and (not nan-or-inf)
                      (every (lambda (p)
                               (if (member (car p) '("integer" "fraction") :test #'string=)
                                   (every (lambda (c) (or (not (digit-value-p c digits))
                                                          (digit-is-zero-p c digits)))
                                          (cdr p))
                                   t))
                             number-parts)))
               (effective-zero (or is-zero rendered-zero))
               (show-sign
                 (cond
                   ((string= sign-display "never") nil)
                   ((string= sign-display "always") (if negative :minus :plus))
                   ((string= sign-display "exceptZero")
                    (cond (is-nan nil) (effective-zero nil) (negative :minus) (t :plus)))
                   ((string= sign-display "negative")
                    (cond ((and negative (not effective-zero)) :minus) (t nil)))
                   (t ;; auto
                    (if negative :minus nil)))))
          (setf parts (assemble-with-affixes resolved show-sign number-parts style)))))
    parts))

(defun digit-value-p (c digits)
  (or (char<= #\0 c #\9) (find c digits)))
(defun digit-is-zero-p (c digits)
  (or (char= c #\0) (and (plusp (length digits)) (char= c (char digits 0)))))

(defun render-number-core (resolved mag digits notation)
  "MAG is a non-negative rational (or special already handled). Returns integer/
   group/decimal/fraction (+compact/exponent) parts, digits substituted."
  (cond
    ((string= notation "compact")
     (render-compact resolved mag digits))
    ((or (string= notation "scientific") (string= notation "engineering"))
     (render-scientific resolved mag digits notation))
    (t (render-standard resolved mag digits))))

(defun rounded-magnitude (resolved mag)
  (multiple-value-bind (v minf maxf sig) (apply-rounding mag (getf resolved :round-type) resolved)
    (values v minf maxf sig)))

(defun render-standard (resolved mag digits)
  (multiple-value-bind (v minf maxf sig) (rounded-magnitude resolved mag)
    (let* ((mnid (getf resolved :minimum-integer-digits))
           (decimal (render-decimal v mnid minf maxf sig resolved)))
      (digits->parts decimal digits resolved))))

(defun render-scientific (resolved mag digits notation)
  (if (zerop mag)
      (multiple-value-bind (v minf maxf sig) (rounded-magnitude resolved 0)
        (declare (ignore v))
        (append (digits->parts (render-decimal 0 1 minf maxf sig resolved) digits resolved)
                (list (cons "exponentSeparator" "E") (cons "exponentInteger" (subst-digits "0" digits)))))
      (let* ((e (log-int-floor mag))
             (exp (if (string= notation "engineering")
                      (* 3 (floor e 3))
                      e))
             (scaled (/ mag (expt-rat 10 exp))))
        (multiple-value-bind (v minf maxf sig) (rounded-magnitude resolved scaled)
          ;; rounding could push mantissa to >=10 (e.g. 9.99e0 -> 10e0); renormalize
          (when (and (>= v 10) (string/= notation "engineering"))
            (incf exp) (setf scaled (/ mag (expt-rat 10 exp)))
            (multiple-value-setq (v minf maxf sig) (rounded-magnitude resolved scaled)))
          (let* ((decimal (render-decimal v 1 minf maxf sig resolved))
                 (mant-parts (digits->parts decimal digits resolved))
                 (exp-sign (if (minusp exp) "-" ""))
                 (exp-str (subst-digits (format nil "~d" (abs exp)) digits)))
            (append mant-parts
                    (list (cons "exponentSeparator" "E"))
                    (when (minusp exp) (list (cons "exponentMinusSign" exp-sign)))
                    (list (cons "exponentInteger" exp-str))))))))

(defun compact-rounding-config (resolved)
  "Return a resolved-copy configured for CLDR compact default rounding
   (morePrecision of {fraction 0..0} and {significant 1..2}) UNLESS the user
   pinned digit options, in which case the user's config is used verbatim."
  (if (getf resolved :user-digits)
      resolved
      (let ((c (copy-list resolved)))
        (setf (getf c :round-type) :morePrecision
              (getf c :min-fraction) 0 (getf c :max-fraction) 0
              (getf c :min-significant) 1 (getf c :max-significant) 2)
        c)))

(defun render-compact (resolved mag digits)
  (let ((cres (compact-rounding-config resolved)))
    (if (< mag 1000)
        (render-standard cres mag digits)
        (let* ((e (log-int-floor mag))
               (pow (min 12 (* 3 (floor e 3))))
               (long (string= (getf resolved :compact-display) "long"))
               (suffix (cdr (assoc pow (if long +compact-long+ +compact-short+))))
               (scaled (/ mag (expt-rat 10 pow))))
          (multiple-value-bind (v minf maxf sig) (rounded-magnitude cres scaled)
            (declare (ignore minf maxf))
            ;; renormalize if rounding pushed to 1000
            (when (>= v 1000)
              (setf pow (min 12 (+ pow 3))
                    suffix (cdr (assoc pow (if long +compact-long+ +compact-short+)))
                    scaled (/ mag (expt-rat 10 pow)))
              (multiple-value-setq (v minf maxf sig) (rounded-magnitude cres scaled)))
            (let* ((decimal (render-decimal v 1 nil nil sig cres))
                   (num-parts (digits->parts decimal digits cres)))
              (if suffix
                  (if long
                      (append num-parts (list (cons "literal" " ") (cons "compact" suffix)))
                      (append num-parts (list (cons "compact" suffix))))
                  num-parts)))))))

(defun expt-rat (base e)
  (if (>= e 0) (expt base e) (/ 1 (expt base (- e)))))

(defun subst-digits (ascii digits)
  (if (string= digits "0123456789")
      ascii
      (map 'string (lambda (c)
                     (if (char<= #\0 c #\9)
                         (char digits (- (char-code c) (char-code #\0)))
                         c))
           ascii)))

(defun digits->parts (decimal digits resolved)
  "DECIMAL is an ASCII 'int.frac' string. Split into integer/group/decimal/
   fraction parts, applying grouping + numbering-system digit substitution."
  (let* ((dot (position #\. decimal))
         (int (if dot (subseq decimal 0 dot) decimal))
         (frac (if dot (subseq decimal (1+ dot)) nil))
         (grouping (getf resolved :use-grouping))
         (parts '()))
    ;; grouping
    (let ((grouped (group-integer int grouping)))
      (dolist (g grouped) (push g parts)))
    (setf parts (nreverse parts))
    ;; substitute digits in integer/group parts
    (setf parts (mapcar (lambda (p)
                          (cons (car p) (subst-digits (cdr p) digits)))
                        parts))
    (when frac
      (setf parts (append parts (list (cons "decimal" ".")
                                      (cons "fraction" (subst-digits frac digits))))))
    parts))

(defun group-integer (int grouping)
  "Return a list of (type . value) parts: 'integer' and 'group' for INT (ASCII).
   GROUPING is the resolved useGrouping value (\"always\" \"auto\" \"min2\" or NIL)."
  (let* ((n (length int))
         (do-group (and grouping (not (eq grouping :false))
                        (cond ((string= grouping "min2") (>= n 5)) ; min2: group only if >=1000 shown as 5+ digits? actually >999,999? we use >=5 int digits→ >=10000
                              (t (> n 3)))))
         (sep ","))
    (if (not do-group)
        (list (cons "integer" int))
        (let ((parts '()) (i n) (first t))
          ;; walk from the right in chunks of 3
          (loop
            (let ((start (max 0 (- i 3))))
              (let ((chunk (subseq int start i)))
                (if first
                    (progn (push (cons "integer" chunk) parts) (setf first nil))
                    (progn (push (cons "group" sep) parts)
                           (push (cons "integer" chunk) parts))))
              (setf i start)
              (when (<= i 0) (return))))
          parts))))

;;; ===========================================================================
;;; Affix assembly (sign, currency, unit, percent)
;;; ===========================================================================
(defun sign-part (kind)
  (ecase kind
    (:minus (cons "minusSign" "-"))
    (:plus (cons "plusSign" "+"))))

(defun assemble-with-affixes (resolved show-sign number-parts style)
  "Wrap NUMBER-PARTS with sign + style affixes. Returns the full part list."
  (let ((prefix '()) (suffix '())
        (accounting nil))
    (cond
      ((string= style "currency")
       (let* ((cur (getf resolved :currency))
              (disp (getf resolved :currency-display)))
         ;; accounting: negatives wrap in parentheses, no minus sign
         (when (and (string= (getf resolved :currency-sign) "accounting")
                    (eq show-sign :minus))
           (setf accounting t show-sign nil))
         (if (string= disp "name")
             ;; "1.00 US dollars": number + literal space + currency name (plural)
             (let ((name (currency-plural-name cur number-parts)))
               (setf suffix (list (cons "literal" " ") (cons "currency" name))))
             (let ((sym (currency-symbol cur disp)))
               (setf prefix (list (cons "currency" sym)))))))
      ((string= style "percent")
       (setf suffix (list (cons "percentSign" "%"))))
      ((string= style "unit")
       (multiple-value-bind (pre suf) (unit-affixes resolved number-parts)
         (setf prefix pre suffix suf))))
    ;; sign goes outermost-left (before currency symbol prefix)
    (let ((body (append
                 (when show-sign (list (sign-part show-sign)))
                 prefix number-parts suffix)))
      (if accounting
          (append (list (cons "literal" "(")) body (list (cons "literal" ")")))
          body))))

(defun currency-plural-name (cur number-parts)
  (let* ((one (currency-is-one number-parts))
         (entry (cdr (assoc cur +currency-name+ :test #'string=))))
    (if entry
        (if one (car entry) (cdr entry))
        (format nil "~a" cur))))

(defun currency-is-one (number-parts)
  "Heuristic plural: value equals '1' (integer 1, no fraction)."
  (let ((int (cdr (assoc "integer" number-parts :test #'string=)))
        (frac (assoc "fraction" number-parts :test #'string=)))
    (and int (string= int "1") (null frac))))

(defun unit-affixes (resolved number-parts)
  "Return (values prefix-parts suffix-parts) for the unit style."
  (let* ((unit (getf resolved :unit))
         (display (getf resolved :unit-display))
         (one (unit-is-one number-parts))
         (per (search "-per-" unit)))
    (if per
        (let* ((num (subseq unit 0 per))
               (den (subseq unit (+ per 5)))
               (num-name (unit-name num display one))
               (den-name (if (string= display "long")
                             (unit-name den display t)
                             (per-unit-short den))))  ; denominator singular
          (cond
            ((string= display "long")
             (values '() (list (cons "literal" " ")
                               (cons "unit" (format nil "~a per ~a" num-name den-name)))))
            ((string= display "narrow")
             (values '() (list (cons "unit" (format nil "~a/~a" num-name den-name)))))
            (t ;; short
             (values '() (list (cons "literal" " ")
                               (cons "unit" (format nil "~a/~a" num-name den-name)))))))
        (let* ((name (unit-name unit display one))
               ;; Units that attach with no separating space (CLDR).
               (no-space (or (string= display "narrow")
                             (member unit '("percent" "celsius" "fahrenheit")
                                     :test #'string=))))
          (if no-space
              (values '() (list (cons "unit" name)))
              (values '() (list (cons "literal" " ") (cons "unit" name))))))))

(defparameter +per-unit-short+
  ;; CLDR per-unit (denominator) short/narrow abbreviations that differ from the
  ;; standalone short form.
  '(("hour" . "h") ("second" . "s") ("minute" . "min") ("day" . "d")
    ("week" . "w") ("month" . "m") ("year" . "y")))

(defun per-unit-short (unit)
  (or (cdr (assoc unit +per-unit-short+ :test #'string=))
      (unit-name unit "short" t)))

(defun unit-is-one (number-parts)
  (let ((int (cdr (assoc "integer" number-parts :test #'string=)))
        (frac (assoc "fraction" number-parts :test #'string=)))
    (and int (string= int "1") (null frac))))

(defun unit-name (unit display one)
  (let ((row (cdr (assoc unit +unit-names+ :test #'string=))))
    (if (null row)
        unit
        (destructuring-bind (ss sp ns np ls lp) row
          (cond
            ((string= display "long") (if one ls lp))
            ((string= display "narrow") (if one ns np))
            (t (if one ss sp)))))))

;;; ===========================================================================
;;; Public formatting entry points
;;; ===========================================================================
(defun parts->string (parts)
  (with-output-to-string (s)
    (dolist (p parts) (write-string (cdr p) s))))

(defun nf-format-to-parts (nf x)
  (format-numeric-parts (getf nf :resolved) (mv-from-value x)))

(defun nf-format-to-string (nf x)
  (parts->string (nf-format-to-parts nf x)))

(defun format-numeric-string (resolved mv)
  (parts->string (format-numeric-parts resolved mv)))

;;; ===========================================================================
;;; InitializeNumberFormat
;;; ===========================================================================
(defun make-number-format (realm locales-arg options-arg)
  "Construct the internal resolved plist. Returns a plist for the :nf slot with
   :resolved (the resolved options plist)."
  (declare (ignore realm))
  (let* ((requested (canonicalize-locale-list locales-arg))
         ;; CoerceOptionsToObject: undefined -> a fresh NULL-prototype object (so
         ;; Object.prototype pollution can't leak defaults); else ToObject.
         (opts (if (js-undefined-p options-arg)
                   (make-object :proto *null* :class "Object")
                   (to-object options-arg)))
         (resolved '()))
    ;; localeMatcher
    (get-option opts "localeMatcher" :string '("lookup" "best fit") "best fit")
    ;; numberingSystem option
    (let ((nu-opt (get-option opts "numberingSystem" :string nil :undefined)))
      (when (and (stringp nu-opt) (not (valid-numbering-system-name-p nu-opt)))
        (js-throw (make-native-error "RangeError" "invalid numberingSystem")))
      ;; Resolve the locale WITHOUT relevant extension keys (the kernel's
      ;; resolve-locale mishandles keyword values on re-parse); derive nu from the
      ;; matched request's own -u-nu- extension instead.
      (let* ((rl (resolve-locale requested '() '()))
             (data-locale (getf rl :data-locale))
             (req-nu (request-nu-value requested data-locale))
             ;; A numbering system is "supported" iff we have its digit table.
             (ext-supported (and (stringp req-nu) (nu-supported-p req-nu)))
             (opt-supported (and (stringp nu-opt) (nu-supported-p nu-opt)))
             ;; [[NumberingSystem]]: option (if supported) beats extension (if
             ;; supported); else default latn.
             (nu (cond (opt-supported nu-opt)
                       (ext-supported req-nu)
                       (t "latn")))
             ;; Locale string carries the request's supported extension value only
             ;; (latn, the default, is dropped).
             (loc (if (and ext-supported (not (string= req-nu "latn")))
                      (locale-with-nu data-locale req-nu)
                      data-locale)))
        (setf (getf resolved :locale)
              (if (structurally-valid-locale-id-p loc)
                  (canonicalize-unicode-locale-id loc)
                  loc)
              (getf resolved :numbering-system) nu)))
    ;; SetNumberFormatUnitOptions
    (let* ((style (get-option opts "style" :string
                              '("decimal" "percent" "currency" "unit") "decimal"))
           (currency (get-option opts "currency" :string nil :undefined))
           (currency-display (get-option opts "currencyDisplay" :string
                                         '("code" "symbol" "narrowSymbol" "name") "symbol"))
           (currency-sign (get-option opts "currencySign" :string
                                      '("standard" "accounting") "standard"))
           (unit (get-option opts "unit" :string nil :undefined))
           (unit-display (get-option opts "unitDisplay" :string
                                     '("short" "narrow" "long") "short")))
      (when (stringp currency)
        (unless (well-formed-currency-p currency)
          (js-throw (make-native-error "RangeError" "invalid currency code"))))
      (when (and (string= style "currency") (eq currency :undefined))
        (js-throw (make-native-error "TypeError" "currency required for currency style")))
      (when (stringp unit)
        (unless (well-formed-unit-p unit)
          (js-throw (make-native-error "RangeError" "invalid unit identifier"))))
      (when (and (string= style "unit") (eq unit :undefined))
        (js-throw (make-native-error "TypeError" "unit required for unit style")))
      (setf (getf resolved :style) style)
      (when (string= style "currency")
        (setf (getf resolved :currency) (string-upcase currency)
              (getf resolved :currency-display) currency-display
              (getf resolved :currency-sign) currency-sign))
      (when (string= style "unit")
        (setf (getf resolved :unit) unit
              (getf resolved :unit-display) unit-display))
      ;; notation
      (let ((notation (get-option opts "notation" :string
                                  '("standard" "scientific" "engineering" "compact") "standard")))
        (setf (getf resolved :notation) notation)
        ;; digit-option defaults depend on style/notation
        (let (mnfd-default mxfd-default)
          (cond
            ((and (string= style "currency") (string= notation "standard"))
             (let ((cd (currency-digits (getf resolved :currency))))
               (setf mnfd-default cd mxfd-default cd)))
            ((string= style "percent")
             (setf mnfd-default 0 mxfd-default 0))
            ((string= notation "compact")
             (setf mnfd-default 0 mxfd-default 0))
            (t (setf mnfd-default 0 mxfd-default 3)))
          (setf resolved (set-nf-digit-options opts resolved mnfd-default mxfd-default notation)))
        ;; compactDisplay (read even if not compact per spec order)
        (let ((cd (get-option opts "compactDisplay" :string '("short" "long") "short")))
          (when (string= notation "compact")
            (setf (getf resolved :compact-display) cd)
            ;; compact default rounding: if the user didn't set digit options, use
            ;; significant 1..2 as CLDR compact does. Our render-compact handles it.
            ))
        ;; useGrouping (V3 GetStringOrBooleanOption); compact fallback is "min2".
        (setf (getf resolved :use-grouping)
              (get-string-or-boolean-option opts "useGrouping" '("min2" "auto" "always")
                                            "always" :false
                                            (if (string= notation "compact") "min2" "auto")))
        ;; signDisplay
        (let ((sd (get-option opts "signDisplay" :string
                              '("auto" "never" "always" "exceptZero" "negative") "auto")))
          (setf (getf resolved :sign-display) sd))))
    (list :resolved resolved)))

(defun request-nu-value (requested data-locale)
  "Find the -u-nu- value of the requested locale that best-matches DATA-LOCALE.
   Returns a string or NIL."
  (dolist (req requested)
    (let* ((lid (parse-unicode-locale-id req))
           (base (and lid (%lc (base-name-string lid)))))
      (when (and base (best-available-locale (intl-available-locales) base))
        (let* ((uentry (and lid (assoc #\u (locale-id-extensions lid))))
               (kw (and uentry (assoc "nu" (getf (cdr uentry) :keywords) :test #'string=))))
          (when kw
            (return-from request-nu-value
              (if (consp (cdr kw)) (format nil "~{~a~^-~}" (cdr kw)) (cdr kw))))))))
  nil)

(defun get-string-or-boolean-option (opts key string-values true-value falsy-value fallback)
  "GetStringOrBooleanOption (ECMA-402 V3): undefined->fallback; true->true-value;
   ToBoolean false -> falsy-value; ToString then \"true\"/\"false\"->fallback;
   in STRING-VALUES -> the string; else RangeError."
  (let ((v (js-get opts key)))
    (cond
      ((js-undefined-p v) fallback)
      ((eq v *true*) true-value)
      ((not (js-truthy v)) falsy-value)
      (t (let ((s (to-string v)))
           (cond
             ((or (string= s "true") (string= s "false")) fallback)
             ((member s string-values :test #'string=) s)
             (t (js-throw (make-native-error "RangeError" (format nil "invalid value for ~a" key))))))))))

(defun nu-supported-p (nu)
  "A numbering system is supported iff we carry its digit table."
  (and (stringp nu)
       (or (assoc nu +nf-all-digits+ :test #'string=)
           (assoc nu +numbering-system-digits+ :test #'string=))))

(defun valid-numbering-system-name-p (s)
  "A type value: alnum{3,8} ('-' alnum{3,8})* — for -u-nu- key."
  (and (stringp s) (plusp (length s))
       (every (lambda (p) (and (<= 3 (length p) 8) (%all #'%alnum-p p))) (split-dash s))))

(defun locale-with-nu (data-locale nu)
  (format nil "~a-u-nu-~a" data-locale nu))

;;; ===========================================================================
;;; resolvedOptions
;;; ===========================================================================
(defun nf-resolved-options-object (realm nf)
  (let* ((r (getf nf :resolved))
         (o (make-object :proto (realm-object-proto realm) :class "Object")))
    (put o "locale" (getf r :locale))
    (put o "numberingSystem" (getf r :numbering-system))
    (put o "style" (getf r :style))
    (when (getf r :currency)
      (put o "currency" (getf r :currency))
      (put o "currencyDisplay" (getf r :currency-display))
      (put o "currencySign" (getf r :currency-sign)))
    (when (getf r :unit)
      (put o "unit" (getf r :unit))
      (put o "unitDisplay" (getf r :unit-display)))
    (put o "minimumIntegerDigits" (float (getf r :minimum-integer-digits) 1d0))
    (when (getf r :min-fraction)
      (put o "minimumFractionDigits" (float (getf r :min-fraction) 1d0))
      (put o "maximumFractionDigits" (float (getf r :max-fraction) 1d0)))
    (when (getf r :min-significant)
      (put o "minimumSignificantDigits" (float (getf r :min-significant) 1d0))
      (put o "maximumSignificantDigits" (float (getf r :max-significant) 1d0)))
    (put o "useGrouping" (let ((g (getf r :use-grouping)))
                           (cond ((eq g :false) *false*)
                                 ((string= g "always") "always")
                                 (t g))))
    (put o "notation" (getf r :notation))
    (when (getf r :compact-display)
      (put o "compactDisplay" (getf r :compact-display)))
    (put o "signDisplay" (getf r :sign-display))
    (put o "roundingIncrement" (float (getf r :rounding-increment) 1d0))
    (put o "roundingMode" (getf r :rounding-mode))
    (put o "roundingPriority" (getf r :rounding-priority))
    (put o "trailingZeroDisplay" (getf r :trailing-zero-display))
    o))

;;; ===========================================================================
;;; install-intl_numberformat
;;; ===========================================================================
(defun install-intl_numberformat (realm)
  (let* ((op (realm-object-proto realm))
         (proto (make-object :proto op :class "Object"))
         (ctor (native-function realm "NumberFormat"
                 (lambda (this args)
                   ;; Called as a function (no new): ChainNumberFormat legacy quirk.
                   ;; If `this` is an object other than the prototype, install the
                   ;; new NumberFormat under the [[FallbackSymbol]] and return it.
                   (let ((nf (nf-construct realm proto args *undefined*)))
                     ;; ChainNumberFormat: only when `this` is (an instance whose
                     ;; prototype chain contains) NumberFormat.prototype.
                     (if (and (js-object-p this) (has-proto-in-chain this proto))
                         (progn
                           (put this *nf-legacy-symbol* nf
                                :enumerable nil :writable nil :configurable nil)
                           this)
                         nf)))
                 0)))
    (setf *intl-numberformat-proto* proto)
    (unless *nf-legacy-symbol*
      (setf *nf-legacy-symbol* (make-js-symbol "IntlLegacyConstructedSymbol")))
    (setf (js-object-construct ctor)
          (lambda (args nt) (nf-construct realm proto args nt)))
    (def-value ctor "prototype" proto :writable nil :configurable nil)
    (def-value proto "constructor" ctor)
    ;; supportedLocalesOf
    (def-method realm ctor "supportedLocalesOf" 1 (this args)
      (declare (ignore this))
      (let ((requested (canonicalize-locale-list (arg 0 args))))
        (get-option (coerce-options-to-object (arg 1 args)) "localeMatcher" :string
                    '("lookup" "best fit") "best fit")
        (make-array-object
         (remove-if-not (lambda (loc)
                          (let ((lid (parse-unicode-locale-id loc)))
                            (and lid (best-available-locale (intl-available-locales)
                                                            (%lc (base-name-string lid))))))
                        requested))))
    ;; @@toStringTag
    (put proto (symbol-tostringtag realm) "Intl.NumberFormat"
         :enumerable nil :writable nil :configurable t)
    ;; format getter (bound function)
    (put-accessor proto "format"
                  :get (native-function realm "get format"
                         (lambda (this args) (declare (ignore args))
                           (let ((nf (require-nf this)))
                             (or (getf (getf (js-object-internal this) :nf) :bound-format)
                                 (let ((bf (native-function realm ""
                                             (lambda (bthis bargs)
                                               (declare (ignore bthis))
                                               (nf-format-to-string nf (arg 0 bargs)))
                                             1)))
                                   (setf (getf (getf (js-object-internal this) :nf) :bound-format) bf)
                                   bf))))
                         0)
                  :enumerable nil :configurable t)
    ;; formatToParts
    (def-method realm proto "formatToParts" 1 (this args)
      (let ((nf (require-nf this)))
        (make-array-object
         (mapcar (lambda (p) (part->object realm p nil))
                 (nf-format-to-parts nf (arg 0 args))))))
    ;; formatRange
    (def-method realm proto "formatRange" 2 (this args)
      (let ((nf (require-nf this)))
        (nf-format-range-string realm nf (arg 0 args) (arg 1 args))))
    ;; formatRangeToParts
    (def-method realm proto "formatRangeToParts" 2 (this args)
      (let ((nf (require-nf this)))
        (make-array-object
         (mapcar (lambda (p) (part->object realm (cons (car p) (cadr p)) (caddr p)))
                 (nf-format-range-parts nf (arg 0 args) (arg 1 args))))))
    ;; resolvedOptions
    (def-method realm proto "resolvedOptions" 0 (this args)
      (declare (ignore args))
      (nf-resolved-options-object realm (require-nf this)))
    (intl-register realm "NumberFormat" ctor)
    ;; Number.prototype.toLocaleString via NumberFormat
    (install-number-tolocalestring realm)
    ctor))

(defun has-proto-in-chain (obj proto)
  "OrdinaryHasInstance: is PROTO on OBJ's prototype chain?"
  (loop for p = (js-get-proto obj) then (js-get-proto p)
        while (js-object-p p)
        when (eq p proto) do (return t)))

(defun nf-construct (realm proto args nt)
  (let* ((p (intl-proto-from-newtarget nt proto))
         (obj (make-object :proto p :class "Object"))
         (nf (make-number-format realm (arg 0 args) (arg 1 args))))
    (setf (getf (js-object-internal obj) :nf) nf)
    obj))

(defun part->object (realm part source)
  (let ((o (make-object :proto (realm-object-proto realm) :class "Object")))
    (put o "type" (car part))
    (put o "value" (cdr part))
    (when source (put o "source" source))
    o))

;;; ---- formatRange ----
(defun nf-format-range (nf xv yv)
  "Return a list of (type value source) triples for formatRange."
  (when (or (js-undefined-p xv) (js-undefined-p yv))
    (js-throw (make-native-error "TypeError" "formatRange requires two arguments")))
  (let ((x (mv-from-value xv)) (y (mv-from-value yv)))
    (when (or (eq x :nan) (eq y :nan))
      (js-throw (make-native-error "RangeError" "formatRange argument is NaN")))
    (let* ((resolved (getf nf :resolved))
           (px (format-numeric-parts resolved x))
           (py (format-numeric-parts resolved y)))
      (if (equal (mapcar (lambda (p) (cons (car p) (cdr p))) px)
                 (mapcar (lambda (p) (cons (car p) (cdr p))) py))
          ;; equal after rounding: approximatelySign + shared parts
          (cons (list "approximatelySign" "~" "shared")
                (mapcar (lambda (p) (list (car p) (cdr p) "shared")) px))
          (append
           (mapcar (lambda (p) (list (car p) (cdr p) "startRange")) px)
           (list (list "literal" (range-separator resolved) "shared"))
           (mapcar (lambda (p) (list (car p) (cdr p) "endRange")) py))))))

(defun range-separator (resolved)
  (declare (ignore resolved))
  " – ")

(defun nf-format-range-parts (nf xv yv)
  (nf-format-range nf xv yv))

(defun nf-format-range-string (realm nf xv yv)
  (declare (ignore realm))
  (parts->string (mapcar (lambda (tr) (cons (first tr) (second tr)))
                         (nf-format-range nf xv yv))))

;;; ---- Number.prototype.toLocaleString ----
(defun install-number-tolocalestring (realm)
  (let ((np (realm-number-proto realm)))
    (def-method realm np "toLocaleString" 0 (this args)
      (let ((x (this-number-value this)))
        (let ((nf (make-number-format realm (arg 0 args) (arg 1 args))))
          (nf-format-to-string nf x))))))

(defun this-number-value (this)
  (cond
    ((floatp this) this)
    ((js-bigint-p this) this)
    ((and (js-object-p this) (js-object-internal this)
          (let ((v (getf (js-object-internal this) :number-data)))
            (and v (floatp v))))
     (getf (js-object-internal this) :number-data))
    (t (to-number this))))

(register-builtin-installer 'install-intl_numberformat)
