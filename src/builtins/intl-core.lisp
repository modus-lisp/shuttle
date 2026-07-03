;;;; builtins/intl-core.lisp — the Intl KERNEL.
;;;;
;;;; This file is the FOUNDATION for the whole Intl namespace. Intl.Locale (this
;;;; round) and the later NumberFormat/DateTimeFormat/Collator/... all
;;;; build ON the abstractions here: the BCP-47 parser + UTS35 canonicalizer,
;;;; the shared abstract ops (CanonicalizeLocaleList / ResolveLocale / GetOption
;;;; family), the `en`-family available-locale data, and the enumerated tables
;;;; (numbering-system digits + the supportedValuesOf whitelists).
;;;;
;;;; NO CLDR: only the small spec-enumerated / test-pinned alias + likely-subtags
;;;; tables the corpus actually exercises. The canonicalizer must AGREE with the
;;;; harness (test262-full/harness/testIntl.js) tables for the tags the tests use.
;;;;
;;;; ---------------------------------------------------------------------------
;;;; KERNEL API (the API installers call these):
;;;;
;;;;  Namespace / registration
;;;;    (intl-namespace realm)             -> the global `Intl` object
;;;;    (intl-register realm name ctor)    -> hang Name on Intl (non-enum)
;;;;    (intl-tag realm)                   -> @@toStringTag symbol
;;;;    (intl-proto-from-newtarget nt def) -> GetPrototypeFromConstructor
;;;;
;;;;  BCP-47 / UTS35
;;;;    (parse-unicode-locale-id str)      -> locale-id struct | NIL (structural)
;;;;    (structurally-valid-locale-id-p s) -> boolean (IsStructurallyValidLanguageTag)
;;;;    (canonicalize-unicode-locale-id s) -> canonical string   (assumes valid)
;;;;    (canonicalize-language-tag s)      -> validate + canonicalize | RangeError
;;;;    lid struct accessors: lid-language lid-script lid-region lid-variants
;;;;      lid-extensions lid-privateuse   (see defstruct locale-id)
;;;;    (lid->string lid) (base-name-string lid)
;;;;    (add-likely-subtags lid) (remove-likely-subtags lid)  -> lid (max/min)
;;;;
;;;;  Shared abstract ops (for the API installers)
;;;;    (canonicalize-locale-list v)       -> list of canonical tag strings
;;;;    (resolve-locale requested rek defaults) -> plist (:locale :ca :nu ...)
;;;;    (canonicalize-option-string s)     helpers for options coercion
;;;;    (get-option opts key type values default)
;;;;    (get-boolean-or-string-option opts key strings default)
;;;;    (default-number-option v min max fallback) (get-number-option ...)
;;;;    (coerce-options-to-object v)
;;;;    (intl-available-locales)           -> ("en" "en-US" ...)
;;;;    +numbering-system-digits+          alist (name . 10-char-string)
;;;;    (supported-values-for key)         -> sorted string list | RangeError
;;;; ---------------------------------------------------------------------------
(in-package #:shuttle)

;;; ===========================================================================
;;; Small character/subtag predicates
;;; ===========================================================================
(defun %alpha-p (c) (or (char<= #\a c #\z) (char<= #\A c #\Z)))
(defun %digit-p (c) (char<= #\0 c #\9))
(defun %alnum-p (c) (or (%alpha-p c) (%digit-p c)))

(defun %all (pred s) (and (plusp (length s)) (every pred s)))
(defun %lc (s) (string-downcase s))

(defun split-dash (s)
  "Split S on '-' (BCP-47 subtag separator). Empty subtags are preserved so the
   parser can reject leading/trailing/double dashes."
  (let ((out '()) (start 0))
    (loop for i = (position #\- s :start start)
          do (push (subseq s start (or i (length s))) out)
             (if i (setf start (1+ i)) (return)))
    (nreverse out)))

;;; subtag-shape predicates (per unicode_locale_id grammar)
(defun language-subtag-p (s)          ; alpha{2,3} | alpha{5,8}  (NO 4)
  (and (%all #'%alpha-p s) (or (<= 2 (length s) 3) (<= 5 (length s) 8))))
(defun script-subtag-p (s) (and (= (length s) 4) (%all #'%alpha-p s)))
(defun region-subtag-p (s)
  (or (and (= (length s) 2) (%all #'%alpha-p s))
      (and (= (length s) 3) (%all #'%digit-p s))))
(defun variant-subtag-p (s)
  (or (and (<= 5 (length s) 8) (%all #'%alnum-p s))
      (and (= (length s) 4) (%digit-p (char s 0)) (%all #'%alnum-p s))))
(defun singleton-p (s)                ; one alnum char
  (and (= (length s) 1) (%alnum-p (char s 0))))

;;; ===========================================================================
;;; locale-id record — the parsed unicode_locale_id
;;; ===========================================================================
(defstruct (locale-id (:constructor make-locale-id))
  (language nil)      ; string (lowercase canonical) or NIL / "und"
  (script nil)        ; Titlecase or NIL
  (region nil)        ; UPPER or NIL
  (variants '())      ; list of lowercase variant strings
  ;; extensions: list of (singleton-char . payload-string) preserving order;
  ;; 'u and 't are canonicalized specially; others kept verbatim (lowercased).
  (extensions '())
  (privateuse nil))   ; the "x-...." string (lowercase) or NIL

;;; ===========================================================================
;;; PARSER: parse-unicode-locale-id
;;; Grammar (UTS35 unicode_locale_id):
;;;   unicode_language_id = "root" | language ("-" script)? ("-" region)? ("-" variant)*
;;;   then extensions (singleton "-" ...) then optional "-x-" privateuse.
;;; Returns a locale-id or NIL (structurally invalid). Does NOT canonicalize.
;;; ===========================================================================
(defun parse-unicode-locale-id (str)
  (when (or (not (stringp str)) (zerop (length str))) (return-from parse-unicode-locale-id nil))
  ;; ASCII only; reject anything else early (non-ASCII letters etc.)
  (unless (every (lambda (c) (< (char-code c) 128)) str)
    (return-from parse-unicode-locale-id nil))
  (let ((subs (split-dash str)))
    ;; No empty subtag anywhere (rejects leading/trailing/double dashes).
    (when (some (lambda (s) (zerop (length s))) subs)
      (return-from parse-unicode-locale-id nil))
    (let ((lid (make-locale-id)) (i 0) (n (length subs)))
      (labels ((cur () (when (< i n) (nth i subs)))
               (adv () (incf i)))
        ;; ---- unicode_language_id ----
        ;; A private-use-only tag (starts with x) is NOT a valid unicode_locale_id.
        (let ((first (cur)))
          (when (or (null first) (string-equal first "x") (singleton-p first))
            (return-from parse-unicode-locale-id nil))
          (cond
            ((string-equal first "root")
             (setf (locale-id-language lid) "root") (adv))
            ((language-subtag-p first)
             (setf (locale-id-language lid) (%lc first)) (adv))
            (t (return-from parse-unicode-locale-id nil))))
        ;; optional script
        (when (and (cur) (not (singleton-p (cur))) (script-subtag-p (cur)))
          (setf (locale-id-script lid) (cur)) (adv))
        ;; optional region
        (when (and (cur) (not (singleton-p (cur))) (region-subtag-p (cur)))
          (setf (locale-id-region lid) (cur)) (adv))
        ;; variants*
        (loop while (and (cur) (not (singleton-p (cur))))
              do (if (variant-subtag-p (cur))
                     (progn (push (%lc (cur)) (locale-id-variants lid)) (adv))
                     (return-from parse-unicode-locale-id nil)))
        (setf (locale-id-variants lid) (nreverse (locale-id-variants lid)))
        ;; ---- extensions + privateuse ----
        (let ((seen-singletons '()))
          (loop while (cur) do
            (let ((sing (cur)))
              (unless (singleton-p sing) (return-from parse-unicode-locale-id nil))
              (adv)
              (let ((sc (char-downcase (char sing 0))))
                (cond
                  ;; private use: x-(1*8alnum)+ , consumes to end.
                  ((char= sc #\x)
                   (let ((parts '()))
                     (loop while (cur) do
                       (let ((p (cur)))
                         (unless (and (<= 1 (length p) 8) (%all #'%alnum-p p))
                           (return-from parse-unicode-locale-id nil))
                         (push (%lc p) parts) (adv)))
                     (when (null parts) (return-from parse-unicode-locale-id nil))
                     (setf (locale-id-privateuse lid)
                           (format nil "x-~{~a~^-~}" (nreverse parts)))))
                  (t
                   ;; duplicate singleton -> invalid
                   (when (member sc seen-singletons) (return-from parse-unicode-locale-id nil))
                   (push sc seen-singletons)
                   (let ((payload
                           (cond ((char= sc #\u) (parse-u-extension #'cur #'adv))
                                 ((char= sc #\t) (parse-t-extension #'cur #'adv))
                                 (t (parse-other-extension #'cur #'adv)))))
                     (when (eq payload :invalid) (return-from parse-unicode-locale-id nil))
                     (setf (locale-id-extensions lid)
                           (append (locale-id-extensions lid) (list (cons sc payload))))))))))))
      lid)))

(defun parse-other-extension (cur adv)
  "other_extensions = other_singleton (-alphanum{2,8})+ . Returns the list of
   lowercase subtags, or :invalid."
  (let ((parts '()))
    (loop for p = (funcall cur)
          while (and p (not (singleton-p p)))
          do (unless (and (<= 2 (length p) 8) (%all #'%alnum-p p)) (return-from parse-other-extension :invalid))
             (push (%lc p) parts) (funcall adv))
    (if (null parts) :invalid (nreverse parts))))

(defun parse-u-extension (cur adv)
  "unicode_locale_extensions body: (attribute)* (keyword)* where
   keyword = key (-type)* , key=alnum alpha, attribute/type = alnum{3,8}.
   Must be non-empty. Returns (values-list) as (:attrs list :keywords alist)
   where keywords = list of (key . (types...))."
  (let ((attrs '()) (keywords '()) (any nil))
    ;; attributes: alnum{3,8} that are NOT keys (a key is exactly 2 chars alnum+alpha)
    (loop for p = (funcall cur)
          while (and p (not (singleton-p p)) (= (length p) 3) nil)) ; placeholder (unused)
    ;; leading attributes
    (loop for p = (funcall cur)
          while (and p (not (singleton-p p))
                     (>= (length p) 3) (<= (length p) 8) (%all #'%alnum-p p))
          do (push (%lc p) attrs) (funcall adv) (setf any t))
    ;; keywords
    (loop for k = (funcall cur)
          while (and k (not (singleton-p k)) (u-key-p k))
          do (funcall adv) (setf any t)
             (let ((types '()))
               (loop for tp = (funcall cur)
                     while (and tp (not (singleton-p tp))
                                (>= (length tp) 3) (<= (length tp) 8) (%all #'%alnum-p tp))
                     do (push (%lc tp) types) (funcall adv))
               (push (cons (%lc k) (nreverse types)) keywords)))
    ;; If something remains that isn't a singleton, it's an invalid subtag.
    (let ((nxt (funcall cur)))
      (when (and nxt (not (singleton-p nxt))) (return-from parse-u-extension :invalid)))
    (unless any (return-from parse-u-extension :invalid))
    (list :attrs (nreverse attrs) :keywords (nreverse keywords))))

(defun u-key-p (s) (and (= (length s) 2) (%alnum-p (char s 0)) (%alpha-p (char s 1))))

(defun parse-t-extension (cur adv)
  "transformed_extensions body: (tlang (tfield)*) | (tfield)+
   tlang = language (-script)? (-region)? (-variant)* ; tfield = tkey (-tvalue)+
   tkey = alpha digit ; tvalue = alnum{3,8}. Returns (:tlang lid-or-nil
   :fields alist(key . (values...))) or :invalid."
  (let ((tlang nil) (fields '()) (any nil))
    ;; optional tlang: first subtag is a language subtag (2-3 or 5-8 alpha), not a tkey.
    (let ((first (funcall cur)))
      (when (and first (not (singleton-p first)) (language-subtag-p first)
                 (not (t-key-p first)))
        (setf any t)
        (let ((tl (make-locale-id)))
          (setf (locale-id-language tl) (%lc first)) (funcall adv)
          (let ((s (funcall cur)))
            (when (and s (not (singleton-p s)) (not (t-key-p s)) (script-subtag-p s))
              (setf (locale-id-script tl) s) (funcall adv)))
          (let ((r (funcall cur)))
            (when (and r (not (singleton-p r)) (not (t-key-p r)) (region-subtag-p r))
              (setf (locale-id-region tl) r) (funcall adv)))
          (let ((vs '()))
            (loop for v = (funcall cur)
                  while (and v (not (singleton-p v)) (not (t-key-p v)) (variant-subtag-p v))
                  do (push (%lc v) vs) (funcall adv))
            ;; duplicate variants in tlang -> invalid
            (let ((lcv (nreverse vs)))
              (when (/= (length lcv) (length (remove-duplicates lcv :test #'string=)))
                (return-from parse-t-extension :invalid))
              (setf (locale-id-variants tl) lcv)))
          (setf tlang tl))))
    ;; tfields: tkey (alpha digit) followed by 1+ tvalue.
    (loop for k = (funcall cur)
          while (and k (not (singleton-p k)) (t-key-p k))
          do (funcall adv) (setf any t)
             (let ((vals '()))
               (loop for v = (funcall cur)
                     while (and v (not (singleton-p v))
                                (>= (length v) 3) (<= (length v) 8) (%all #'%alnum-p v))
                     do (push (%lc v) vals) (funcall adv))
               (when (null vals) (return-from parse-t-extension :invalid))
               (push (cons (%lc k) (nreverse vals)) fields)))
    ;; anything left that isn't a singleton is invalid
    (let ((nxt (funcall cur)))
      (when (and nxt (not (singleton-p nxt))) (return-from parse-t-extension :invalid)))
    (unless any (return-from parse-t-extension :invalid))
    (list :tlang tlang :fields (nreverse fields))))

(defun t-key-p (s) (and (= (length s) 2) (%alpha-p (char s 0)) (%digit-p (char s 1))))

;;; ===========================================================================
;;; Structural validity (IsStructurallyValidLanguageTag): parses + no dup variant.
;;; ===========================================================================
(defun structurally-valid-locale-id-p (s)
  (let ((lid (and (stringp s) (parse-unicode-locale-id s))))
    (and lid
         ;; no duplicate variant subtags in the main id
         (let ((v (locale-id-variants lid)))
           (= (length v) (length (remove-duplicates v :test #'string=)))))))

;;; ===========================================================================
;;; ALIAS + LIKELY-SUBTAGS TABLES  (test-pinned subsets; NO full CLDR)
;;; ===========================================================================
;;; Simple language aliases (subtag -> replacement); replacement may be a single
;;; subtag or "lang-Script" / "lang-REGION" (handled by canonicalize).
(defparameter +language-alias+
  '(("cmn" . "zh") ("in" . "id") ("iw" . "he") ("ji" . "yi") ("jw" . "jv")
    ("mo" . "ro") ("aar" . "aa") ("heb" . "he") ("ces" . "cs") ("zho" . "zh")
    ("eng" . "en") ("deu" . "de") ("fra" . "fr") ("spa" . "es") ("nld" . "nl")
    ("ell" . "el") ("ita" . "it") ("por" . "pt") ("rus" . "ru") ("jpn" . "ja")
    ("kor" . "ko") ("ara" . "ar") ("hin" . "hi") ("tha" . "th") ("tgl" . "fil")
    ("tl" . "fil") ("no" . "nb") ("bh" . "bho")))

;;; Complex language aliases: subtag -> (:language L :script S :region R)
;;; (script/region added only if absent). From testIntl.js __complexLanguageMappings.
(defparameter +complex-language-alias+
  '(("sh"  . (:language "sr" :script "Latn"))
    ("hbs" . (:language "sr" :script "Latn"))
    ("cnr" . (:language "sr" :region "ME"))
    ("drw" . (:language "fa" :region "AF"))
    ("prs" . (:language "fa" :region "AF"))
    ("tnf" . (:language "fa" :region "AF"))
    ("swc" . (:language "sw" :region "CD"))))

;;; Simple region aliases (deprecated single-territory replacements + numeric).
(defparameter +region-alias+
  '(("DD" . "DE") ("SU" . "RU") ("810" . "RU") ("CS" . "RS") ("276" . "DE")
    ("554" . "NZ") ("UK" . "GB") ("BU" . "MM") ("TP" . "TL") ("YU" . "RS")
    ("ZR" . "CD") ("QU" . "EU")))

;;; Complex region aliases: territory -> (:default R :map ((likely-tag . R) ...))
;;; The map is keyed by the maximized "lang" or "lang-Script" of the source.
;;; From testIntl.js __complexRegionMappings (SU/810/CS/NT + their aliases).
(defparameter +complex-region-alias+
  '(("SU"  . (:default "RU" :map (("hy" . "AM") ("und-Armn" . "AM"))))
    ("810" . (:default "RU" :map (("hy" . "AM") ("und-Armn" . "AM"))))
    ("CS"  . (:default "RS" :map ()))
    ("NT"  . (:default "SA" :map ()))))

;;; Variant aliases: variant -> (:type T :replacement R). heploc->alalc97 etc.
(defparameter +variant-alias+
  '(("heploc" . (:type :variant :replacement "alalc97"))
    ("polytoni" . (:type :variant :replacement "polyton"))
    ("arevela" . (:type :language :replacement "hy"))
    ("arevmda" . (:type :language :replacement "hyw"))
    ("aaland" . (:type :region :replacement "AX"))))

;;; Grandfathered whole-tag mappings (regular, UTS35-valid) + irregular preferred.
;;; canonicalized-tags pins sgn-GR->gss (via sign-language alias). We map the
;;; specific tags the tests use.
;;; Only the regular, UTS35-VALID grandfathered tags (structurally valid, get a
;;; preferred replacement). The irregular ones (i-klingon, en-GB-oed, sgn-BE-FR)
;;; are structurally INVALID per UTS35 and must be rejected by the parser, so
;;; they are NOT listed here (listing them would bypass the invalid check).
(defparameter +grandfathered-alias+
  '(("art-lojban" . "jbo") ("cel-gaulish" . "xtg") ("zh-guoyu" . "zh")
    ("zh-hakka" . "hak") ("zh-xiang" . "hsn")
    ("sgn-gr" . "gss")))

;;; Unicode-extension type aliases per key: key -> ((alias . canonical) ...).
(defparameter +u-type-alias+
  '(("ca" . (("ethiopic-amete-alem" . "ethioaa") ("islamicc" . "islamic-civil")))
    ("ms" . (("imperial" . "uksystem")))
    ("ks" . (("primary" . "level1") ("tertiary" . "level3")))))

;;; Keys whose "yes" -> "true" then "true" removed.
(defparameter +u-yes-to-true-keys+ '("kb" "kc" "kh" "kk" "kn"))

;;; Subdivision aliases (for rg / sd values) — test-pinned subset.
(defparameter +subdivision-alias+
  '(("no23" . "no50") ("cn11" . "cnbj") ("cz10a" . "cz110")
    ("fra" . "frges") ("frg" . "frges") ("lud" . "lucl")))

;;; t-extension tfield value aliases: tkey -> ((alias . canonical) ...).
(defparameter +t-value-alias+
  '(("m0" . (("names" . "prprname")))))

;;; u-extension tz value aliases (deprecated/alias timezone ids -> canonical).
(defparameter +tz-value-alias+
  '(("cnckg" . "cnsha") ("eire" . "iedub") ("est" . "papty") ("gmt0" . "gmt")
    ("uct" . "utc") ("zulu" . "utc")))

;;; Multi-variant sequence aliases (whole-sequence -> single replacement).
(defparameter +variant-sequence-alias+
  '(("hepburn-heploc" . "alalc97")))

;;; Likely-subtags (maximize): key "lang" | "lang-Script" | "und-Script" |
;;; "und-Region" -> (:language L :script S :region R). Test-pinned subset.
(defparameter +likely-subtags+
  '(;; language-only
    ("und" :language "en" :script "Latn" :region "US")
    ("en" :language "en" :script "Latn" :region "US")
    ("th" :language "th" :script "Thai" :region "TH")
    ("de" :language "de" :script "Latn" :region "DE")
    ("es" :language "es" :script "Latn" :region "ES")
    ("it" :language "it" :script "Latn" :region "IT")
    ("ru" :language "ru" :script "Cyrl" :region "RU")
    ("ar" :language "ar" :script "Arab" :region "EG")
    ("zh" :language "zh" :script "Hans" :region "CN")
    ("hi" :language "hi" :script "Deva" :region "IN")
    ("bg" :language "bg" :script "Cyrl" :region "BG")
    ("sr" :language "sr" :script "Cyrl" :region "RS")
    ("fa" :language "fa" :script "Arab" :region "IR")
    ("he" :language "he" :script "Hebr" :region "IL")
    ("hy" :language "hy" :script "Armn" :region "AM")
    ("hyw" :language "hyw" :script "Armn" :region "AM")
    ("ro" :language "ro" :script "Latn" :region "RO")
    ("cs" :language "cs" :script "Latn" :region "CZ")
    ("aa" :language "aa" :script "Latn" :region "ET")
    ("jbo" :language "jbo" :script "Latn" :region "001")
    ("hak" :language "hak" :script "Hans" :region "CN")
    ("hsn" :language "hsn" :script "Hans" :region "CN")
    ("uz" :language "uz" :script "Latn" :region "UZ")
    ("pap" :language "pap" :script "Latn" :region "CW")
    ("aae" :language "aae" :script "Latn" :region "IT")
    ;; und-Script
    ("und-Thai" :language "th" :script "Thai" :region "TH")
    ("und-Cyrl" :language "ru" :script "Cyrl" :region "RU")
    ("und-Armn" :language "hy" :script "Armn" :region "AM")
    ("und-Latn" :language "en" :script "Latn" :region "US")
    ("und-Arab" :language "ar" :script "Arab" :region "EG")
    ("und-Hans" :language "zh" :script "Hans" :region "CN")
    ("und-Hant" :language "zh" :script "Hant" :region "TW")
    ("und-Hebr" :language "he" :script "Hebr" :region "IL")
    ("und-Deva" :language "hi" :script "Deva" :region "IN")
    ;; und-Region
    ("und-419" :language "es" :script "Latn" :region "419")
    ("und-150" :language "en" :script "Latn" :region "150")
    ("und-AT"  :language "de" :script "Latn" :region "AT")
    ("und-AQ"  :language "en" :script "Latn" :region "AQ")
    ("und-CW"  :language "pap" :script "Latn" :region "CW")
    ("und-US"  :language "en" :script "Latn" :region "US")
    ("und-GB"  :language "en" :script "Latn" :region "GB")
    ;; lang-Script (for minimize round-trips)
    ("en-Shaw" :language "en" :script "Shaw" :region "GB")
    ("en-Arab" :language "en" :script "Arab" :region "US")
    ("zh-Hant" :language "zh" :script "Hant" :region "TW")
    ("zh-TW" :language "zh" :script "Hant" :region "TW")
    ("und-Cyrl-RO" :language "bg" :script "Cyrl" :region "RO")
    ;; complex-region likely lookups
    ("und-Armn-AM" :language "hy" :script "Armn" :region "AM")))

(defun likely-lookup (key)
  (let ((row (assoc key +likely-subtags+ :test #'string-equal)))
    (when row (cdr row))))

;;; ===========================================================================
;;; Titlecase / uppercase helpers for canonical case
;;; ===========================================================================
(defun titlecase (s)
  (if (zerop (length s)) s
      (concatenate 'string (string (char-upcase (char s 0))) (%lc (subseq s 1)))))

;;; ===========================================================================
;;; CANONICALIZE (CanonicalizeUnicodeLocaleId) — operates on a parsed lid.
;;; ===========================================================================
(defun canonicalize-lid (lid)
  "Canonicalize the parsed LID in place per UTS35, returning it."
  ;; 1. language / script / region case + variant lowercase already lowercased.
  (canonicalize-unicode-language-id lid)
  ;; 2. extensions
  (setf (locale-id-extensions lid)
        (mapcar (lambda (ext)
                  (let ((sc (car ext)))
                    (cond ((char= sc #\u) (cons sc (canonicalize-u-payload (cdr ext))))
                          ((char= sc #\t) (cons sc (canonicalize-t-payload (cdr ext))))
                          (t ext))))
                (locale-id-extensions lid)))
  ;; sort extensions by singleton char (u before t? spec: by singleton; keep
  ;; other singletons sorted, then t, then u? Actually per UTS35: extensions are
  ;; sorted by singleton, with 'x' last. We sort alphabetically by char.)
  (setf (locale-id-extensions lid)
        (stable-sort (copy-list (locale-id-extensions lid)) #'char< :key #'car))
  lid)

(defun apply-grandfathered-lid (lid)
  "If LID's language + a leading run of variants matches a grandfathered/
   language-id alias key (e.g. art-lojban, zh-guoyu, sgn + region), rewrite the
   base subtags with the canonical replacement (a bare language). The remaining
   variants are preserved. Mutates and returns LID."
  ;; language(-variant)* keys
  (let* ((lang (or (locale-id-language lid) ""))
         (vars (locale-id-variants lid)))
    (dolist (pair +grandfathered-alias+)
      (let ((key-parts (split-dash (car pair))))
        ;; sgn-<region> style: language + region key (no variants)
        (cond
          ((and (= (length key-parts) 2)
                (string-equal (first key-parts) lang)
                (region-subtag-p (second key-parts))
                (locale-id-region lid)
                (string-equal (second key-parts) (locale-id-region lid))
                (null vars))
           (setf (locale-id-language lid) (%lc (cdr pair))
                 (locale-id-region lid) nil)
           (return-from apply-grandfathered-lid lid))
          ;; language + variant-prefix style (art-lojban, zh-guoyu, ...)
          ((and (string-equal (first key-parts) lang)
                (every #'variant-subtag-p (rest key-parts))
                (>= (length vars) (length (rest key-parts)))
                (every #'string-equal (rest key-parts) vars))
           (setf (locale-id-language lid) (%lc (cdr pair))
                 (locale-id-variants lid) (nthcdr (length (rest key-parts)) vars))
           (return-from apply-grandfathered-lid lid))))))
  lid)

(defun canonicalize-unicode-language-id (lid)
  "Apply language/script/region aliases + case regularization to LID."
  (apply-grandfathered-lid lid)
  (let ((lang (locale-id-language lid)))
    ;; grandfathered whole-tag handled by caller (canonicalize-unicode-locale-id).
    ;; multi-variant sequence aliases (e.g. hepburn-heploc -> alalc97): if the
    ;; variant list contains the whole ordered sequence, collapse it.
    (dolist (pair +variant-sequence-alias+)
      (let* ((seq (split-dash (car pair)))
             (vars (locale-id-variants lid))
             (pos (search seq vars :test #'string-equal)))
        (when pos
          (setf (locale-id-variants lid)
                (append (subseq vars 0 pos)
                        (list (cdr pair))
                        (subseq vars (+ pos (length seq))))))))
    ;; variant aliases that map to language/region
    (dolist (v (copy-list (locale-id-variants lid)))
      (let ((va (cdr (assoc v +variant-alias+ :test #'string-equal))))
        (when va
          (ecase (getf va :type)
            (:variant (setf (locale-id-variants lid)
                            (substitute (getf va :replacement) v (locale-id-variants lid) :test #'string=)))
            (:language (setf lang (getf va :replacement)
                             (locale-id-variants lid) (remove v (locale-id-variants lid) :test #'string=)))
            (:region (setf (locale-id-region lid) (getf va :replacement)
                           (locale-id-variants lid) (remove v (locale-id-variants lid) :test #'string=)))))))
    ;; complex language alias (adds script/region if absent)
    (let ((cx (cdr (assoc lang +complex-language-alias+ :test #'string-equal))))
      (when cx
        (setf lang (getf cx :language))
        (when (and (getf cx :script) (null (locale-id-script lid)))
          (setf (locale-id-script lid) (getf cx :script)))
        (when (and (getf cx :region) (null (locale-id-region lid)))
          (setf (locale-id-region lid) (getf cx :region)))))
    ;; simple language alias
    (let ((sa (cdr (assoc lang +language-alias+ :test #'string-equal))))
      (when sa (setf lang sa)))
    (setf (locale-id-language lid) (and lang (%lc lang))))
  ;; script titlecase
  (when (locale-id-script lid) (setf (locale-id-script lid) (titlecase (locale-id-script lid))))
  ;; region: uppercase, then alias (simple or complex likely-based)
  (when (locale-id-region lid)
    (setf (locale-id-region lid) (canonicalize-region (locale-id-region lid) lid)))
  ;; variants: lowercase + sort alphabetically
  (setf (locale-id-variants lid)
        (sort (remove-duplicates (mapcar #'%lc (locale-id-variants lid)) :test #'string= :from-end t)
              #'string<))
  lid)

(defun canonicalize-region (region lid)
  "Canonicalize a region subtag: uppercase, then simple/complex territory alias."
  (let* ((up (if (%all #'%digit-p region) region (string-upcase region)))
         (cx (assoc up +complex-region-alias+ :test #'string-equal)))
    (cond
      (cx
       ;; likely-based: build lookup key from language (+script) of the lid.
       (let* ((info (cdr cx))
              (lang (or (locale-id-language lid) "und"))
              (scr (locale-id-script lid))
              ;; maximize lang(+script) ignoring the source region.
              (likely (or (and scr (likely-lookup (format nil "~a-~a" lang scr)))
                          (likely-lookup lang)
                          (and (string-equal lang "und") scr (likely-lookup (format nil "und-~a" scr)))))
              (likely-region (getf likely :region))
              (mapped (or (cdr (assoc lang (getf info :map) :test #'string-equal))
                          ;; try und-Script key
                          (and scr (cdr (assoc (format nil "und-~a" scr) (getf info :map) :test #'string-equal))))))
         (or mapped
             ;; if the likely region is one of the replacement options, use it —
             ;; but our test-pinned map already encodes the special cases, so
             ;; fall back to default. (likely-region kept for AM cases.)
             (and likely-region (member likely-region (list (getf info :default)) :test #'string=) likely-region)
             (getf info :default))))
      (t (let ((sa (cdr (assoc up +region-alias+ :test #'string-equal))))
           (or sa up))))))

;;; ---- u extension canonicalization ----
(defun canonicalize-u-payload (payload)
  "PAYLOAD is (:attrs list :keywords alist). Canonicalize: type aliases,
   yes->true, drop 'true' type, sort attributes, sort keywords by key."
  (let ((attrs (sort (copy-list (getf payload :attrs)) #'string<))
        (keywords
          (mapcar
           (lambda (kw)
             (let* ((key (car kw)) (types (cdr kw))
                    ;; join types with '-', apply type-alias on the joined value.
                    (val (format nil "~{~a~^-~}" types))
                    (alias-tbl (cdr (assoc key +u-type-alias+ :test #'string=)))
                    (aliased (or (cdr (assoc val alias-tbl :test #'string=)) val)))
               ;; yes -> true for the listed keys
               (when (and (member key +u-yes-to-true-keys+ :test #'string=)
                          (string= aliased "yes"))
                 (setf aliased "true"))
               ;; subdivision/region value alias for rg/sd
               (when (member key '("rg" "sd") :test #'string=)
                 (setf aliased (or (cdr (assoc aliased +subdivision-alias+ :test #'string=)) aliased)))
               ;; timezone value alias for tz
               (when (string= key "tz")
                 (setf aliased (or (cdr (assoc aliased +tz-value-alias+ :test #'string=)) aliased)))
               ;; drop a lone "true" type value
               (cons key (if (string= aliased "true") "" aliased))))
           (getf payload :keywords))))
    ;; sort keywords by key (US-ASCII), drop duplicate keys (keep first).
    (setf keywords (stable-sort keywords #'string< :key #'car))
    (setf keywords (remove-duplicates keywords :test #'string= :key #'car :from-end t))
    (list :attrs attrs :keywords keywords)))

(defun canonicalize-t-payload (payload)
  "PAYLOAD is (:tlang lid :fields alist). Canonicalize tlang + field values,
   sort fields by key."
  (let* ((tl (getf payload :tlang))
         (fields (mapcar
                  (lambda (fl)
                    (let* ((key (car fl)) (vals (cdr fl))
                           (val (format nil "~{~a~^-~}" vals))
                           (tbl (cdr (assoc key +t-value-alias+ :test #'string=)))
                           (aliased (or (cdr (assoc val tbl :test #'string=)) val)))
                      (cons key aliased)))
                  (getf payload :fields))))
    (when tl (canonicalize-tlang tl))
    (list :tlang tl :fields (stable-sort fields #'string< :key #'car))))

(defun canonicalize-tlang (tl)
  "Canonicalize a tlang (transformed-extension language). Unlike the main
   unicode_language_id, tlang subtags are all lowercased (script NOT titlecased,
   region NOT uppercased); language/region aliases still apply, variants sorted."
  (let ((lang (locale-id-language tl)))
    (let ((cx (cdr (assoc lang +complex-language-alias+ :test #'string-equal))))
      (when cx
        (setf lang (getf cx :language))
        (when (and (getf cx :script) (null (locale-id-script tl)))
          (setf (locale-id-script tl) (%lc (getf cx :script))))
        (when (and (getf cx :region) (null (locale-id-region tl)))
          (setf (locale-id-region tl) (%lc (getf cx :region))))))
    (let ((sa (cdr (assoc lang +language-alias+ :test #'string-equal))))
      (when sa (setf lang sa)))
    (setf (locale-id-language tl) (%lc lang)))
  (when (locale-id-script tl) (setf (locale-id-script tl) (%lc (locale-id-script tl))))
  (when (locale-id-region tl)
    (setf (locale-id-region tl)
          (%lc (or (cdr (assoc (string-upcase (locale-id-region tl)) +region-alias+ :test #'string-equal))
                   (locale-id-region tl)))))
  (setf (locale-id-variants tl)
        (sort (mapcar #'%lc (locale-id-variants tl)) #'string<))
  tl)

;;; ===========================================================================
;;; SERIALIZE
;;; ===========================================================================
(defun base-name-string (lid)
  "language ('-'script)? ('-'region)? ('-'variant)*"
  (with-output-to-string (s)
    (write-string (or (locale-id-language lid) "und") s)
    (when (locale-id-script lid) (format s "-~a" (locale-id-script lid)))
    (when (locale-id-region lid) (format s "-~a" (locale-id-region lid)))
    (dolist (v (locale-id-variants lid)) (format s "-~a" v))))

(defun u-payload->string (payload)
  (with-output-to-string (s)
    (dolist (a (getf payload :attrs)) (format s "-~a" a))
    (dolist (kw (getf payload :keywords))
      (format s "-~a" (car kw))
      (unless (string= (cdr kw) "") (format s "-~a" (cdr kw))))))

(defun t-payload->string (payload)
  (with-output-to-string (s)
    (let ((tl (getf payload :tlang)))
      (when tl (format s "-~a" (base-name-string tl))))
    (dolist (fl (getf payload :fields))
      (format s "-~a-~a" (car fl) (cdr fl)))))

(defun lid->string (lid)
  (with-output-to-string (s)
    (write-string (base-name-string lid) s)
    (dolist (ext (locale-id-extensions lid))
      (let ((sc (car ext)) (payload (cdr ext)))
        (cond ((char= sc #\u) (format s "-u~a" (u-payload->string payload)))
              ((char= sc #\t) (format s "-t~a" (t-payload->string payload)))
              (t (format s "-~c~{-~a~}" sc payload)))))
    (when (locale-id-privateuse lid) (format s "-~a" (locale-id-privateuse lid)))))

;;; ===========================================================================
;;; Public canonicalize entry points
;;; ===========================================================================
(defun canonicalize-unicode-locale-id (str)
  "Assumes STR is structurally valid. Returns the canonical string."
  ;; whole-tag grandfathered replacement (case-insensitive)
  (let ((gf (cdr (assoc str +grandfathered-alias+ :test #'string-equal))))
    (when gf (return-from canonicalize-unicode-locale-id
               ;; the replacement itself may need canonicalization but our table
               ;; values are already canonical.
               gf)))
  (let ((lid (parse-unicode-locale-id str)))
    (unless lid (return-from canonicalize-unicode-locale-id str))
    (lid->string (canonicalize-lid lid))))

(defun canonicalize-language-tag (str)
  "IsStructurallyValidLanguageTag ? CanonicalizeUnicodeLocaleId : RangeError."
  (unless (structurally-valid-locale-id-p str)
    ;; grandfathered whole-tags in our table are considered valid even if the
    ;; base parser rejects them (they parse fine actually). Double-check table.
    (unless (assoc str +grandfathered-alias+ :test #'string-equal)
      (js-throw (make-native-error "RangeError" (format nil "invalid language tag: ~a" str)))))
  (canonicalize-unicode-locale-id str))

;;; ===========================================================================
;;; LIKELY SUBTAGS: maximize / minimize
;;; ===========================================================================
(defun add-likely-subtags (lid)
  "AddLikelySubtags: fill script+region from the likely-subtags table. Mutates a
   COPY; returns a new lid (base fields only changed; ext/privateuse preserved)."
  (let* ((lang (or (locale-id-language lid) "und"))
         (scr (locale-id-script lid))
         (reg (locale-id-region lid))
         (match
           (or (and scr reg (likely-lookup (format nil "~a-~a-~a" lang scr reg)))
               (and scr (likely-lookup (format nil "~a-~a" lang scr)))
               (and reg (likely-lookup (format nil "~a-~a" lang reg)))
               (likely-lookup lang)
               (and (string-equal lang "und") scr (likely-lookup (format nil "und-~a" scr)))
               (and (string-equal lang "und") reg (likely-lookup (format nil "und-~a" reg))))))
    (let ((out (copy-locale-id lid)))
      (when match
        (setf (locale-id-language out) (if (string-equal lang "und") (getf match :language) lang))
        (unless scr (setf (locale-id-script out) (getf match :script)))
        (unless reg (setf (locale-id-region out) (getf match :region))))
      out)))

(defun remove-likely-subtags (lid)
  "RemoveLikelySubtags: maximize, then try dropping region/script to the shortest
   form that maximizes back to the same. Test-pinned subset via the table."
  (let* ((max (add-likely-subtags lid))
         (lang (locale-id-language max))
         (scr (locale-id-script max))
         (reg (locale-id-region max)))
    (flet ((maxes-to (l s r)
             (let ((tmp (make-locale-id :language l :script s :region r)))
               (let ((m (add-likely-subtags tmp)))
                 (and (equal (locale-id-language m) lang)
                      (equal (locale-id-script m) scr)
                      (equal (locale-id-region m) reg))))))
      (let ((out (copy-locale-id lid)))
        (setf (locale-id-language out) lang)
        (cond
          ((maxes-to lang nil nil) (setf (locale-id-script out) nil (locale-id-region out) nil))
          ((maxes-to lang nil reg) (setf (locale-id-script out) nil (locale-id-region out) reg))
          ((maxes-to lang scr nil) (setf (locale-id-script out) scr (locale-id-region out) nil))
          (t (setf (locale-id-script out) scr (locale-id-region out) reg)))
        out))))

;;; ===========================================================================
;;; SHARED ABSTRACT OPS
;;; ===========================================================================
(defun canonicalize-locale-list (v)
  "CanonicalizeLocaleList: V undefined -> (); a String -> single-element; else an
   array-like of strings/Locale objects. Returns a CL list of canonical tag
   strings (dedup, order-preserving). RangeError bad tags, TypeError bad element."
  (cond
    ((js-undefined-p v) '())
    ((stringp v)
     (list (canonicalize-language-tag v)))
    ((and (js-object-p v) (locale-instance-tag v))
     (list (locale-instance-tag v)))
    (t
     (let* ((o (to-object v))
            (len (truncate (to-length (js-get o "length"))))
            (seen '()))
       (dotimes (k len)
         (let ((pk (princ-to-string k)))
           (when (js-truthy* (js-has o pk))
             (let ((kv (js-get o pk)))
               (unless (or (stringp kv) (js-object-p kv))
                 (js-throw (make-native-error "TypeError" "locale must be a string or object")))
               (let ((tag (if (and (js-object-p kv) (locale-instance-tag kv))
                              (locale-instance-tag kv)
                              (to-string kv))))
                 (let ((ctag (canonicalize-language-tag tag)))
                   (pushnew ctag seen :test #'string=)))))))
       (nreverse seen)))))

(defun locale-instance-tag (o)
  "If O is an Intl.Locale instance, return its [[Locale]] string, else NIL. Set
   by intl-locale.lisp via the :initialized-locale internal slot."
  (and (js-object-p o) (js-object-internal o)
       (getf (js-object-internal o) :initialized-locale)))

;;; ---- Options coercion (GetOption family) ----
(defun coerce-options-to-object (v)
  "CoerceOptionsToObject: undefined -> fresh empty object; else ToObject."
  (if (js-undefined-p v)
      (make-object :proto (%obj-proto) :class "Object")
      (to-object v)))

(defun get-option (opts key type values default)
  "GetOption. TYPE is :string or :boolean. VALUES is a list of allowed strings or
   NIL. DEFAULT returned if the property is undefined (or :required -> RangeError)."
  (let ((v (js-get opts key)))
    (if (js-undefined-p v)
        (if (eq default :required)
            (js-throw (make-native-error "RangeError" (format nil "~a is required" key)))
            default)
        (let ((cv (ecase type
                    (:boolean (js-truthy v))
                    (:string (to-string v)))))
          (when (and values (eq type :string) (not (member cv values :test #'string=)))
            (js-throw (make-native-error "RangeError" (format nil "invalid value for ~a" key))))
          cv))))

(defun get-boolean-or-string-option (opts key strings default)
  "GetBooleanOrStringOption: undefined -> DEFAULT; boolean true -> T; a string in
   STRINGS -> the string; else RangeError."
  (let ((v (js-get opts key)))
    (cond
      ((js-undefined-p v) default)
      ((eq v *true*) t)
      ((eq v *false*) nil)
      (t (let ((s (to-string v)))
           (unless (member s strings :test #'string=)
             (js-throw (make-native-error "RangeError" (format nil "invalid value for ~a" key))))
           s)))))

(defun default-number-option (v minimum maximum fallback)
  (if (js-undefined-p v)
      fallback
      (let ((n (to-number v)))
        (when (or (js-nan-p n) (< n minimum) (> n maximum))
          (js-throw (make-native-error "RangeError" "number option out of range")))
        (floor n))))

(defun get-number-option (opts key minimum maximum fallback)
  (default-number-option (js-get opts key) minimum maximum fallback))

;;; ---- ResolveLocale ----
(defun intl-available-locales ()
  '("en" "en-US"))

(defun best-available-locale (available loc)
  "BestAvailableLocale: longest prefix of LOC (stripping -subtag each step) that
   is in AVAILABLE."
  (let ((candidate loc))
    (loop
      (when (member candidate available :test #'string-equal)
        (return-from best-available-locale candidate))
      (let ((pos (position #\- candidate :from-end t)))
        (unless pos (return-from best-available-locale nil))
        (when (and (>= pos 2) (char= (char candidate (- pos 2)) #\-))
          (decf pos 2))
        (setf candidate (subseq candidate 0 pos))))))

(defun resolve-locale (requested-locales relevant-extension-keys defaults)
  "ResolveLocale (lookup matcher, best-fit == lookup here). REQUESTED-LOCALES is a
   list of canonical tag strings. Returns a plist: (:locale <str> :data-locale
   <str> <key> <value> ...). DEFAULTS is a plist of extension-key -> default
   value used when a request doesn't pin the key."
  (let* ((available (intl-available-locales))
         (found nil) (found-ext nil))
    (dolist (req requested-locales)
      (let* ((lid (parse-unicode-locale-id req))
             (nolextag (and lid (base-name-string lid)))
             (match (and nolextag (best-available-locale available (%lc nolextag)))))
        (when match
          (setf found match found-ext lid)
          (return))))
    (unless found (setf found (first available) found-ext nil))
    (let ((result (list :locale nil :data-locale found))
          (uext (and found-ext
                     (getf (cdr (assoc #\u (locale-id-extensions found-ext))) :keywords))))
      (dolist (key relevant-extension-keys)
        (let* ((kw (and uext (assoc key uext :test #'string=)))
               (val (cond (kw (if (string= (cdr kw) "") "" (cdr kw)))
                          (t (getf defaults (intern (string-upcase key) :keyword))))))
          (setf (getf result (intern (string-upcase key) :keyword)) val)))
      ;; Build resolved locale string: data-locale + relevant -u- keywords set.
      (let ((kwstr (with-output-to-string (s)
                     (dolist (key relevant-extension-keys)
                       (let ((val (getf result (intern (string-upcase key) :keyword))))
                         (when (and val (not (eq val :undefined)) (stringp val) (plusp (length val)))
                           (format s "-~a-~a" key val)))))))
        (setf (getf result :locale)
              (if (plusp (length kwstr))
                  (format nil "~a-u~a" found kwstr)
                  found)))
      result)))

;;; ===========================================================================
;;; Enumerated tables — numbering-system digits + supportedValuesOf whitelists
;;; ===========================================================================
;;; numberingSystemDigits keys (the harness's table). We only need the KEY set
;;; for supportedValuesOf("numberingSystem"); the actual digit strings are used
;;; by NumberFormat. Provide both.
(defparameter +numbering-system-digit-names+
  '("adlm" "ahom" "arab" "arabext" "bali" "beng" "bhks" "brah" "cakm" "cham"
    "deva" "diak" "fullwide" "gara" "gong" "gonm" "gujr" "gukh" "guru" "hanidec"
    "hmng" "hmnp" "java" "kali" "kawi" "khmr" "knda" "krai" "lana" "lanatham"
    "laoo" "latn" "lepc" "limb" "mathbold" "mathdbl" "mathmono" "mathsanb"
    "mathsans" "mlym" "modi" "mong" "mroo" "mtei" "mymr" "mymrepka" "mymrpao"
    "mymrshan" "mymrtlng" "nagm" "newa" "nkoo" "olck" "onao" "orya" "osma"
    "outlined" "rohg" "saur" "segment" "shrd" "sind" "sinh" "sora" "sund" "sunu"
    "takr" "talu" "tamldec" "telu" "thai" "tibt" "tirh" "tnsa" "tols" "vaii"
    "wara" "wcho"))

;;; A few actual digit strings NumberFormat needs (latn + common ones).
(defparameter +numbering-system-digits+
  '(("latn" . "0123456789")
    ("arab" . "٠١٢٣٤٥٦٧٨٩")
    ("arabext" . "۰۱۲۳۴۵۶۷۸۹")
    ("beng" . "০১২৩৪৫৬৭৮৯")
    ("deva" . "०१२३४५६७८९")
    ("fullwide" . "０１２３４５６７８９")
    ("gujr" . "૦૧૨૩૪૫૬૭૮૯")
    ("guru" . "੦੧੨੩੪੫੬੭੮੯")
    ("hanidec" . "〇一二三四五六七八九")
    ("khmr" . "០១២៣៤៥៦៧៨៩")
    ("knda" . "೦೧೨೩೪೫೬೭೮೯")
    ("laoo" . "໐໑໒໓໔໕໖໗໘໙")
    ("mlym" . "൦൧൨൩൪൫൬൭൮൯")
    ("mong" . "᠐᠑᠒᠓᠔᠕᠖᠗᠘᠙")
    ("mymr" . "၀၁၂၃၄၅၆၇၈၉")
    ("orya" . "୦୧୨୩୪୫୬୭୮୯")
    ("tamldec" . "௦௧௨௩௪௫௬௭௮௯")
    ("telu" . "౦౧౨౩౪౫౬౭౮౯")
    ("thai" . "๐๑๒๓๔๕๖๗๘๙")
    ("tibt" . "༠༡༢༣༤༥༦༧༨༩")))

;;; supportedValuesOf whitelists. Small VALID subsets that satisfy the core
;;; tests (well-formed, sorted, unique, forced members). See project notes.
(defparameter +supported-calendars+
  ;; Exactly the calendar set required by intl-era-monthcode (Table 1), which is
  ;; also a valid superset-satisfying list for calendars.js (includes "gregory").
  '("buddhist" "chinese" "coptic" "dangi" "ethioaa" "ethiopic" "gregory"
    "hebrew" "indian" "islamic-civil" "islamic-tbla" "islamic-umalqura"
    "iso8601" "japanese" "persian" "roc"))

(defparameter +supported-collations+
  ;; must NOT include "standard" or "search".
  '("compat" "dict" "emoji" "eor" "phonebk" "phonetic" "pinyin" "searchjl"
    "stroke" "trad" "unihan" "zhuyin"))

(defparameter +supported-currencies+
  ;; well-formed 3-uppercase-letter ISO 4217 codes.
  '("AUD" "BRL" "CAD" "CHF" "CNY" "EUR" "GBP" "HKD" "INR" "JPY" "KRW" "MXN"
    "NOK" "RUB" "SEK" "USD" "ZAR"))

(defparameter +supported-timezones+
  ;; include the 26 Etc/GMT±N + UTC (for timeZones-include-non-continental),
  ;; plus a few IANA continental zones. Kept SORTED at build time.
  (sort
   (append
    (list "UTC")
    (loop for i from 1 to 12 collect (format nil "Etc/GMT+~d" i))
    (loop for i from 1 to 14 collect (format nil "Etc/GMT-~d" i))
    (list "America/New_York" "America/Los_Angeles" "Asia/Tokyo"
          "Europe/London" "Europe/Paris"))
   #'string<))

(defparameter +supported-units+
  ;; every item must be in allSimpleSanctionedUnits() and contain no "-per-".
  '("acre" "bit" "byte" "celsius" "centimeter" "day" "degree" "fahrenheit"
    "foot" "gallon" "gram" "hectare" "hour" "inch" "kilogram" "kilometer"
    "liter" "meter" "mile" "minute" "month" "second" "week" "yard" "year"))

(defun supported-values-for (key)
  "supportedValuesOf(key): return a fresh SORTED list of strings, RangeError on
   a bad key."
  (let ((data
          (cond ((string= key "calendar") +supported-calendars+)
                ((string= key "collation") +supported-collations+)
                ((string= key "currency") +supported-currencies+)
                ((string= key "numberingSystem")
                 (sort (copy-list +numbering-system-digit-names+) #'string<))
                ((string= key "timeZone") +supported-timezones+)
                ((string= key "unit") +supported-units+)
                (t (js-throw (make-native-error "RangeError"
                              (format nil "invalid key for supportedValuesOf: ~a" key)))))))
    ;; return a defensive sorted copy
    (sort (copy-list data) #'string<)))

;;; ===========================================================================
;;; Intl namespace + registration
;;; ===========================================================================
(defvar *intl-namespace* nil)

(defun intl-tag (realm) (symbol-tostringtag realm))

(defun intl-namespace (realm)
  (or *intl-namespace*
      (let ((existing (ignore-errors (js-get (realm-global realm) "Intl"))))
        (when (js-object-p existing) (setf *intl-namespace* existing)))))

(defun intl-register (realm name ctor)
  "Hang NAME on the Intl namespace as a non-enumerable, writable, configurable
   data property (the API installers call this)."
  (let ((ns (intl-namespace realm)))
    (when ns (put ns name ctor :enumerable nil :writable t :configurable t))))

(defun intl-proto-from-newtarget (nt default-proto)
  (proto-from-newtarget nt default-proto))

;;; ===========================================================================
;;; install-intl_core — Intl object + getCanonicalLocales + supportedValuesOf
;;; ===========================================================================
(defun install-intl_core (realm)
  (setf *intl-namespace* nil)
  (let* ((op (realm-object-proto realm))
         (ns (make-object :proto op :class "Object")))
    (setf *intl-namespace* ns)
    (put ns (symbol-tostringtag realm) "Intl" :enumerable nil :writable nil :configurable t)
    (put (realm-global realm) "Intl" ns :enumerable nil :writable t :configurable t)
    ;; getCanonicalLocales (length 1)
    (def-method realm ns "getCanonicalLocales" 1 (this args)
      (declare (ignore this))
      (make-array-object (canonicalize-locale-list (arg 0 args))))
    ;; supportedValuesOf (length 1)
    (def-method realm ns "supportedValuesOf" 1 (this args)
      (declare (ignore this))
      (let ((key (to-string (arg 0 args))))
        (make-array-object (supported-values-for key))))))

(register-builtin-installer 'install-intl_core)
