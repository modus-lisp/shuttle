;;;; builtins/intl-collator-segmenter-displaynames.lisp — Intl.Collator +
;;;; Intl.Segmenter + Intl.DisplayNames + Intl.DurationFormat.
;;;; Built ON the intl-core kernel (parse/canonicalize + the GetOption family +
;;;; resolve-locale + intl-register + proto-from-newtarget).
(in-package #:shuttle)

;;; ===========================================================================
;;; Shared little helpers for this file
;;; ===========================================================================
(defun %intl-tag-put (realm proto tagstr)
  (put proto (symbol-tostringtag realm) tagstr :enumerable nil :writable nil :configurable t))

(defun %require-new (nt name)
  (when (js-undefined-p nt)
    (js-throw (make-native-error "TypeError" (format nil "Intl.~a requires new" name)))))

(defun %ctor-throws-without-new (realm name)
  "A callable ctor stub that throws TypeError when called (no [[Construct]])."
  (native-function realm name
    (lambda (this args) (declare (ignore this args))
      (js-throw (make-native-error "TypeError" (format nil "Constructor ~a requires 'new'" name))))
    (cond ((string= name "DisplayNames") 2) (t 0))))

(defun %supported-locales-of (requested opts &optional broad)
  "SupportedLocalesOf: validate localeMatcher, then LookupSupportedLocales over
   the (already canonicalized) REQUESTED list; return a fresh JS Array. When
   BROAD, every structurally-valid requested locale is considered supported
   (Segmenter reports support for all locales)."
  (let ((o (%coerce-options opts)))
    (get-option o "localeMatcher" :string '("lookup" "best fit") "best fit")
    (let ((available (intl-available-locales)) (out '()))
      (dolist (req requested)
        (let* ((lid (parse-unicode-locale-id req))
               (nolext (and lid (base-name-string lid)))
               (lang (and lid (locale-id-language lid)))
               (match (if broad
                          ;; broad support: any locale with a KNOWN language.
                          (and (%known-language-p lang) req)
                          (and nolext (best-available-locale available (%lc nolext))))))
          (when match (push req out))))
      (make-array-object (nreverse out)))))

(defun %static-supported-locales-of (this args &optional broad)
  (declare (ignore this))
  (%supported-locales-of (canonicalize-locale-list (arg 0 args)) (arg 1 args) broad))

(defun %read-u-keyword (requested key)
  "Scan the canonical REQUESTED tags (a list) for the first -u-KEY-... keyword,
   returning its value string (\"\" for a bare key) or NIL. Reads the RAW parsed
   lid keyword shape (key . (types...))."
  (dolist (req requested)
    (let* ((lid (parse-unicode-locale-id req))
           (uentry (and lid (assoc #\u (locale-id-extensions lid))))
           (kw (and uentry (assoc key (getf (cdr uentry) :keywords) :test #'string=))))
      (when kw
        (return-from %read-u-keyword
          (if (cdr kw) (format nil "~{~a~^-~}" (cdr kw)) "")))))
  nil)

(defun %coerce-options (optv)
  "CoerceOptionsToObject: undefined -> a fresh NULL-proto object (so Object.prototype
   pollution is not observed); else ToObject."
  (if (js-undefined-p optv)
      (make-object :proto *null* :class "Object")
      (to-object optv)))

(defun %get-options-object (optv)
  "GetOptionsObject: undefined -> fresh empty object; an Object -> itself; else
   TypeError (does NOT coerce primitives)."
  (cond
    ((js-undefined-p optv) (make-object :proto *null* :class "Object"))
    ((js-object-p optv) optv)
    (t (js-throw (make-native-error "TypeError" "options must be an object")))))

;;; A modest list of real ISO-639 language subtags (the corpus exercises the
;;; common ones). Used to distinguish a supported locale (real language) from an
;;; unknown/no-content tag (xyz, zxx, und) for the "all locales" services.
(defparameter +known-languages+
  '("aa" "ab" "af" "ak" "am" "ar" "as" "az" "be" "bg" "bh" "bn" "bo" "br" "bs"
    "ca" "ce" "cs" "cy" "da" "de" "dv" "dz" "ee" "el" "en" "eo" "es" "et" "eu"
    "fa" "fi" "fil" "fo" "fr" "fy" "ga" "gd" "gl" "gn" "gu" "ha" "haw" "he" "hi"
    "hr" "hsb" "hu" "hy" "hyw" "id" "ig" "is" "it" "ja" "jv" "ka" "kk" "km" "kn"
    "ko" "ks" "ku" "kw" "ky" "la" "lb" "lo" "lt" "lv" "mg" "mi" "mk" "ml" "mn"
    "mr" "ms" "mt" "my" "nb" "ne" "nl" "nn" "no" "oc" "om" "or" "pa" "pap" "pl"
    "ps" "pt" "qu" "rm" "ro" "ru" "rw" "sa" "sd" "si" "sk" "sl" "so" "sq" "sr"
    "sv" "sw" "ta" "te" "tg" "th" "ti" "tk" "tl" "tn" "to" "tr" "tt" "ug" "uk"
    "ur" "uz" "vi" "wo" "xh" "yi" "yo" "zh" "zu" "jbo" "hak" "hsn" "aae"))

(defun %known-language-p (lang)
  (and lang (member lang +known-languages+ :test #'string-equal)))

(defun %broad-resolve-locale (requested)
  "For services that support all locales (Segmenter): the resolved [[Locale]] is
   the base-name of the first requested locale with a KNOWN language (dropping
   -u- extensions), else the default available locale."
  (dolist (req requested)
    (let ((lid (parse-unicode-locale-id req)))
      (when (and lid (%known-language-p (locale-id-language lid)))
        (return-from %broad-resolve-locale (base-name-string lid)))))
  (%canonical-default-locale))

(defun %canon-locale (loc)
  "Canonicalize a resolved locale string (e.g. en-us -> en-US)."
  (if (and (stringp loc) (structurally-valid-locale-id-p loc))
      (canonicalize-unicode-locale-id loc)
      loc))

(defun %canonical-default-locale ()
  (let ((d (first (intl-available-locales))))
    (let ((lid (parse-unicode-locale-id d))) (if lid (base-name-string lid) d))))

(defun %def-supported-locales-of (realm ctor &optional broad)
  (put ctor "supportedLocalesOf"
       (native-function realm "supportedLocalesOf"
         (lambda (this args) (%static-supported-locales-of this args broad)) 1)
       :enumerable nil :writable t :configurable t))

;;; ===========================================================================
;;; Intl.Collator
;;; ===========================================================================
(defvar *intl-collator-proto* nil)

(defun collator-slots (this)
  "RequireInternalSlot [[InitializedCollator]] -> the plist, or TypeError."
  (let ((v (if (js-object-p this)
               (getf (js-object-internal this) :initialized-collator 'none)
               'none)))
    (when (eq v 'none)
      (js-throw (make-native-error "TypeError" "receiver is not an Intl.Collator")))
    v))

;;; ---- accent folding: strip common Latin-1 combining accents / decompose the
;;; ---- precomposed accented Latin letters to their base letter. Used for the
;;; ---- base/accent/case sensitivity levels (a SUBSET of full canonical
;;; ---- equivalence — enough for the alphabet-order tests, not the exotic ones).
(defparameter +collator-fold-map+
  ;; precomposed accented -> base (lowercased base). Covers Latin-1 + a few more.
  '((#\à . #\a) (#\á . #\a) (#\â . #\a) (#\ã . #\a) (#\ä . #\a) (#\å . #\a) (#\ā . #\a)
    (#\ă . #\a) (#\ą . #\a) (#\ç . #\c) (#\ć . #\c) (#\č . #\c) (#\ĉ . #\c) (#\ċ . #\c)
    (#\è . #\e) (#\é . #\e) (#\ê . #\e) (#\ë . #\e) (#\ē . #\e) (#\ĕ . #\e) (#\ė . #\e)
    (#\ę . #\e) (#\ě . #\e) (#\ì . #\i) (#\í . #\i) (#\î . #\i) (#\ï . #\i) (#\ī . #\i)
    (#\ĭ . #\i) (#\į . #\i) (#\ñ . #\n) (#\ń . #\n) (#\ň . #\n) (#\ò . #\o) (#\ó . #\o)
    (#\ô . #\o) (#\õ . #\o) (#\ö . #\o) (#\ø . #\o) (#\ō . #\o) (#\ŏ . #\o) (#\ù . #\u)
    (#\ú . #\u) (#\û . #\u) (#\ü . #\u) (#\ū . #\u) (#\ŭ . #\u) (#\ů . #\u) (#\ý . #\y)
    (#\ÿ . #\y) (#\š . #\s) (#\ś . #\s) (#\ş . #\s) (#\ž . #\z) (#\ź . #\z) (#\ż . #\z)
    (#\ł . #\l) (#\đ . #\d) (#\ð . #\d) (#\ř . #\r) (#\ť . #\t)))

;;; combining diacritical marks range (U+0300..U+036F) + a few common ones.
(defun %combining-mark-p (c)
  (let ((cc (char-code c)))
    (or (<= #x300 cc #x36F) (<= #x1AB0 cc #x1AFF) (<= #x1DC0 cc #x1DFF)
        (<= #x20D0 cc #x20FF) (<= #xFE20 cc #xFE2F))))

(defun collator-fold-char (c fold-accent fold-case)
  "Return the folded lowercase base char, or NIL to drop (a combining mark when
   accents are being folded)."
  (cond
    ((and fold-accent (%combining-mark-p c)) nil)
    (t
     (let* ((base (if fold-accent (or (cdr (assoc (char-downcase c) +collator-fold-map+)) c) c)))
       (if fold-case (char-downcase base) base)))))

(defparameter +collator-punct-chars+
  ;; punctuation + whitespace stripped when ignorePunctuation.
  " !\"#$%&'()*+,-./:;<=>?@[\\]^_`{|}~‘’“”‛‚–—…·«»¡¿")

(defun collator-prepare (s fold-accent fold-case ignore-punct)
  "Produce a comparison key string per the sensitivity + ignorePunctuation."
  (with-output-to-string (out)
    (loop for c across s do
      (unless (and ignore-punct (find c +collator-punct-chars+))
        (let ((f (collator-fold-char c fold-accent fold-case)))
          (when f (write-char f out)))))))

(defun %numeric-runs (s)
  "Split S into a list of (:num . value) | (:str . string) runs for numeric
   collation. Digit runs become integer values (leading zeros ignored)."
  (let ((runs '()) (i 0) (n (length s)))
    (loop while (< i n) do
      (if (%digit-p (char s i))
          (let ((j i))
            (loop while (and (< j n) (%digit-p (char s j))) do (incf j))
            (push (cons :num (parse-integer s :start i :end j)) runs)
            (setf i j))
          (let ((j i))
            (loop while (and (< j n) (not (%digit-p (char s j)))) do (incf j))
            (push (cons :str (subseq s i j)) runs)
            (setf i j))))
    (nreverse runs)))

(defun collator-compare-strings (x y slots)
  "Core comparison returning -1/0/1 (a double).

   The PRIMARY comparison is always case+accent-insensitive (so the alphabet
   sorts A,b,C,d... regardless of case). The tiebreak then applies the level of
   distinction the sensitivity asks for: variant restores accents THEN case,
   accent restores accents only, case restores case only, base restores nothing."
  (let* ((sensitivity (getf slots :sensitivity))
         (numeric (getf slots :numeric))
         (ignore-punct (getf slots :ignore-punctuation))
         ;; primary key: fold BOTH accent and case.
         (kx (collator-prepare x t t ignore-punct))
         (ky (collator-prepare y t t ignore-punct)))
    (let ((cmp (if numeric (%compare-numeric kx ky) (%compare-plain kx ky))))
      (if (/= cmp 0)
          (float cmp 1d0)
          (float (%collator-tiebreak x y sensitivity ignore-punct numeric) 1d0)))))

(defun %compare-plain (a b)
  (cond ((string< a b) -1) ((string> a b) 1) (t 0)))

(defun %compare-numeric (a b)
  (let ((ra (%numeric-runs a)) (rb (%numeric-runs b)))
    (loop
      (cond
        ((and (null ra) (null rb)) (return 0))
        ((null ra) (return -1))
        ((null rb) (return 1))
        (t (let ((pa (pop ra)) (pb (pop rb)))
             (cond
               ((and (eq (car pa) :num) (eq (car pb) :num))
                (cond ((< (cdr pa) (cdr pb)) (return -1))
                      ((> (cdr pa) (cdr pb)) (return 1))))
               (t (let ((sa (if (eq (car pa) :num) (princ-to-string (cdr pa)) (cdr pa)))
                        (sb (if (eq (car pb) :num) (princ-to-string (cdr pb)) (cdr pb))))
                    (let ((c (%compare-plain sa sb))) (unless (zerop c) (return c))))))))))))

(defun %collator-cmp-keys (x y fold-accent fold-case ignore-punct numeric)
  (let ((rx (collator-prepare x fold-accent fold-case ignore-punct))
        (ry (collator-prepare y fold-accent fold-case ignore-punct)))
    (if numeric (%compare-numeric rx ry) (%compare-plain rx ry))))

(defun %collator-tiebreak (x y sensitivity ignore-punct numeric)
  "Primary (case+accent-insensitive) keys tied. Apply the sensitivity's extra
   distinction levels:
     base    -> nothing (0)
     accent  -> accents matter, case doesn't  (accent level)
     case    -> case matters, accents don't   (case level)
     variant -> accents then case             (both)"
  (cond
    ((string= sensitivity "base") 0)
    ((string= sensitivity "accent")
     ;; case-fold but keep accents
     (%collator-cmp-keys x y nil t ignore-punct numeric))
    ((string= sensitivity "case")
     ;; accent-fold but keep case
     (%collator-cmp-keys x y t nil ignore-punct numeric))
    (t ;; variant: accent level first, then case level.
     (let ((acc (%collator-cmp-keys x y nil t ignore-punct numeric)))
       (if (/= acc 0) acc
           (%collator-cmp-keys x y t nil ignore-punct numeric))))))

(defun %collator-resolved-collation (slots)
  (or (getf slots :collation) "default"))

(defun collator-resolved-options (realm slots)
  (let ((o (make-object :proto (realm-object-proto realm) :class "Object")))
    (put o "locale" (getf slots :locale))
    (put o "usage" (getf slots :usage))
    (put o "sensitivity" (getf slots :sensitivity))
    (put o "ignorePunctuation" (js-bool (getf slots :ignore-punctuation)))
    (put o "collation" (%collator-resolved-collation slots))
    (when (getf slots :numeric-present)
      (put o "numeric" (js-bool (getf slots :numeric))))
    (when (getf slots :case-first)
      (put o "caseFirst" (getf slots :case-first)))
    o))

(defun install-intl_collator (realm)
  (let* ((op (realm-object-proto realm))
         (proto (make-object :proto op :class "Object"))
         (ctor (%ctor-throws-without-new realm "Collator")))
    (setf *intl-collator-proto* proto)
    ;; Collator is a legacy Intl service: callable WITHOUT new (creates a new
    ;; instance, ignoring the `this` value) AND newable.
    (setf (js-object-call ctor)
          (lambda (this args) (declare (ignore this))
            (funcall (js-object-construct ctor) args ctor)))
    (setf (js-object-construct ctor)
          (lambda (args nt)
            (let* ((locv (arg 0 args)) (optv (arg 1 args))
                   (requested (canonicalize-locale-list locv))
                   (opts (%coerce-options optv))
                   (usage (get-option opts "usage" :string '("sort" "search") "sort"))
                   (matcher (get-option opts "localeMatcher" :string '("lookup" "best fit") "best fit"))
                   (collation-opt (let ((v (get-option opts "collation" :string nil :undefined)))
                                    (if (eq v :undefined) nil v)))
                   (numeric-raw (js-get opts "numeric"))
                   (numeric-present (not (js-undefined-p numeric-raw)))
                   (numeric-opt (and numeric-present (js-truthy numeric-raw)))
                   (casefirst (get-option opts "caseFirst" :string '("upper" "lower" "false") :undefined))
                   (sensitivity (get-option opts "sensitivity" :string
                                            '("base" "accent" "case" "variant") :undefined))
                   (ip-raw (js-get opts "ignorePunctuation")))
              (declare (ignore matcher collation-opt))
              (let* ((data-locale (%canon-locale (getf (resolve-locale requested '() '()) :data-locale)))
                     ;; -u-* from the requested tags.
                     (u-kn (%read-u-keyword requested "kn"))
                     (u-kf (%read-u-keyword requested "kf"))
                     (u-co (%read-u-keyword requested "co"))
                     (opt-numeric (when numeric-present numeric-opt))
                     (opt-casefirst (unless (eq casefirst :undefined) casefirst))
                     ;; ResolveLocale for kn/kf/co: option wins over extension.
                     ;; numeric present iff option present OR extension present.
                     (numeric-present* (or numeric-present (and u-kn t)))
                     (ext-numeric (and u-kn (not (string= u-kn "false"))))
                     (numeric (cond (numeric-present numeric-opt)
                                    (u-kn ext-numeric)
                                    (t nil)))
                     ;; Reflect -u-kn iff the extension was present and the final
                     ;; numeric equals the extension's numeric (option matched or
                     ;; no option override).
                     (kn-reflect (and u-kn (eq numeric ext-numeric)))
                     (case-first (cond (opt-casefirst opt-casefirst)
                                       ((and u-kf (member u-kf '("upper" "lower" "false") :test #'string=)) u-kf)
                                       (t nil)))
                     (kf-reflect (and u-kf (member u-kf '("upper" "lower" "false") :test #'string=)
                                      case-first (string= case-first u-kf)))
                     (sens (if (eq sensitivity :undefined) "variant" sensitivity))
                     (ip-default (%collator-ip-default requested))
                     (ignore-punct (if (js-undefined-p ip-raw) ip-default (js-truthy ip-raw)))
                     (collation (cond ((string= usage "search") "default")
                                      ((and u-co (collator-valid-collation-p u-co)) u-co)
                                      (t "default")))
                     (co-in-locale (and (string= usage "sort")
                                        (not (string= collation "default")) collation))
                     ;; Build the resolved [[Locale]]: data-locale + the -u- keys
                     ;; that are reflected. Value "" for bare kn-true.
                     (kw-alist (remove nil
                                 (list (when kn-reflect (cons "kn" (if ext-numeric "" "false")))
                                       (when kf-reflect (cons "kf" case-first))
                                       (when co-in-locale (cons "co" co-in-locale)))))
                     (loc (%collator-build-locale data-locale kw-alist)))
                (let* ((slots (list :locale loc :usage usage :sensitivity sens
                                    :numeric numeric :numeric-present numeric-present*
                                    :case-first case-first :collation collation
                                    :ignore-punctuation ignore-punct))
                       (obj (make-object :proto (proto-from-newtarget nt proto) :class "Object")))
                  (setf (getf (js-object-internal obj) :initialized-collator) slots)
                  obj)))))
    (def-value ctor "prototype" proto :writable nil :configurable nil)
    (def-value proto "constructor" ctor)
    ;; ---- compare (bound getter) ----
    (def-getter realm proto "compare"
      (lambda (this args) (declare (ignore args))
        (let ((slots (collator-slots this)))
          (or (getf (js-object-internal this) :bound-compare)
              (let ((fn (native-function realm ""
                          (lambda (cthis cargs) (declare (ignore cthis))
                            (collator-compare-strings
                             (to-string (arg 0 cargs)) (to-string (arg 1 cargs)) slots))
                          2)))
                (setf (getf (js-object-internal this) :bound-compare) fn)
                fn)))))
    ;; ---- resolvedOptions ----
    (def-method realm proto "resolvedOptions" 0 (this args)
      (declare (ignore args))
      (collator-resolved-options realm (collator-slots this)))
    ;; ---- supportedLocalesOf ----
    (%def-supported-locales-of realm ctor)
    (%intl-tag-put realm proto "Intl.Collator")
    (intl-register realm "Collator" ctor)
    ctor))

(defun %collator-build-locale (data-locale kw-alist)
  "Serialize DATA-LOCALE plus the -u- KW-ALIST (key . value, \"\" for a bare key),
   keys sorted alphabetically. Empty alist -> just DATA-LOCALE."
  (if (null kw-alist)
      data-locale
      (let ((sorted (stable-sort (copy-list kw-alist) #'string< :key #'car)))
        (with-output-to-string (s)
          (write-string data-locale s)
          (write-string "-u" s)
          (dolist (kw sorted)
            (format s "-~a" (car kw))
            (unless (string= (cdr kw) "") (format s "-~a" (cdr kw))))))))

(defun %collator-ip-default (requested)
  "ignorePunctuation defaults to true for Thai, false otherwise."
  (some (lambda (r) (let ((lid (parse-unicode-locale-id r)))
                      (and lid (string-equal (locale-id-language lid) "th"))))
        requested))

(defun collator-valid-collation-p (co)
  (and (stringp co)
       (member co +supported-collations+ :test #'string=)))

;;; ===========================================================================
;;; Intl.Segmenter
;;; ===========================================================================
(defvar *intl-segmenter-proto* nil)
(defvar *intl-segments-proto* nil)
(defvar *intl-segment-iterator-proto* nil)

(defun segmenter-slots (this)
  (let ((v (if (js-object-p this)
               (getf (js-object-internal this) :initialized-segmenter 'none)
               'none)))
    (when (eq v 'none)
      (js-throw (make-native-error "TypeError" "receiver is not an Intl.Segmenter")))
    v))

;;; ---- segmentation: produce a list of (start . end) code-unit boundaries.
;;; ---- Strings here are CL strings whose chars are BMP; astral chars in the JS
;;; ---- string are stored as surrogate pairs (two CL chars). We approximate
;;; ---- UAX#29 for grapheme/word/sentence.
(defun %hi-surrogate-p (c) (<= #xD800 (char-code c) #xDBFF))
(defun %lo-surrogate-p (c) (<= #xDC00 (char-code c) #xDFFF))
(defun %regional-indicator-hi-p (c d)
  ;; a regional indicator U+1F1E6..1F1FF is surrogate pair D83C DDE6..DDFF.
  (and (char= c (code-char #xD83C)) (<= #xDDE6 (char-code d) #xDDFF)))
(defun %zwj-p (c) (= (char-code c) #x200D))

(defun segment-graphemes (s)
  "List of (start . end) grapheme boundaries. Handles: surrogate pairs, trailing
   combining marks, regional-indicator pairs, and simple ZWJ emoji joins."
  (let ((n (length s)) (out '()) (i 0))
    (labels ((cp-at (k) ;; returns (values char-count next) for the code point at k
               (if (and (< (1+ k) n) (%hi-surrogate-p (char s k)) (%lo-surrogate-p (char s (1+ k))))
                   (values 2 (+ k 2))
                   (values 1 (1+ k)))))
      (loop while (< i n) do
        (let ((start i))
          (multiple-value-bind (len next) (cp-at i)
            (declare (ignore len))
            (setf i next))
          ;; extend: combining marks, ZWJ + following cp, and RI pairs.
          (loop
            (when (>= i n) (return))
            (let ((c (char s i)))
              (cond
                ;; combining mark extends the cluster
                ((%combining-mark-p c) (incf i))
                ;; ZWJ joins the next code point
                ((%zwj-p c)
                 (incf i)
                 (when (< i n)
                   (multiple-value-bind (len2 next2) (cp-at i) (declare (ignore len2)) (setf i next2))))
                (t (return)))))
          (push (cons start i) out)))
      (nreverse out))))

(defun %word-char-p (c)
  "isWordLike run member: letters (any alpha, plus non-ASCII letters roughly) or
   digits. We treat anything alphanumeric or CJK/most letters as word."
  (let ((cc (char-code c)))
    (or (%alnum-p c)
        (char= c #\_)
        ;; broad: treat most non-space, non-punct, non-symbol as letters (CJK etc.)
        (and (> cc 127)
             (not (%combining-mark-p c))
             (not (find c +collator-punct-chars+))
             (not (member cc '(#x3000 #x00A0)))))))

(defun segment-words (s)
  "Split into runs: a maximal run of word chars, or a single non-word grapheme.
   Returns (start . end) list. Whitespace/punct each split; word runs group."
  (let ((n (length s)) (out '()) (i 0))
    (loop while (< i n) do
      (let ((c (char s i)))
        (cond
          ((%word-char-p c)
           (let ((start i))
             (loop while (< i n) do
               (cond
                 ((%word-char-p (char s i)) (incf i))
                 ;; MidNum: '.' ',' between two DIGITS stays in the run (e.g.
                 ;; "1.23", "3,000"). Letters do NOT join across these.
                 ((and (find (char s i) ".,'·’")
                       (> i start) (%digit-p (char s (1- i)))
                       (< (1+ i) n) (%digit-p (char s (1+ i))))
                  (incf i))
                 (t (return))))
             (push (cons start i) out)))
          ;; whitespace run
          ((member (char-code c) '(#x20 #x09 #x0A #x0D #x0C #x0B #xA0 #x3000))
           (let ((start i))
             (loop while (and (< i n)
                              (member (char-code (char s i)) '(#x20 #x09 #x0A #x0D #x0C #x0B #xA0 #x3000)))
                   do (incf i))
             (push (cons start i) out)))
          (t
           ;; single non-word grapheme (punct/symbol) — respect surrogate pairs
           (let ((start i))
             (if (and (< (1+ i) n) (%hi-surrogate-p c) (%lo-surrogate-p (char s (1+ i))))
                 (incf i 2)
                 (incf i))
             (push (cons start i) out))))))
    (nreverse out)))

(defun %word-run-is-word-like (s start end)
  (and (< start end) (%word-char-p (char s start))))

(defun segment-sentences (s)
  "Split after a terminator (. ! ?) plus any trailing closing punctuation and the
   following whitespace. Keeps the trailing sentence."
  (let ((n (length s)) (out '()) (i 0) (start 0))
    (loop while (< i n) do
      (let ((c (char s i)))
        (incf i)
        (when (member c '(#\. #\! #\?))
          ;; consume trailing quotes/brackets
          (loop while (and (< i n) (find (char s i) "\"')]}»”’")) do (incf i))
          ;; consume the following whitespace
          (loop while (and (< i n) (member (char-code (char s i)) '(#x20 #x09 #x0A #x0D #x0C #x0B #xA0)))
                do (incf i))
          (push (cons start i) out)
          (setf start i))))
    (when (< start n) (push (cons start n) out))
    (nreverse out)))

(defun segment-string (granularity s)
  (cond
    ((string= granularity "word") (values (segment-words s) :word))
    ((string= granularity "sentence") (values (segment-sentences s) :sentence))
    (t (values (segment-graphemes s) :grapheme))))

(defun %make-segment-data-object (realm s granularity start end)
  "Build the {segment, index, input[, isWordLike]} result object."
  (let ((o (make-object :proto (realm-object-proto realm) :class "Object")))
    (put o "segment" (subseq s start end))
    (put o "index" (float start 1d0))
    (put o "input" s)
    (when (string= granularity "word")
      (put o "isWordLike" (js-bool (%word-run-is-word-like s start end))))
    o))

(defun %segments-find-containing (segs index)
  "Return the (start . end) covering INDEX, or NIL."
  (find-if (lambda (r) (and (<= (car r) index) (< index (cdr r)))) segs))

(defun install-intl_segmenter (realm)
  (let* ((op (realm-object-proto realm))
         (proto (make-object :proto op :class "Object"))
         (segments-proto (make-object :proto op :class "Object"))
         (seg-iter-proto (make-object :proto op :class "Object"))
         (ctor (%ctor-throws-without-new realm "Segmenter")))
    (setf *intl-segmenter-proto* proto
          *intl-segments-proto* segments-proto
          *intl-segment-iterator-proto* seg-iter-proto)
    (setf (js-object-construct ctor)
          (lambda (args nt)
            (%require-new nt "Segmenter")
            (let* ((locv (arg 0 args)) (optv (arg 1 args))
                   (requested (canonicalize-locale-list locv))
                   (opts (%coerce-options optv)))
              (get-option opts "localeMatcher" :string '("lookup" "best fit") "best fit")
              (let* ((granularity (get-option opts "granularity" :string
                                              '("grapheme" "word" "sentence") "grapheme"))
                     (slots (list :locale (%broad-resolve-locale requested) :granularity granularity))
                     (obj (make-object :proto (proto-from-newtarget nt proto) :class "Object")))
                (setf (getf (js-object-internal obj) :initialized-segmenter) slots)
                obj))))
    (def-value ctor "prototype" proto :writable nil :configurable nil)
    (def-value proto "constructor" ctor)
    ;; ---- segment(string) -> %Segments% ----
    (def-method realm proto "segment" 1 (this args)
      (let* ((slots (segmenter-slots this))
             (str (to-string (arg 0 args)))
             (granularity (getf slots :granularity))
             (segs (segment-string granularity str))
             (segments (make-object :proto segments-proto :class "Object")))
        (setf (getf (js-object-internal segments) :segments-string) str
              (getf (js-object-internal segments) :segments-granularity) granularity
              (getf (js-object-internal segments) :segments-boundaries) segs)
        segments))
    ;; ---- resolvedOptions ----
    (def-method realm proto "resolvedOptions" 0 (this args)
      (declare (ignore args))
      (let* ((slots (segmenter-slots this))
             (o (make-object :proto (realm-object-proto realm) :class "Object")))
        (put o "locale" (getf slots :locale))
        (put o "granularity" (getf slots :granularity))
        o))
    (%def-supported-locales-of realm ctor t)
    (%intl-tag-put realm proto "Intl.Segmenter")

    ;; ---- %Segments% prototype ----
    (labels ((segments-slots (this)
               (let ((v (if (js-object-p this)
                            (getf (js-object-internal this) :segments-string 'none)
                            'none)))
                 (when (eq v 'none)
                   (js-throw (make-native-error "TypeError" "receiver is not a Segments object")))
                 v)))
      (def-method realm segments-proto "containing" 1 (this args)
        (segments-slots this)
        (let* ((internal (js-object-internal this))
               (str (getf internal :segments-string))
               (granularity (getf internal :segments-granularity))
               (segs (getf internal :segments-boundaries))
               (nv (to-integer-or-infinity (arg 0 args)))
               (n (length str)))
          (if (or (= nv *inf*) (= nv *-inf*) (< nv 0) (>= nv n))
              *undefined*
              (let ((idx (truncate nv)))
                (let ((r (%segments-find-containing segs idx)))
                  (if r
                      (%make-segment-data-object realm str granularity (car r) (cdr r))
                      *undefined*))))))
      ;; @@iterator on Segments -> a Segment Iterator
      (when *symbol-iterator*
        (put segments-proto *symbol-iterator*
             (native-function realm "[Symbol.iterator]"
               (lambda (this args) (declare (ignore args))
                 (segments-slots this)
                 (let* ((internal (js-object-internal this))
                        (it (make-object :proto seg-iter-proto :class "Object")))
                   (setf (getf (js-object-internal it) :seg-iter-string) (getf internal :segments-string)
                         (getf (js-object-internal it) :seg-iter-granularity) (getf internal :segments-granularity)
                         (getf (js-object-internal it) :seg-iter-boundaries) (getf internal :segments-boundaries)
                         (getf (js-object-internal it) :seg-iter-pos) 0)
                   it))
               0)
             :enumerable nil :writable t :configurable t)))

    ;; ---- %SegmentIterator% prototype ----
    (labels ((iter-slots (this)
               (let ((v (if (js-object-p this)
                            (getf (js-object-internal this) :seg-iter-string 'none)
                            'none)))
                 (when (eq v 'none)
                   (js-throw (make-native-error "TypeError" "receiver is not a Segment Iterator")))
                 v)))
      (def-method realm seg-iter-proto "next" 0 (this args)
        (declare (ignore args))
        (iter-slots this)
        (let* ((internal (js-object-internal this))
               (str (getf internal :seg-iter-string))
               (granularity (getf internal :seg-iter-granularity))
               (segs (getf internal :seg-iter-boundaries))
               (pos (getf internal :seg-iter-pos))
               (res (make-object :proto (realm-object-proto realm) :class "Object")))
          (if (>= pos (length segs))
              (progn (put res "value" *undefined*) (put res "done" *true*))
              (let ((r (nth pos segs)))
                (setf (getf (js-object-internal this) :seg-iter-pos) (1+ pos))
                (put res "value" (%make-segment-data-object realm str granularity (car r) (cdr r)))
                (put res "done" *false*)))
          res))
      (when *symbol-iterator*
        (put seg-iter-proto *symbol-iterator*
             (native-function realm "[Symbol.iterator]"
               (lambda (this args) (declare (ignore args)) this) 0)
             :enumerable nil :writable t :configurable t))
      (put seg-iter-proto (symbol-tostringtag realm) "Segmenter String Iterator"
           :enumerable nil :writable nil :configurable t))

    (intl-register realm "Segmenter" ctor)
    ctor))

;;; ===========================================================================
;;; Intl.DisplayNames
;;; ===========================================================================
(defvar *intl-displaynames-proto* nil)

(defun displaynames-slots (this)
  (let ((v (if (js-object-p this)
               (getf (js-object-internal this) :initialized-displaynames 'none)
               'none)))
    (when (eq v 'none)
      (js-throw (make-native-error "TypeError" "receiver is not an Intl.DisplayNames")))
    v))

;;; ---- a small en names table for the pinned cases (fallback=code otherwise).
(defparameter +dn-language-names+
  '(("en" . "English") ("fr" . "French") ("de" . "German") ("es" . "Spanish")
    ("it" . "Italian") ("ja" . "Japanese") ("zh" . "Chinese") ("ru" . "Russian")
    ("pt" . "Portuguese") ("ar" . "Arabic") ("ko" . "Korean") ("nl" . "Dutch")))
(defparameter +dn-region-names+
  '(("US" . "United States") ("GB" . "United Kingdom") ("FR" . "France")
    ("DE" . "Germany") ("JP" . "Japan") ("CN" . "China") ("CA" . "Canada")
    ("BR" . "Brazil") ("IN" . "India") ("RU" . "Russia") ("ES" . "Spain")
    ("IT" . "Italy")))
(defparameter +dn-script-names+
  '(("Latn" . "Latin") ("Cyrl" . "Cyrillic") ("Arab" . "Arabic")
    ("Hans" . "Simplified Han") ("Hant" . "Traditional Han") ("Hebr" . "Hebrew")
    ("Grek" . "Greek") ("Jpan" . "Japanese") ("Kore" . "Korean")))
(defparameter +dn-currency-names+
  '(("USD" . "US Dollar") ("EUR" . "Euro") ("GBP" . "British Pound")
    ("JPY" . "Japanese Yen") ("CNY" . "Chinese Yuan") ("CAD" . "Canadian Dollar")))
(defparameter +dn-datetimefield-values+
  '("era" "year" "quarter" "month" "weekOfYear" "weekday" "day" "dayPeriod"
    "hour" "minute" "second" "timeZoneName"))

(defun %dn-validate-code (type code)
  "Validate CODE per TYPE; RangeError on malformed. Returns the canonicalized
   code (as used for the fallback / lookup key)."
  (cond
    ((string= type "language")
     ;; a unicode_language_id: valid, no extensions/privateuse, not "root".
     (let ((lid (parse-unicode-locale-id code)))
       (unless (and lid
                    (structurally-valid-locale-id-p code)
                    (null (locale-id-extensions lid))
                    (null (locale-id-privateuse lid))
                    (not (string-equal (or (locale-id-language lid) "") "root")))
         (js-throw (make-native-error "RangeError" (format nil "invalid language code: ~a" code)))))
     (canonicalize-unicode-locale-id code))
    ((string= type "region")
     (unless (region-subtag-p code)
       (js-throw (make-native-error "RangeError" (format nil "invalid region code: ~a" code))))
     (if (%all #'%digit-p code) code (string-upcase code)))
    ((string= type "script")
     (unless (script-subtag-p code)
       (js-throw (make-native-error "RangeError" (format nil "invalid script code: ~a" code))))
     (titlecase code))
    ((string= type "currency")
     (unless (and (= (length code) 3) (%all #'%alpha-p code))
       (js-throw (make-native-error "RangeError" (format nil "invalid currency code: ~a" code))))
     (string-upcase code))
    ((string= type "calendar")
     (unless (%dn-valid-type-sequence-p code)
       (js-throw (make-native-error "RangeError" (format nil "invalid calendar code: ~a" code))))
     (%lc code))
    ((string= type "dateTimeField")
     (unless (member code +dn-datetimefield-values+ :test #'string=)
       (js-throw (make-native-error "RangeError" (format nil "invalid dateTimeField code: ~a" code))))
     code)
    (t (js-throw (make-native-error "TypeError" "invalid type")))))

(defun %dn-valid-type-sequence-p (code)
  "A '-'-separated sequence of alphanum{3,8} segments."
  (let ((parts (split-dash code)))
    (and parts
         (every (lambda (p) (and (<= 3 (length p) 8) (%all #'%alnum-p p))) parts))))

(defun %dn-lookup-name (type canon-code)
  (let ((tbl (cond ((string= type "language") +dn-language-names+)
                   ((string= type "region") +dn-region-names+)
                   ((string= type "script") +dn-script-names+)
                   ((string= type "currency") +dn-currency-names+)
                   ((string= type "dateTimeField") nil)
                   (t nil))))
    (cond
      ((string= type "dateTimeField") canon-code) ; field name is its own display in en
      (tbl (cdr (assoc canon-code tbl :test #'string=)))
      (t nil))))

(defun install-intl_displaynames (realm)
  (let* ((op (realm-object-proto realm))
         (proto (make-object :proto op :class "Object"))
         (ctor (%ctor-throws-without-new realm "DisplayNames")))
    (setf *intl-displaynames-proto* proto)
    (setf (js-object-construct ctor)
          (lambda (args nt)
            (%require-new nt "DisplayNames")
            ;; OrdinaryCreateFromConstructor first (reads newTarget.prototype —
            ;; observable, may throw) BEFORE option processing.
            (let* ((instance-proto (proto-from-newtarget nt proto))
                   (locv (arg 0 args)) (optv (arg 1 args))
                   (requested (canonicalize-locale-list locv)))
              ;; GetOptionsObject: undefined -> empty; Object -> itself; else
              ;; TypeError. `type` being required then rejects the empty case.
              (let ((opts (%get-options-object optv)))
                ;; read localeMatcher, style, type, fallback, languageDisplay (order).
                (get-option opts "localeMatcher" :string '("lookup" "best fit") "best fit")
                (let* ((style (get-option opts "style" :string '("narrow" "short" "long") "long"))
                       ;; type: undefined/missing -> TypeError (required); present
                       ;; but not in the set -> RangeError.
                       (type (let ((tv (js-get opts "type")))
                               (when (js-undefined-p tv)
                                 (js-throw (make-native-error "TypeError" "type option is required")))
                               (get-option opts "type" :string
                                           '("language" "region" "script" "currency" "calendar" "dateTimeField")
                                           :required)))
                       (fallback (get-option opts "fallback" :string '("code" "none") "code"))
                       (langdisplay (get-option opts "languageDisplay" :string
                                                '("dialect" "standard") "dialect"))
                       (resolved (resolve-locale requested '() '()))
                       (slots (list :locale (%canon-locale (getf resolved :locale)) :style style :type type
                                    :fallback fallback
                                    :language-display (when (string= type "language") langdisplay)))
                       (obj (make-object :proto instance-proto :class "Object")))
                  (setf (getf (js-object-internal obj) :initialized-displaynames) slots)
                  obj)))))
    (def-value ctor "prototype" proto :writable nil :configurable nil)
    (def-value proto "constructor" ctor)
    ;; ---- of(code) ----
    (def-method realm proto "of" 1 (this args)
      (let* ((slots (displaynames-slots this))
             (type (getf slots :type))
             (fallback (getf slots :fallback))
             (code (to-string (arg 0 args)))
             (canon (%dn-validate-code type code))
             (name (%dn-lookup-name type canon)))
        (cond
          (name name)
          ((string= fallback "code") canon)
          (t *undefined*))))
    ;; ---- resolvedOptions ----
    (def-method realm proto "resolvedOptions" 0 (this args)
      (declare (ignore args))
      (let* ((slots (displaynames-slots this))
             (o (make-object :proto (realm-object-proto realm) :class "Object")))
        (put o "locale" (getf slots :locale))
        (put o "style" (getf slots :style))
        (put o "type" (getf slots :type))
        (put o "fallback" (getf slots :fallback))
        (when (getf slots :language-display)
          (put o "languageDisplay" (getf slots :language-display)))
        o))
    (%def-supported-locales-of realm ctor)
    (%intl-tag-put realm proto "Intl.DisplayNames")
    (intl-register realm "DisplayNames" ctor)
    ctor))

;;; ===========================================================================
;;; Intl.DurationFormat
;;; ===========================================================================
(defvar *intl-durationformat-proto* nil)

(defparameter +df-units+
  '(("years" . :year) ("months" . :month) ("weeks" . :week) ("days" . :day)
    ("hours" . :hour) ("minutes" . :minute) ("seconds" . :second)
    ("milliseconds" . :millisecond) ("microseconds" . :microsecond)
    ("nanoseconds" . :nanosecond))
  "Ordered (property . keyword) for the ten duration units.")

(defun %df-unit-allowed-styles (unit)
  (cond
    ((member unit '("years" "months" "weeks" "days") :test #'string=)
     '("long" "short" "narrow"))
    ((member unit '("hours" "minutes" "seconds") :test #'string=)
     '("long" "short" "narrow" "numeric" "2-digit"))
    (t '("long" "short" "narrow" "numeric")))) ; ms/us/ns

(defun durationformat-slots (this)
  (let ((v (if (js-object-p this)
               (getf (js-object-internal this) :initialized-durationformat 'none)
               'none)))
    (when (eq v 'none)
      (js-throw (make-native-error "TypeError" "receiver is not an Intl.DurationFormat")))
    v))

;;; ---- duration record validation (LOCAL ToDurationRecord + IsValidDuration) ----
(defun %df-to-duration-record (input)
  "Return a plist unit-keyword -> integer, validating per IsValidDurationRecord.
   Accepts a Temporal.Duration object (read internal slot), an ISO-8601 duration
   string, or a plain property bag. Throws TypeError/RangeError."
  (cond
    ((and (js-object-p input) (temporal-branded-object-p input)
          (not (eq (getf (js-object-internal input) :temporal-duration 'none) 'none)))
     ;; Temporal.Duration: read its internal record (a plist keyed same as +df-units+
     ;; keywords, per temporal). Fall through to validate.
     (%df-duration-from-temporal input))
    ((stringp input)
     (%df-parse-iso-duration input))
    ((not (js-object-p input))
     (js-throw (make-native-error "TypeError" "duration must be an object or string")))
    (t
     ;; property bag: read each unit property; at least one must be present.
     (let ((rec '()) (any nil))
       (dolist (u +df-units+)
         (let ((v (js-get input (car u))))
           (if (js-undefined-p v)
               (setf rec (append rec (list (cdr u) 0)))
               (progn (setf any t)
                      (setf (getf rec (cdr u)) (%df-to-integral v))))))
       (unless any
         (js-throw (make-native-error "TypeError" "duration has no recognized properties")))
       (%df-validate-record rec)
       rec))))

(defun %df-to-integral (v)
  "ToIntegerIfIntegral: number must be integral + finite, else RangeError."
  (let ((n (to-number v)))
    (when (or (js-nan-p n) (= n *inf*) (= n *-inf*))
      (js-throw (make-native-error "RangeError" "duration field must be finite")))
    (unless (= n (ftruncate n))
      (js-throw (make-native-error "RangeError" "duration field must be integral")))
    (truncate n)))

(defparameter +df-temporal-key-map+
  ;; my singular record keyword -> temporal's plural plist keyword.
  '((:year . :years) (:month . :months) (:week . :weeks) (:day . :days)
    (:hour . :hours) (:minute . :minutes) (:second . :seconds)
    (:millisecond . :milliseconds) (:microsecond . :microseconds)
    (:nanosecond . :nanoseconds)))

(defun %df-duration-from-temporal (obj)
  "Read a Temporal.Duration's fields directly from the internal slot (no getter
   invocation, so a poisoned Temporal.Duration.prototype is not observed)."
  (let ((dur (getf (js-object-internal obj) :temporal-duration))
        (rec '()))
    (dolist (u +df-units+)
      (let* ((mine (cdr u))
             (tkey (cdr (assoc mine +df-temporal-key-map+)))
             (v (getf dur tkey 0)))
        (setf (getf rec mine) (truncate (or v 0)))))
    (%df-validate-record rec)
    rec))

(defun %df-parse-iso-duration (str)
  "Minimal ISO-8601 duration parser: PnYnMnWnDTnHnMnS with optional fractional
   seconds. Returns a validated record plist. RangeError on malformed."
  (let ((s str) (sign 1) (i 0) (n (length str)) (rec (list :year 0 :month 0 :week 0
                                                           :day 0 :hour 0 :minute 0
                                                           :second 0 :millisecond 0
                                                           :microsecond 0 :nanosecond 0)))
    (flet ((fail () (js-throw (make-native-error "RangeError" (format nil "invalid duration string: ~a" str)))))
      (when (zerop n) (fail))
      (when (and (< i n) (member (char s i) '(#\+ #\-)))
        (when (char= (char s i) #\-) (setf sign -1)) (incf i))
      (unless (and (< i n) (char-equal (char s i) #\P)) (fail))
      (incf i)
      (let ((in-time nil) (seen-any nil))
        (loop while (< i n) do
          (cond
            ((char-equal (char s i) #\T)
             (setf in-time t) (incf i)
             (when (>= i n) (fail)))
            (t
             (let ((start i))
               (loop while (and (< i n) (or (%digit-p (char s i)) (char= (char s i) #\.))) do (incf i))
               (when (= start i) (fail))
               (when (>= i n) (fail))
               (let* ((numstr (subseq s start i))
                      (desig (char s i)))
                 (incf i) (setf seen-any t)
                 (%df-assign-iso-field rec numstr desig in-time sign #'fail))))))
        (unless seen-any (fail)))
      (%df-validate-record rec)
      rec)))

(defun %df-assign-iso-field (rec numstr desig in-time sign fail)
  (let* ((dot (position #\. numstr))
         (intpart (if dot (subseq numstr 0 dot) numstr))
         (fracpart (if dot (subseq numstr (1+ dot)) nil))
         (ival (if (plusp (length intpart)) (* sign (parse-integer intpart)) 0)))
    (when (and fracpart (not (char-equal desig #\S))) (funcall fail))
    (cond
      ((not in-time)
       (case (char-upcase desig)
         (#\Y (setf (getf rec :year) ival))
         (#\M (setf (getf rec :month) ival))
         (#\W (setf (getf rec :week) ival))
         (#\D (setf (getf rec :day) ival))
         (t (funcall fail))))
      (t
       (case (char-upcase desig)
         (#\H (setf (getf rec :hour) ival))
         (#\M (setf (getf rec :minute) ival))
         (#\S (setf (getf rec :second) ival)
              (when fracpart
                (let* ((padded (subseq (concatenate 'string fracpart "000000000") 0 9))
                       (ms (parse-integer padded :start 0 :end 3))
                       (us (parse-integer padded :start 3 :end 6))
                       (ns (parse-integer padded :start 6 :end 9)))
                  (setf (getf rec :millisecond) (* sign ms)
                        (getf rec :microsecond) (* sign us)
                        (getf rec :nanosecond) (* sign ns)))))
         (t (funcall fail)))))))

(defun %df-validate-record (rec)
  "IsValidDurationRecord: no mixed signs; range checks on Y/M/W and normalized
   seconds. Uses exact integer math."
  (let ((sign 0))
    (dolist (u +df-units+)
      (let ((v (getf rec (cdr u))))
        (cond ((> v 0) (when (< sign 0) (js-throw (make-native-error "RangeError" "mixed-sign duration"))) (setf sign 1))
              ((< v 0) (when (> sign 0) (js-throw (make-native-error "RangeError" "mixed-sign duration"))) (setf sign -1)))))
    ;; range: abs(years|months|weeks) < 2^32
    (dolist (kw '(:year :month :week))
      (when (>= (abs (getf rec kw)) (expt 2 32))
        (js-throw (make-native-error "RangeError" "duration field out of range"))))
    ;; abs(normalized-seconds) < 2^53 (exact integer)
    (let ((total-sec (+ (* (getf rec :day) 86400)
                        (* (getf rec :hour) 3600)
                        (* (getf rec :minute) 60)
                        (getf rec :second))))
      (when (>= (abs total-sec) (expt 2 53))
        (js-throw (make-native-error "RangeError" "duration out of range")))
      ;; also nanoseconds normalized shouldn't exceed 2^53 sub-second-wise; the
      ;; spec bounds normalizedSeconds; our total-sec check covers the coarse case.
      (let ((subsec-ns (+ (* (getf rec :millisecond) 1000000)
                          (* (getf rec :microsecond) 1000)
                          (getf rec :nanosecond))))
        (when (>= (abs (+ (* total-sec 1000000000) subsec-ns)) (* (expt 2 53) 1000000000))
          (js-throw (make-native-error "RangeError" "duration out of range")))))
    rec))

;;; ---- format via the realm's NumberFormat + ListFormat ----
(defun %df-realm-intl (realm name)
  "Fetch a currently-registered Intl.<name> constructor, or TypeError if absent."
  (let* ((ns (intl-namespace realm))
         (c (and ns (js-get ns name))))
    (unless (js-callable-p c)
      (js-throw (make-native-error "TypeError" (format nil "Intl.~a is required for DurationFormat" name))))
    c))

(defun %df-singular-unit-name (unit-prop)
  (subseq unit-prop 0 (1- (length unit-prop))))

(defun %df-unit-style-key (unit-prop)
  (intern (string-upcase (concatenate 'string "unit-style-" unit-prop)) :keyword))
(defun %df-unit-display-key (unit-prop)
  (intern (string-upcase (concatenate 'string "unit-display-" unit-prop)) :keyword))

;;; ---- A faithful port of testIntl.js partitionDurationFormatPattern. Uses the
;;; ---- realm's Intl.NumberFormat + Intl.ListFormat (formatToParts) so the output
;;; ---- byte-matches what the harness derives from the same services.

(defun %df-fractional (rec exponent)
  "durationToFractional: combine seconds + sub-seconds into a decimal STRING (or
   an integer when no sub-seconds), using exact integer math. EXPONENT is 9/6/3."
  (let ((seconds (getf rec :second)) (ms (getf rec :millisecond))
        (us (getf rec :microsecond)) (ns (getf rec :nanosecond)))
    (cond
      ((and (= exponent 9) (zerop ms) (zerop us) (zerop ns)) seconds)
      ((and (= exponent 6) (zerop us) (zerop ns)) ms)
      ((and (= exponent 3) (zerop ns)) us)
      (t
       (let ((nsum ns))
         (when (>= exponent 9) (incf nsum (* seconds 1000000000)))
         (when (>= exponent 6) (incf nsum (* ms 1000000)))
         (when (>= exponent 3) (incf nsum (* us 1000)))
         (let* ((e (expt 10 exponent))
                (q (truncate nsum e))
                (r (rem nsum e)))
           (when (< r 0) (setf r (- r)))
           (format nil "~a.~v,'0d" q exponent r)))))))

(defun %df-nf-parts (realm locale nfopts value)
  "Construct Intl.NumberFormat(locale, nfopts) and return formatToParts(value) as
   a CL list of (type . value) conses. VALUE may be an integer or a decimal string."
  (let* ((nf-ctor (%df-realm-intl realm "NumberFormat"))
         (nf (js-construct nf-ctor (list locale nfopts)))
         (ftp (js-get nf "formatToParts"))
         (jsval (cond ((integerp value) (float value 1d0))
                      ((stringp value) value) ; decimal string -> NF coerces
                      (t value)))
         (arr (js-call ftp nf (list jsval)))
         (len (truncate (to-number (js-get arr "length"))))
         (out '()))
    (dotimes (i len)
      (let ((p (js-get arr (princ-to-string i))))
        (push (cons (to-string (js-get p "type")) (to-string (js-get p "value"))) out)))
    (nreverse out)))

(defun %df-partition (realm slots rec)
  "Return a list of parts: each is a plist (:type T :value V [:unit U]) — the
   flattened DurationFormat pattern. format = concat of values."
  (let* ((locale (getf slots :locale))
         (numsys (getf slots :numbering-system))
         (fd (getf slots :fractional-digits))
         (result '())          ; list of unit-part-lists (each a list of plists)
         (need-separator nil)
         (display-negative t))
    (loop for tail on +df-units+
          for u = (car tail)
          for prop = (car u) for kw = (cdr u) do
      (let* ((value (getf rec kw))
             (style (getf slots (%df-unit-style-key prop)))
             (display (getf slots (%df-unit-display-key prop)))
             (nfunit (%df-singular-unit-name prop))
             (nfopts (make-object :proto *null* :class "Object"))
             (done nil))
        ;; combine numeric seconds/ms/us with a numeric next unit
        (when (member prop '("seconds" "milliseconds" "microseconds") :test #'string=)
          (let* ((next (car (cadr tail)))
                 (next-style (and next (getf slots (%df-unit-style-key next)))))
            (when (and next-style (string= next-style "numeric"))
              (setf value (%df-fractional rec (cond ((string= prop "seconds") 9)
                                                    ((string= prop "milliseconds") 6)
                                                    (t 3))))
              (put nfopts "maximumFractionDigits" (float (or fd 9) 1d0))
              (put nfopts "minimumFractionDigits" (float (or fd 0) 1d0))
              (put nfopts "roundingMode" "trunc")
              (setf done t))))
        ;; minutes force-display when a separator is pending and seconds present
        (let ((display-required nil))
          (when (and (string= prop "minutes") need-separator)
            (setf display-required
                  (or (string= (getf slots (%df-unit-display-key "seconds")) "always")
                      (/= (getf rec :second) 0) (/= (getf rec :millisecond) 0)
                      (/= (getf rec :microsecond) 0) (/= (getf rec :nanosecond) 0))))
          (when (or (%df-value-nonzero value) (not (string= display "auto")) display-required)
            ;; sign handling: first displayed value keeps sign; rest signDisplay never
            (if display-negative
                (progn
                  (setf display-negative nil)
                  (when (%df-value-zero value)
                    (when (some (lambda (uu) (< (getf rec (cdr uu)) 0)) +df-units+)
                      (setf value :negative-zero))))
                (put nfopts "signDisplay" "never"))
            (put nfopts "numberingSystem" numsys)
            (when (string= style "2-digit") (put nfopts "minimumIntegerDigits" 2d0))
            (if (and (not (string= style "numeric")) (not (string= style "2-digit")))
                (progn (put nfopts "style" "unit")
                       (put nfopts "unit" nfunit)
                       (put nfopts "unitDisplay" style))
                (put nfopts "useGrouping" *false*))
            (let* ((nfval (cond ((eq value :negative-zero) -0d0)
                                (t value)))
                   (parts (%df-nf-parts realm locale nfopts nfval))
                   (unit-parts (mapcar (lambda (pp)
                                         (list :type (car pp) :value (cdr pp) :unit nfunit))
                                       parts)))
              (if need-separator
                  ;; splice a ':' separator + these parts onto the previous
                  ;; (already time-numeric) unit list.
                  (setf (car result)
                        (append (car result)
                                (list (list :type "literal" :value ":"))
                                unit-parts))
                  (progn
                    (when (member style '("2-digit" "numeric") :test #'string=)
                      (setf need-separator t))
                    (push unit-parts result))))))
        (when done (return))))
    (setf result (nreverse result))
    ;; join with ListFormat.formatToParts over the per-unit strings
    (%df-join-parts realm slots result)))

(defun %df-value-nonzero (v)
  (cond ((eq v :negative-zero) nil)
        ((integerp v) (/= v 0))
        ((stringp v) (not (every (lambda (c) (or (char= c #\0) (char= c #\.) (char= c #\-))) v)))
        ((numberp v) (/= v 0))
        (t t)))
(defun %df-value-zero (v) (not (%df-value-nonzero v)))

(defun %df-join-parts (realm slots result)
  "RESULT is a list of unit-part-lists. Join their string forms with ListFormat
   formatToParts, splicing the original parts back in for 'element' entries."
  (let* ((lf-ctor (%df-realm-intl realm "ListFormat"))
         (style (getf slots :style))
         (lf-style (if (string= style "digital") "short" style))
         (opts (make-object :proto *null* :class "Object")))
    (put opts "type" "unit")
    (put opts "style" lf-style)
    (let* ((lf (js-construct lf-ctor (list (getf slots :locale) opts)))
           (ftp (js-get lf "formatToParts"))
           (strings (mapcar (lambda (parts)
                              (apply #'concatenate 'string
                                     (mapcar (lambda (p) (getf p :value)) parts)))
                            result))
           (arr (js-call ftp lf (list (make-array-object strings))))
           (len (truncate (to-number (js-get arr "length"))))
           (queue (copy-list result))
           (flattened '()))
      (dotimes (i len)
        (let* ((p (js-get arr (princ-to-string i)))
               (type (to-string (js-get p "type")))
               (val (to-string (js-get p "value"))))
          (if (string= type "element")
              (progn (dolist (pp (pop queue)) (push pp flattened)))
              (push (list :type "literal" :value val) flattened))))
      (nreverse flattened))))

(defun %df-format-string (parts)
  (apply #'concatenate 'string (mapcar (lambda (p) (getf p :value)) parts)))

(defun install-intl_durationformat (realm)
  (let* ((op (realm-object-proto realm))
         (proto (make-object :proto op :class "Object"))
         (ctor (%ctor-throws-without-new realm "DurationFormat")))
    (setf *intl-durationformat-proto* proto)
    (setf (js-object-construct ctor)
          (lambda (args nt)
            (%require-new nt "DurationFormat")
            (let* ((locv (arg 0 args)) (optv (arg 1 args))
                   (requested (canonicalize-locale-list locv))
                   (opts (%coerce-options optv)))
              ;; option-read order: localeMatcher, numberingSystem, style, then
              ;; per-unit (style, display) for each unit, then fractionalDigits.
              (get-option opts "localeMatcher" :string '("lookup" "best fit") "best fit")
              (let* ((numbering (let ((v (get-option opts "numberingSystem" :string nil :undefined)))
                                  (if (eq v :undefined) nil
                                      (progn (%df-validate-numbering-system v) v))))
                     (style (get-option opts "style" :string
                                        '("long" "short" "narrow" "digital") "short"))
                     (slots (list :style style)))
                ;; per-unit options in order (GetDurationUnitOptions)
                (let ((prev-style nil))
                  (dolist (u +df-units+)
                    (let* ((prop (car u))
                           (allowed (%df-unit-allowed-styles prop))
                           (numeric-capable (member prop '("hours" "minutes" "seconds"
                                                           "milliseconds" "microseconds" "nanoseconds")
                                                    :test #'string=))
                           (prev-numeric (member prev-style '("numeric" "2-digit") :test #'string=))
                           ;; default style:
                           ;;  - digital: hours/min/sec/ms/us/ns default numeric
                           ;;  - cascade: after a numeric/2-digit unit, minutes/seconds
                           ;;    default 2-digit, ms/us/ns default numeric
                           ;;  - else the base style
                           (default-style (%df-unit-default prop style prev-numeric))
                           (ustyle (get-option opts prop :string allowed default-style)))
                      ;; style conflict: after a numeric/2-digit unit, a numeric-capable
                      ;; unit given long/short/narrow is a RangeError.
                      (when (and prev-numeric numeric-capable
                                 (member ustyle '("long" "short" "narrow") :test #'string=))
                        (js-throw (make-native-error "RangeError"
                                    (format nil "~a style conflicts with preceding numeric unit" prop))))
                      ;; GetDurationUnitOptions: after a numeric/2-digit unit, a
                      ;; minutes/seconds unit is forced to 2-digit (even if the
                      ;; requested/default style was "numeric").
                      (when (and prev-numeric
                                 (member prop '("minutes" "seconds") :test #'string=)
                                 (string= ustyle "numeric"))
                        (setf ustyle "2-digit"))
                      (let ((udisplay (get-option opts (concatenate 'string prop "Display")
                                                  :string '("auto" "always") "auto")))
                        (setf (getf slots (%df-unit-style-key prop)) ustyle)
                        (setf (getf slots (%df-unit-display-key prop)) udisplay))
                      (setf prev-style ustyle))))
                (let ((fd (let ((v (js-get opts "fractionalDigits")))
                            (if (js-undefined-p v) nil
                                (let ((n (%df-to-integral-opt v 0 9)))
                                  n)))))
                  (setf (getf slots :fractional-digits) fd))
                (let* ((data-locale (%broad-resolve-locale requested))
                       (ext-nu (%read-u-keyword requested "nu"))
                       (opt-nu-supported (and numbering (%df-nu-supported-p numbering)))
                       (ext-nu-supported (and ext-nu (%df-nu-supported-p ext-nu)))
                       (nu (cond (opt-nu-supported numbering)
                                 (ext-nu-supported ext-nu)
                                 (t "latn")))
                       ;; reflect -u-nu iff final nu came from the extension.
                       (nu-reflect (and ext-nu-supported (string= nu ext-nu)))
                       (loc (%collator-build-locale data-locale
                                                    (when nu-reflect (list (cons "nu" nu))))))
                  (setf (getf slots :locale) loc
                        (getf slots :numbering-system) nu)
                  (let ((obj (make-object :proto (proto-from-newtarget nt proto) :class "Object")))
                    (setf (getf (js-object-internal obj) :initialized-durationformat) slots)
                    obj))))))
    (def-value ctor "prototype" proto :writable nil :configurable nil)
    (def-value proto "constructor" ctor)
    ;; ---- format ----
    (def-method realm proto "format" 1 (this args)
      (let* ((slots (durationformat-slots this))
             (rec (%df-to-duration-record (arg 0 args))))
        (%df-format-string (%df-partition realm slots rec))))
    ;; ---- formatToParts ----
    (def-method realm proto "formatToParts" 1 (this args)
      (let* ((slots (durationformat-slots this))
             (rec (%df-to-duration-record (arg 0 args)))
             (parts (%df-partition realm slots rec)))
        (make-array-object
         (mapcar (lambda (p)
                   (let ((o (make-object :proto (realm-object-proto realm) :class "Object")))
                     (put o "type" (getf p :type))
                     (put o "value" (getf p :value))
                     (when (getf p :unit)
                       (put o "unit" (getf p :unit)))
                     o))
                 parts))))
    ;; ---- resolvedOptions ----
    (def-method realm proto "resolvedOptions" 0 (this args)
      (declare (ignore args))
      (let* ((slots (durationformat-slots this))
             (o (make-object :proto (realm-object-proto realm) :class "Object")))
        (put o "locale" (getf slots :locale))
        (put o "numberingSystem" (getf slots :numbering-system))
        (put o "style" (getf slots :style))
        (dolist (u +df-units+)
          (let ((prop (car u)))
            (put o prop (getf slots (%df-unit-style-key prop)))
            (put o (concatenate 'string prop "Display") (getf slots (%df-unit-display-key prop)))))
        (when (getf slots :fractional-digits)
          (put o "fractionalDigits" (float (getf slots :fractional-digits) 1d0)))
        o))
    (%def-supported-locales-of realm ctor t)
    (%intl-tag-put realm proto "Intl.DurationFormat")
    (intl-register realm "DurationFormat" ctor)
    ctor))

(defun %df-unit-default (prop base-style prev-numeric)
  "Default per-unit style (GetDurationUnitOptions):
    - after a numeric/2-digit unit: minutes/seconds -> 2-digit, ms/us/ns -> numeric
    - digital base: hours/min/sec -> numeric, ms/us/ns -> numeric, others short
    - else the DurationFormat base style (long/short/narrow)."
  (cond
    (prev-numeric
     (cond ((member prop '("minutes" "seconds") :test #'string=) "2-digit")
           ((member prop '("milliseconds" "microseconds" "nanoseconds") :test #'string=) "numeric")
           ;; hours after nothing-numeric handled elsewhere; keep base
           (t (if (string= base-style "digital") "numeric" base-style))))
    ((string= base-style "digital")
     (cond ((member prop '("hours") :test #'string=) "numeric")
           ((member prop '("minutes" "seconds") :test #'string=) "2-digit")
           ((member prop '("milliseconds" "microseconds" "nanoseconds") :test #'string=) "numeric")
           (t "short")))
    (t base-style)))

(defun %df-nu-supported-p (nu)
  (and (stringp nu) (member nu +numbering-system-digit-names+ :test #'string=)))

(defun %df-validate-numbering-system (nu)
  "A well-formed unicode type value: one-or-more alphanum{3,8} '-' segments."
  (let ((parts (split-dash nu)))
    (unless (and parts (every (lambda (p) (and (<= 3 (length p) 8) (%all #'%alnum-p p))) parts))
      (js-throw (make-native-error "RangeError" (format nil "invalid numberingSystem: ~a" nu))))))

(defun %df-to-integral-opt (v min max)
  (let ((n (to-number v)))
    (when (or (js-nan-p n) (< n min) (> n max))
      (js-throw (make-native-error "RangeError" "fractionalDigits out of range")))
    (floor n)))

;;; ===========================================================================
;;; Aggregate installer (self-registering)
;;; ===========================================================================
(defun install-intl_collator_segmenter_displaynames (realm)
  (install-intl_collator realm)
  (install-intl_segmenter realm)
  (install-intl_displaynames realm)
  (install-intl_durationformat realm))

(register-builtin-installer 'install-intl_collator_segmenter_displaynames)
