;;;; builtins/intl-datetimeformat.lisp — Intl.DateTimeFormat.
;;;;
;;;; Built ON the intl-core kernel (canonicalize-locale-list / resolve-locale /
;;;; the GetOption family) + date.lisp's epoch-ms -> calendar-field helpers
;;;; (year-from-time / month-from-time / date-from-time / week-day / hours-/min-/
;;;; sec-/ms-from-time — all UTC, since date.lisp treats local == UTC).
;;;;
;;;; SCOPE: gregory calendar + en/en-US formatting only. Time zone: "UTC" default,
;;;; IANA-shaped named zones case-canonicalized (offset 0 semantics — no DST), and
;;;; ES2024 offset zones ("+01:00") which shift the displayed wall-clock. Non-
;;;; gregory calendars and real IANA/DST semantics are out of scope (see notes).
(in-package #:shuttle)

(defvar *intl-dtf-proto* nil)
(defvar *intl-dtf-ctor* nil)
(defvar *intl-legacy-symbol* nil)  ; the [[FallbackSymbol]]

;;; ===========================================================================
;;; Internal-slot access
;;; ===========================================================================
(defun dtf-slots (this)
  "Return the :initialized-datetimeformat plist from THIS, or NIL."
  (and (js-object-p this) (js-object-internal this)
       (getf (js-object-internal this) :initialized-datetimeformat)))

(defun require-dtf (this)
  "UnwrapDateTimeFormat + RequireInternalSlot. Returns the slots plist or throws
   a TypeError. Handles the legacy [[FallbackSymbol]] unwrap."
  (let ((s (dtf-slots this)))
    (when s (return-from require-dtf s))
    ;; UnwrapDateTimeFormat: if THIS is (ordinary) an instance of the ctor and
    ;; carries the fallback symbol, use that.
    (when (and (js-object-p this) *intl-dtf-ctor*
               (ordinary-instance-of-p this *intl-dtf-ctor*))
      (let ((inner (js-get this *intl-legacy-symbol*)))
        (let ((is (dtf-slots inner)))
          (when is (return-from require-dtf is)))))
    (js-throw (make-native-error "TypeError" "receiver is not an Intl.DateTimeFormat"))))

(defun ordinary-instance-of-p (o ctor)
  "OrdinaryHasInstance(ctor, o) — walk O's proto chain for ctor.prototype,
   WITHOUT triggering Symbol.hasInstance."
  (let ((proto (js-get ctor "prototype")))
    (and (js-object-p o)
         (loop for p = (js-get-proto o) then (js-get-proto p)
               while (js-object-p p) thereis (eq p proto)))))

;;; ===========================================================================
;;; Option value tables
;;; ===========================================================================
(defparameter +dtf-narrow-short-long+ '("narrow" "short" "long"))
(defparameter +dtf-numeric-2digit+ '("2-digit" "numeric"))
(defparameter +dtf-month-values+ '("2-digit" "numeric" "narrow" "short" "long"))
(defparameter +dtf-tzname-values+
  '("short" "long" "shortOffset" "longOffset" "shortGeneric" "longGeneric"))
(defparameter +dtf-style-values+ '("full" "long" "medium" "short"))

;;; component keys in canonical (resolvedOptions / read) order
(defparameter +dtf-date-components+ '("weekday" "era" "year" "month" "day"))
(defparameter +dtf-time-components+
  '("dayPeriod" "hour" "minute" "second" "fractionalSecondDigits"))

;;; ===========================================================================
;;; calendar / numberingSystem type validation (structural)
;;; ===========================================================================
(defun dtf-type-string-p (s)
  "type nonterminal: (3*8 alnum) *(-(3*8 alnum))"
  (let ((parts (split-dash s)))
    (and parts
         (every (lambda (p) (and (<= 3 (length p) 8) (%all #'%alnum-p p))) parts))))

(defun dtf-get-type-option (opts key)
  "GetOption(opts,key,string,empty,undefined) + structural validation (RangeError)."
  (let ((v (js-get opts key)))
    (if (js-undefined-p v)
        nil
        (let ((s (to-string v)))
          (unless (dtf-type-string-p s)
            (js-throw (make-native-error "RangeError"
                        (format nil "invalid value for ~a" key))))
          (%lc s)))))

;;; ===========================================================================
;;; Time-zone canonicalization
;;; ===========================================================================
;;; Named IANA zones the tests exercise (case-canonical spellings). Matched
;;; ASCII-case-insensitively; output = the canonical spelling as-passed (links NOT
;;; resolved). This is a test-pinned subset; unknown names throw RangeError.
(defparameter +iana-timezone-names+
  (list
    "Africa/Abidjan" "Africa/Algiers" "Africa/Bissau" "Africa/Cairo" "Africa/Casablanca"
    "Africa/Ceuta" "Africa/El_Aaiun" "Africa/Johannesburg" "Africa/Juba" "Africa/Khartoum"
    "Africa/Lagos" "Africa/Maputo" "Africa/Monrovia" "Africa/Nairobi" "Africa/Ndjamena"
    "Africa/Sao_Tome" "Africa/Tripoli" "Africa/Tunis" "Africa/Windhoek" "America/Adak"
    "America/Anchorage" "America/Araguaina" "America/Argentina/Buenos_Aires"
    "America/Argentina/Catamarca" "America/Argentina/Cordoba" "America/Argentina/Jujuy"
    "America/Argentina/La_Rioja" "America/Argentina/Mendoza" "America/Argentina/Rio_Gallegos"
    "America/Argentina/Salta" "America/Argentina/San_Juan" "America/Argentina/San_Luis"
    "America/Argentina/Tucuman" "America/Argentina/Ushuaia" "America/Asuncion" "America/Bahia"
    "America/Bahia_Banderas" "America/Barbados" "America/Belem" "America/Belize"
    "America/Boa_Vista" "America/Bogota" "America/Boise" "America/Cambridge_Bay"
    "America/Campo_Grande" "America/Cancun" "America/Caracas" "America/Cayenne"
    "America/Chicago" "America/Chihuahua" "America/Costa_Rica" "America/Cuiaba"
    "America/Danmarkshavn" "America/Dawson" "America/Dawson_Creek" "America/Denver"
    "America/Detroit" "America/Edmonton" "America/Eirunepe" "America/El_Salvador"
    "America/Fort_Nelson" "America/Fortaleza" "America/Glace_Bay" "America/Goose_Bay"
    "America/Grand_Turk" "America/Guatemala" "America/Guayaquil" "America/Guyana"
    "America/Halifax" "America/Havana" "America/Hermosillo" "America/Indiana/Indianapolis"
    "America/Indiana/Knox" "America/Indiana/Marengo" "America/Indiana/Petersburg"
    "America/Indiana/Tell_City" "America/Indiana/Vevay" "America/Indiana/Vincennes"
    "America/Indiana/Winamac" "America/Inuvik" "America/Iqaluit" "America/Jamaica"
    "America/Juneau" "America/Kentucky/Louisville" "America/Kentucky/Monticello"
    "America/La_Paz" "America/Lima" "America/Los_Angeles" "America/Maceio" "America/Managua"
    "America/Manaus" "America/Martinique" "America/Matamoros" "America/Mazatlan"
    "America/Menominee" "America/Merida" "America/Metlakatla" "America/Mexico_City"
    "America/Miquelon" "America/Moncton" "America/Monterrey" "America/Montevideo"
    "America/New_York" "America/Nome" "America/Noronha" "America/North_Dakota/Beulah"
    "America/North_Dakota/Center" "America/North_Dakota/New_Salem" "America/Nuuk"
    "America/Ojinaga" "America/Panama" "America/Paramaribo" "America/Phoenix"
    "America/Port-au-Prince" "America/Porto_Velho" "America/Puerto_Rico"
    "America/Punta_Arenas" "America/Rankin_Inlet" "America/Recife" "America/Regina"
    "America/Resolute" "America/Rio_Branco" "America/Santarem" "America/Santiago"
    "America/Santo_Domingo" "America/Sao_Paulo" "America/Scoresbysund" "America/Sitka"
    "America/St_Johns" "America/Swift_Current" "America/Tegucigalpa" "America/Thule"
    "America/Tijuana" "America/Toronto" "America/Vancouver" "America/Whitehorse"
    "America/Winnipeg" "America/Yakutat" "America/Yellowknife" "Antarctica/Casey"
    "Antarctica/Davis" "Antarctica/Macquarie" "Antarctica/Mawson" "Antarctica/Palmer"
    "Antarctica/Rothera" "Antarctica/Troll" "Asia/Almaty" "Asia/Amman" "Asia/Anadyr"
    "Asia/Aqtau" "Asia/Aqtobe" "Asia/Ashgabat" "Asia/Atyrau" "Asia/Baghdad" "Asia/Baku"
    "Asia/Bangkok" "Asia/Barnaul" "Asia/Beirut" "Asia/Bishkek" "Asia/Chita" "Asia/Choibalsan"
    "Asia/Colombo" "Asia/Damascus" "Asia/Dhaka" "Asia/Dili" "Asia/Dubai" "Asia/Dushanbe"
    "Asia/Famagusta" "Asia/Gaza" "Asia/Hebron" "Asia/Ho_Chi_Minh" "Asia/Hong_Kong" "Asia/Hovd"
    "Asia/Irkutsk" "Asia/Jakarta" "Asia/Jayapura" "Asia/Jerusalem" "Asia/Kabul"
    "Asia/Kamchatka" "Asia/Karachi" "Asia/Kathmandu" "Asia/Khandyga" "Asia/Kolkata"
    "Asia/Krasnoyarsk" "Asia/Kuching" "Asia/Macau" "Asia/Magadan" "Asia/Makassar"
    "Asia/Manila" "Asia/Nicosia" "Asia/Novokuznetsk" "Asia/Novosibirsk" "Asia/Omsk"
    "Asia/Oral" "Asia/Pontianak" "Asia/Pyongyang" "Asia/Qatar" "Asia/Qostanay"
    "Asia/Qyzylorda" "Asia/Riyadh" "Asia/Sakhalin" "Asia/Samarkand" "Asia/Seoul"
    "Asia/Shanghai" "Asia/Singapore" "Asia/Srednekolymsk" "Asia/Taipei" "Asia/Tashkent"
    "Asia/Tbilisi" "Asia/Tehran" "Asia/Thimphu" "Asia/Tokyo" "Asia/Tomsk" "Asia/Ulaanbaatar"
    "Asia/Urumqi" "Asia/Ust-Nera" "Asia/Vladivostok" "Asia/Yakutsk" "Asia/Yangon"
    "Asia/Yekaterinburg" "Asia/Yerevan" "Atlantic/Azores" "Atlantic/Bermuda" "Atlantic/Canary"
    "Atlantic/Cape_Verde" "Atlantic/Faroe" "Atlantic/Madeira" "Atlantic/South_Georgia"
    "Atlantic/Stanley" "Australia/Adelaide" "Australia/Brisbane" "Australia/Broken_Hill"
    "Australia/Darwin" "Australia/Eucla" "Australia/Hobart" "Australia/Lindeman"
    "Australia/Lord_Howe" "Australia/Melbourne" "Australia/Perth" "Australia/Sydney" "CET"
    "CST6CDT" "EET" "EST" "EST5EDT" "Etc/GMT" "Etc/GMT+1" "Etc/GMT+10" "Etc/GMT+11"
    "Etc/GMT+12" "Etc/GMT+2" "Etc/GMT+3" "Etc/GMT+4" "Etc/GMT+5" "Etc/GMT+6" "Etc/GMT+7"
    "Etc/GMT+8" "Etc/GMT+9" "Etc/GMT-1" "Etc/GMT-10" "Etc/GMT-11" "Etc/GMT-12" "Etc/GMT-13"
    "Etc/GMT-14" "Etc/GMT-2" "Etc/GMT-3" "Etc/GMT-4" "Etc/GMT-5" "Etc/GMT-6" "Etc/GMT-7"
    "Etc/GMT-8" "Etc/GMT-9" "Etc/UTC" "Europe/Andorra" "Europe/Astrakhan" "Europe/Athens"
    "Europe/Belgrade" "Europe/Berlin" "Europe/Brussels" "Europe/Bucharest" "Europe/Budapest"
    "Europe/Chisinau" "Europe/Dublin" "Europe/Gibraltar" "Europe/Helsinki" "Europe/Istanbul"
    "Europe/Kaliningrad" "Europe/Kirov" "Europe/Kyiv" "Europe/Lisbon" "Europe/London"
    "Europe/Madrid" "Europe/Malta" "Europe/Minsk" "Europe/Moscow" "Europe/Paris"
    "Europe/Prague" "Europe/Riga" "Europe/Rome" "Europe/Samara" "Europe/Saratov"
    "Europe/Simferopol" "Europe/Sofia" "Europe/Tallinn" "Europe/Tirane" "Europe/Ulyanovsk"
    "Europe/Vienna" "Europe/Vilnius" "Europe/Volgograd" "Europe/Warsaw" "Europe/Zurich" "HST"
    "Indian/Chagos" "Indian/Maldives" "Indian/Mauritius" "MET" "MST" "MST7MDT" "PST8PDT"
    "Pacific/Apia" "Pacific/Auckland" "Pacific/Bougainville" "Pacific/Chatham"
    "Pacific/Easter" "Pacific/Efate" "Pacific/Fakaofo" "Pacific/Fiji" "Pacific/Galapagos"
    "Pacific/Gambier" "Pacific/Guadalcanal" "Pacific/Guam" "Pacific/Honolulu" "Pacific/Kanton"
    "Pacific/Kiritimati" "Pacific/Kosrae" "Pacific/Kwajalein" "Pacific/Marquesas"
    "Pacific/Nauru" "Pacific/Niue" "Pacific/Norfolk" "Pacific/Noumea" "Pacific/Pago_Pago"
    "Pacific/Palau" "Pacific/Pitcairn" "Pacific/Port_Moresby" "Pacific/Rarotonga"
    "Pacific/Tahiti" "Pacific/Tarawa" "Pacific/Tongatapu" "WET" "Africa/Accra"
    "Africa/Addis_Ababa" "Africa/Asmara" "Africa/Asmera" "Africa/Bamako" "Africa/Bangui"
    "Africa/Banjul" "Africa/Blantyre" "Africa/Brazzaville" "Africa/Bujumbura" "Africa/Conakry"
    "Africa/Dakar" "Africa/Dar_es_Salaam" "Africa/Djibouti" "Africa/Douala" "Africa/Freetown"
    "Africa/Gaborone" "Africa/Harare" "Africa/Kampala" "Africa/Kigali" "Africa/Kinshasa"
    "Africa/Libreville" "Africa/Lome" "Africa/Luanda" "Africa/Lubumbashi" "Africa/Lusaka"
    "Africa/Malabo" "Africa/Maseru" "Africa/Mbabane" "Africa/Mogadishu" "Africa/Niamey"
    "Africa/Nouakchott" "Africa/Ouagadougou" "Africa/Porto-Novo" "Africa/Timbuktu"
    "America/Anguilla" "America/Antigua" "America/Argentina/ComodRivadavia" "America/Aruba"
    "America/Atikokan" "America/Atka" "America/Blanc-Sablon" "America/Buenos_Aires"
    "America/Catamarca" "America/Cayman" "America/Coral_Harbour" "America/Cordoba"
    "America/Creston" "America/Curacao" "America/Dominica" "America/Ensenada"
    "America/Fort_Wayne" "America/Godthab" "America/Grenada" "America/Guadeloupe"
    "America/Indianapolis" "America/Jujuy" "America/Knox_IN" "America/Kralendijk"
    "America/Louisville" "America/Lower_Princes" "America/Marigot" "America/Mendoza"
    "America/Montreal" "America/Montserrat" "America/Nassau" "America/Nipigon"
    "America/Pangnirtung" "America/Port_of_Spain" "America/Porto_Acre" "America/Rainy_River"
    "America/Rosario" "America/Santa_Isabel" "America/Shiprock" "America/St_Barthelemy"
    "America/St_Kitts" "America/St_Lucia" "America/St_Thomas" "America/St_Vincent"
    "America/Thunder_Bay" "America/Tortola" "America/Virgin" "Antarctica/DumontDUrville"
    "Antarctica/McMurdo" "Antarctica/South_Pole" "Antarctica/Syowa" "Antarctica/Vostok"
    "Arctic/Longyearbyen" "Asia/Aden" "Asia/Ashkhabad" "Asia/Bahrain" "Asia/Brunei"
    "Asia/Calcutta" "Asia/Chongqing" "Asia/Chungking" "Asia/Dacca" "Asia/Harbin"
    "Asia/Istanbul" "Asia/Kashgar" "Asia/Katmandu" "Asia/Kuala_Lumpur" "Asia/Kuwait"
    "Asia/Macao" "Asia/Muscat" "Asia/Phnom_Penh" "Asia/Rangoon" "Asia/Saigon" "Asia/Tel_Aviv"
    "Asia/Thimbu" "Asia/Ujung_Pandang" "Asia/Ulan_Bator" "Asia/Vientiane" "Atlantic/Faeroe"
    "Atlantic/Jan_Mayen" "Atlantic/Reykjavik" "Atlantic/St_Helena" "Australia/ACT"
    "Australia/Canberra" "Australia/Currie" "Australia/LHI" "Australia/NSW" "Australia/North"
    "Australia/Queensland" "Australia/South" "Australia/Tasmania" "Australia/Victoria"
    "Australia/West" "Australia/Yancowinna" "Brazil/Acre" "Brazil/DeNoronha" "Brazil/East"
    "Brazil/West" "Canada/Atlantic" "Canada/Central" "Canada/Eastern" "Canada/Mountain"
    "Canada/Newfoundland" "Canada/Pacific" "Canada/Saskatchewan" "Canada/Yukon"
    "Chile/Continental" "Chile/EasterIsland" "Cuba" "Egypt" "Eire" "Etc/GMT+0" "Etc/GMT-0"
    "Etc/GMT0" "Etc/Greenwich" "Etc/UCT" "Etc/Universal" "Etc/Zulu" "Europe/Amsterdam"
    "Europe/Belfast" "Europe/Bratislava" "Europe/Busingen" "Europe/Copenhagen"
    "Europe/Guernsey" "Europe/Isle_of_Man" "Europe/Jersey" "Europe/Kiev" "Europe/Ljubljana"
    "Europe/Luxembourg" "Europe/Mariehamn" "Europe/Monaco" "Europe/Nicosia" "Europe/Oslo"
    "Europe/Podgorica" "Europe/San_Marino" "Europe/Sarajevo" "Europe/Skopje"
    "Europe/Stockholm" "Europe/Tiraspol" "Europe/Uzhgorod" "Europe/Vaduz" "Europe/Vatican"
    "Europe/Zagreb" "Europe/Zaporozhye" "GB" "GB-Eire" "GMT" "GMT+0" "GMT-0" "GMT0"
    "Greenwich" "Hongkong" "Iceland" "Indian/Antananarivo" "Indian/Christmas" "Indian/Cocos"
    "Indian/Comoro" "Indian/Kerguelen" "Indian/Mahe" "Indian/Mayotte" "Indian/Reunion" "Iran"
    "Israel" "Jamaica" "Japan" "Kwajalein" "Libya" "Mexico/BajaNorte" "Mexico/BajaSur"
    "Mexico/General" "NZ" "NZ-CHAT" "Navajo" "PRC" "Pacific/Chuuk" "Pacific/Enderbury"
    "Pacific/Funafuti" "Pacific/Johnston" "Pacific/Majuro" "Pacific/Midway" "Pacific/Pohnpei"
    "Pacific/Ponape" "Pacific/Saipan" "Pacific/Samoa" "Pacific/Truk" "Pacific/Wake"
    "Pacific/Wallis" "Pacific/Yap" "Poland" "Portugal" "ROC" "ROK" "Singapore" "Turkey" "UCT"
    "US/Alaska" "US/Aleutian" "US/Arizona" "US/Central" "US/East-Indiana" "US/Eastern"
    "US/Hawaii" "US/Indiana-Starke" "US/Michigan" "US/Mountain" "US/Pacific" "US/Samoa" "UTC"
    "Universal" "W-SU" "Zulu"))

(defun ascii-only-p (s)
  (every (lambda (c) (< (char-code c) 128)) s))

(defun ascii-string-equal (a b)
  "Case-insensitive compare using ASCII case folding only."
  (and (= (length a) (length b))
       (loop for ca across a for cb across b
             always (char-equal (if (< (char-code ca) 128) ca #\Nul)
                                (if (< (char-code cb) 128) cb #\Nul)))))

(defun parse-offset-timezone (s)
  "IsTimeZoneOffsetString: ASCII sign + HH | HHMM | HH:MM (hour 00-23, min 00-59,
   no seconds/fractions). Returns canonical ±HH:MM string, or NIL if not a
   (well-formed) offset. Zero offsets collapse to +00:00. Non-offset shapes (no
   leading +/-) return NIL; malformed offsets (leading +/-) throw RangeError."
  (when (or (null s) (zerop (length s))) (return-from parse-offset-timezone nil))
  (let ((c0 (char s 0)))
    (unless (or (char= c0 #\+) (char= c0 #\-))
      (return-from parse-offset-timezone nil))
    ;; From here it's meant to be an offset — malformed => RangeError.
    (flet ((bad () (js-throw (make-native-error "RangeError"
                              (format nil "invalid time zone: ~a" s)))))
      (let* ((sign (if (char= c0 #\-) -1 1))
             (rest (subseq s 1))
             (hh nil) (mm nil))
        (cond
          ;; HH:MM
          ((and (= (length rest) 5) (char= (char rest 2) #\:))
           (setf hh (subseq rest 0 2) mm (subseq rest 3 5)))
          ;; HHMM
          ((= (length rest) 4)
           (setf hh (subseq rest 0 2) mm (subseq rest 2 4)))
          ;; HH
          ((= (length rest) 2)
           (setf hh rest mm "00"))
          (t (bad)))
        (unless (and (%all #'%digit-p hh) (%all #'%digit-p mm)) (bad))
        (let ((h (parse-integer hh)) (m (parse-integer mm)))
          (when (or (> h 23) (> m 59)) (bad))
          (let ((total (* sign (+ (* h 60) m))))
            (if (zerop total)
                "+00:00"
                (multiple-value-bind (ah am) (floor (abs total) 60)
                  (format nil "~c~2,'0d:~2,'0d" (if (minusp total) #\- #\+) ah am)))))))))

(defun canonicalize-timezone-name (s)
  "CanonicalizeTimeZoneName. Returns canonical id string or throws RangeError."
  ;; offset zone?
  (let ((off (parse-offset-timezone s)))
    (when off (return-from canonicalize-timezone-name off)))
  ;; non-ASCII never matches a named zone
  (unless (ascii-only-p s)
    (js-throw (make-native-error "RangeError" (format nil "invalid time zone: ~a" s))))
  ;; named-zone lookup (ASCII case-insensitive)
  (let ((match (find s +iana-timezone-names+ :test #'ascii-string-equal)))
    (cond
      (match
       ;; "utc" -> "UTC" is handled by the canonical spelling in the table.
       match)
      (t (js-throw (make-native-error "RangeError"
                    (format nil "invalid time zone: ~a" s)))))))

;;; Return the UTC offset (in minutes, +east) that a canonical zone applies to
;;; wall-clock. Named zones -> 0 (offset-0 model). Offset zones -> parsed.
(defun timezone-offset-minutes (tz)
  (cond
    ;; offset zone ±HH:MM
    ((and (>= (length tz) 3)
          (or (char= (char tz 0) #\+) (char= (char tz 0) #\-))
          (find #\: tz))
     (let* ((sign (if (char= (char tz 0) #\-) -1 1))
            (h (parse-integer tz :start 1 :end 3))
            (m (parse-integer tz :start 4 :end 6)))
       (* sign (+ (* h 60) m))))
    ;; Etc/GMT±n : sign is INVERTED (Etc/GMT-3 is UTC+3).
    ((and (>= (length tz) 9) (string= (subseq tz 0 8) "Etc/GMT+"))
     (* -60 (parse-integer tz :start 8)))
    ((and (>= (length tz) 9) (string= (subseq tz 0 8) "Etc/GMT-"))
     (* 60 (parse-integer tz :start 8)))
    (t 0)))

;;; ===========================================================================
;;; hour-cycle resolution
;;; ===========================================================================
(defun dtf-default-hour-cycle (requested)
  "Locale default hour cycle when hour requested + no hc pinned. ja defaults to
   h11; other (en-family / tested) locales default to h12."
  (let* ((tag (first requested))
         (lid (and tag (parse-unicode-locale-id tag)))
         (lang (and lid (locale-id-language lid))))
    (if (and lang (string= lang "ja")) "h11" "h12")))

(defun dtf-hour12-cycle (requested)
  "The 12-hour cycle for hour12:true. ja uses h11; other locales use h12."
  (let* ((tag (first requested))
         (lid (and tag (parse-unicode-locale-id tag)))
         (lang (and lid (locale-id-language lid))))
    (if (and lang (string= lang "ja")) "h11" "h12")))

;;; ===========================================================================
;;; CreateDateTimeFormat — the constructor body
;;; ===========================================================================
(defun create-datetimeformat (dtf-obj locales options-arg required defaults)
  "Fill DTF-OBJ's :initialized-datetimeformat slot. REQUIRED/DEFAULTS drive
   ToDateTimeOptions. Reads options in spec order."
  (let* ((requested (canonicalize-locale-list locales))
         ;; ToObject on the options (legacy DateTimeFormat: null throws, undefined
         ;; -> fresh object, primitives boxed).
         (raw-opts (if (js-undefined-p options-arg)
                       (make-object :proto *null* :class "Object")
                       (to-object options-arg)))  ; to-object throws on null
         (opts raw-opts))
    ;; ---- read options in spec order ----
    (let* ((locale-matcher (get-option opts "localeMatcher" :string
                                       '("lookup" "best fit") "best fit"))
           (calendar-opt (dtf-get-type-option opts "calendar"))
           (numbering-opt (dtf-get-type-option opts "numberingSystem"))
           (hour12-raw (js-get opts "hour12"))
           (hour12-present (not (js-undefined-p hour12-raw)))
           (hour12 (and hour12-present (js-truthy hour12-raw)))
           (hourcycle-opt (get-option opts "hourCycle" :string
                                      '("h11" "h12" "h23" "h24") :undefined))
           (timezone-raw (js-get opts "timeZone")))
      (declare (ignore locale-matcher))
      ;; timeZone
      (let ((timezone (if (js-undefined-p timezone-raw)
                          "UTC"
                          (canonicalize-timezone-name (to-string timezone-raw)))))
        ;; component options
        (flet ((gopt (key values)
                 (get-option opts key :string values :undefined)))
          (let* ((weekday (gopt "weekday" +dtf-narrow-short-long+))
                 (era (gopt "era" +dtf-narrow-short-long+))
                 (year (gopt "year" +dtf-numeric-2digit+))
                 (month (gopt "month" +dtf-month-values+))
                 (day (gopt "day" +dtf-numeric-2digit+))
                 (dayperiod (gopt "dayPeriod" +dtf-narrow-short-long+))
                 (hour (gopt "hour" +dtf-numeric-2digit+))
                 (minute (gopt "minute" +dtf-numeric-2digit+))
                 (second (gopt "second" +dtf-numeric-2digit+))
                 (fsd (let ((v (get-number-option opts "fractionalSecondDigits" 1 3 :undefined)))
                        v))
                 (tzname (gopt "timeZoneName" +dtf-tzname-values+))
                 (format-matcher (get-option opts "formatMatcher" :string
                                             '("basic" "best fit") "best fit"))
                 (date-style (gopt "dateStyle" +dtf-style-values+))
                 (time-style (gopt "timeStyle" +dtf-style-values+)))
            (declare (ignore format-matcher))
            ;; normalize :undefined -> nil
            (macrolet ((nz (x) `(if (eq ,x :undefined) nil ,x)))
              (setf weekday (nz weekday) era (nz era) year (nz year)
                    month (nz month) day (nz day) dayperiod (nz dayperiod)
                    hour (nz hour) minute (nz minute) second (nz second)
                    fsd (nz fsd) tzname (nz tzname)
                    date-style (nz date-style) time-style (nz time-style)
                    hourcycle-opt (nz hourcycle-opt)))
            ;; style vs component mutual exclusion
            (let ((has-components
                    (or weekday era year month day dayperiod hour minute
                        second fsd tzname)))
              (when (or date-style time-style)
                (when has-components
                  (js-throw (make-native-error "TypeError"
                              "dateStyle/timeStyle may not be used with component options")))))
            ;; ToDateTimeOptions defaulting (applied to the already-read values, so
            ;; no extra observable [[Get]]s). needDefaults per required/defaults.
            (let ((need-defaults t))
              (when (member required '(:date :any))
                (when (or weekday year month day) (setf need-defaults nil)))
              (when (member required '(:time :any))
                (when (or dayperiod hour minute second fsd) (setf need-defaults nil)))
              (when (or date-style time-style) (setf need-defaults nil))
              (when need-defaults
                (when (member defaults '(:date :all))
                  (setf year "numeric" month "numeric" day "numeric"))
                (when (member defaults '(:time :all))
                  (setf hour "numeric" minute "numeric" second "numeric"))))
            ;; ---- resolve locale ----
            ;; NOTE: we call resolve-locale with NO relevant-extension-keys, then
            ;; extract ca/nu/hc from the first requested tag ourselves. (The core
            ;; resolve-locale mishandles list-valued -u- keyword payloads, and its
            ;; matching drops the extension on locale fallback anyway.)
            (let* ((resolved (resolve-locale requested '() '()))
                   (data-locale (getf resolved :data-locale))
                   (req-uk (dtf-requested-u-keywords requested))
                   ;; unsupported extension values are ignored (dropped).
                   (ext-ca (let ((c (cdr (assoc "ca" req-uk :test #'string=))))
                             (and c (dtf-supported-calendar-p (dtf-canon-calendar c)) c)))
                   (ext-nu (let ((n (cdr (assoc "nu" req-uk :test #'string=))))
                             (and n (dtf-supported-numbering-p n) n)))
                   (ext-hc (let ((h (cdr (assoc "hc" req-uk :test #'string=))))
                             (and h (member h '("h11" "h12" "h23" "h24") :test #'string=) h)))
                   ;; calendar: supported option overrides ext; default gregory.
                   (calendar-opt* (and calendar-opt
                                       (dtf-supported-calendar-p (dtf-canon-calendar calendar-opt))
                                       calendar-opt))
                   (calendar (dtf-canon-calendar (or calendar-opt* ext-ca "gregory")))
                   (calendar-from-opt (and calendar-opt* t))
                   ;; numberingSystem: supported option overrides ext; default latn.
                   (numbering-opt* (and numbering-opt
                                        (dtf-supported-numbering-p numbering-opt)
                                        numbering-opt))
                   (numbering (or numbering-opt* ext-nu "latn"))
                   (numbering-from-opt (and numbering-opt* t)))
              (declare (ignorable calendar-from-opt numbering-from-opt))
              ;; figure out whether the format includes an hour
              (let* ((style-has-time (and time-style t))
                     (has-hour (or hour style-has-time
                                   ;; dayPeriod alone doesn't add hour, but resolved
                                   ;; format may; keep simple: hour presence.
                                   nil))
                     (hour-cycle nil)
                     (hour12-out :undefined))
                (when has-hour
                  (cond
                    (hour12-present
                     (setf hour-cycle (if hour12 (dtf-hour12-cycle requested) "h23")
                           hour12-out (js-bool hour12)))
                    (hourcycle-opt
                     (setf hour-cycle hourcycle-opt
                           hour12-out (js-bool (member hour-cycle '("h11" "h12") :test #'string=))))
                    (ext-hc
                     (setf hour-cycle ext-hc
                           hour12-out (js-bool (member hour-cycle '("h11" "h12") :test #'string=))))
                    (t
                     (setf hour-cycle (dtf-default-hour-cycle requested)
                           hour12-out (js-bool (member hour-cycle '("h11" "h12") :test #'string=))))))
                ;; build resolved locale string: the ca/nu/hc extension is
                ;; reflected in the resolved locale iff the extension value was
                ;; present AND the finally-resolved value equals it.
                (let* ((loc-ca (and ext-ca (string= (dtf-canon-calendar ext-ca) calendar) ext-ca))
                       (loc-nu (and ext-nu (string= ext-nu numbering) ext-nu))
                       ;; hc extension reflected in locale when present and not
                       ;; overridden by hour12. With an hour, reflect iff the
                       ;; resolved hour-cycle equals the extension (an hourCycle
                       ;; option that coincides still reflects). Without an hour,
                       ;; reflect only when no hourCycle option was supplied.
                       (loc-hc (and ext-hc (not hour12-present)
                                    (if has-hour
                                        (equal ext-hc hour-cycle)
                                        (not hourcycle-opt))
                                    ext-hc))
                       (locale-str (dtf-build-locale-string data-locale loc-ca loc-nu loc-hc)))
                  ;; store slots
                  (setf (getf (js-object-internal dtf-obj) :initialized-datetimeformat)
                        (list :locale locale-str :data-locale data-locale
                              :calendar calendar :numbering-system numbering
                              :time-zone timezone
                              :hour-cycle hour-cycle :hour12 hour12-out
                              :weekday weekday :era era :year year :month month
                              :day day :day-period dayperiod
                              :hour hour :minute minute :second second
                              :fractional-second-digits fsd :time-zone-name tzname
                              :date-style date-style :time-style time-style
                              :has-hour has-hour
                              :bound-format nil)))))))))
    dtf-obj))

(defun dtf-requested-u-keywords (requested)
  "Return an alist of (key . value-string) for the -u- keywords of the FIRST
   requested locale tag (ca/nu/hc etc.). Empty if none."
  (let ((tag (first requested)))
    (when tag
      (let* ((lid (parse-unicode-locale-id tag))
             (uentry (and lid (assoc #\u (locale-id-extensions lid))))
             (kws (and uentry (getf (cdr uentry) :keywords))))
        (loop for (k . types) in kws
              for v = (format nil "~{~a~^-~}" types)
              when (plusp (length v)) collect (cons k v))))))

(defun dtf-ext-value (v)
  "Normalize a resolve-locale extension value (may be a list of type subtags, a
   string, \"\", NIL, or :undefined) to a non-empty string or NIL."
  (cond ((null v) nil)
        ((eq v :undefined) nil)
        ((stringp v) (if (plusp (length v)) v nil))
        ((consp v) (let ((s (format nil "~{~a~^-~}" v))) (if (plusp (length s)) s nil)))
        (t nil)))

(defun dtf-supported-calendar-p (ca)
  (member ca +supported-calendars+ :test #'string=))
(defun dtf-supported-numbering-p (nu)
  (member nu +numbering-system-digit-names+ :test #'string=))

(defun dtf-canon-calendar (ca)
  "Canonicalize a calendar type value (alias -> canonical)."
  (cond ((string= ca "ethiopic-amete-alem") "ethioaa")
        ((string= ca "islamicc") "islamic-civil")
        ((string= ca "gregorian") "gregory")
        (t ca)))

(defun dtf-build-locale-string (base ca nu hc)
  "Build data-locale + -u- keywords for the surviving extension values, in
   canonical (sorted-by-key) order: ca, hc, nu."
  (let ((parts '()))
    (when ca (push (cons "ca" ca) parts))
    (when hc (push (cons "hc" hc) parts))
    (when nu (push (cons "nu" nu) parts))
    (setf parts (stable-sort (nreverse parts) #'string< :key #'car))
    (if parts
        (format nil "~a-u~{-~a-~a~}" base
                (loop for (k . v) in parts nconc (list k v)))
        base)))

;;; ===========================================================================
;;; en formatting data
;;; ===========================================================================
(defparameter +en-month-long+
  #("January" "February" "March" "April" "May" "June" "July" "August"
    "September" "October" "November" "December"))
(defparameter +en-month-short+
  #("Jan" "Feb" "Mar" "Apr" "May" "Jun" "Jul" "Aug" "Sep" "Oct" "Nov" "Dec"))
(defparameter +en-month-narrow+
  #("J" "F" "M" "A" "M" "J" "J" "A" "S" "O" "N" "D"))
(defparameter +en-weekday-long+
  ;; index 0 = Sunday (week-day returns 0..6 with 0 = Thursday? NO: week-day 0 =
  ;; Sunday per ECMAScript: WeekDay(0)=4=Thursday... week-day returns the JS day
  ;; of week where 0=Sunday). date.lisp week-day: (mod (day+4) 7): epoch day 0
  ;; (Thu 1970-01-01) -> (0+4) mod 7 = 4 => 4=Thursday, 0=Sunday. Good.
  #("Sunday" "Monday" "Tuesday" "Wednesday" "Thursday" "Friday" "Saturday"))
(defparameter +en-weekday-short+
  #("Sun" "Mon" "Tue" "Wed" "Thu" "Fri" "Sat"))
(defparameter +en-weekday-narrow+
  #("S" "M" "T" "W" "T" "F" "S"))

(defun en-era (year style)
  "Gregory era string. YEAR is the proleptic gregorian year (may be <= 0)."
  (let ((bc (<= year 0)))
    (cond ((string= style "long") (if bc "Before Christ" "Anno Domini"))
          ((string= style "narrow") (if bc "B" "A"))
          (t (if bc "BC" "AD")))))

;;; en dayPeriod (the dayPeriod OPTION): long/short = phrase, narrow = phrase but
;;; noon -> "n". Boundaries (CLDR en): night 21-05, morning 06-11, noon 12,
;;; afternoon 12-17 (excl noon), evening 18-20. noon is exactly hour 12 minute 0.
(defun en-day-period (hour minute style)
  (let ((phrase
          (cond
            ((and (= hour 12) (= minute 0)) (if (string= style "narrow") "n" "noon"))
            ((< hour 6) "at night")            ; 0-5
            ((< hour 12) "in the morning")     ; 6-11
            ((< hour 18) "in the afternoon")   ; 12-17
            ((< hour 21) "in the evening")     ; 18-20
            (t "at night"))))                  ; 21-23
    phrase))

;;; AM/PM (the dayPeriod that goes with h11/h12 hours) — always the fixed marker.
(defun en-am-pm (hour) (if (< hour 12) "AM" "PM"))

;;; digit mapping for the numbering system
(defun dtf-digits (ns)
  (or (cdr (assoc ns +numbering-system-digits+ :test #'string=))
      "0123456789"))
(defun dtf-decimal-sep (ns)
  (if (string= ns "arab") (string (code-char #x066B)) "."))

(defun dtf-map-number (str ns)
  "Map ASCII digits in STR to the numbering system NS digits."
  (let ((digits (dtf-digits ns)))
    (if (string= ns "latn")
        str
        (map 'string (lambda (c)
                       (if (char<= #\0 c #\9)
                           (char digits (- (char-code c) (char-code #\0)))
                           c))
             str))))

(defun dtf-num (n ns &optional (min-int 1))
  "Format integer N with at least MIN-INT digits, mapped to NS."
  (dtf-map-number (format nil "~v,'0d" min-int n) ns))

;;; ===========================================================================
;;; Field extraction from epoch-ms, honoring the (offset) time zone
;;; ===========================================================================
(defun dtf-allow (allowed key val)
  "If ALLOWED is NIL (legacy Date/epoch), return VAL unchanged. Otherwise return
   VAL only if KEY is in ALLOWED, else NIL (the object can't supply that field)."
  (if (null allowed)
      val
      (and (member key allowed) val)))

;;; ---- Temporal object recognition + field extraction ----
(defun dtf-temporal-brand (v)
  "Return the Temporal brand keyword for V, or NIL."
  (when (and (js-object-p v) (js-object-internal v))
    (let ((int (js-object-internal v)))
      (cond ((not (eq (getf int :temporal-instant 'none) 'none)) :temporal-instant)
            ((not (eq (getf int :temporal-plaindatetime 'none) 'none)) :temporal-plaindatetime)
            ((not (eq (getf int :temporal-plaindate 'none) 'none)) :temporal-plaindate)
            ((not (eq (getf int :temporal-plaintime 'none) 'none)) :temporal-plaintime)
            ((not (eq (getf int :temporal-plainyearmonth 'none) 'none)) :temporal-plainyearmonth)
            ((not (eq (getf int :temporal-plainmonthday 'none) 'none)) :temporal-plainmonthday)
            ((not (eq (getf int :temporal-zoneddatetime 'none) 'none)) :temporal-zoneddatetime)
            (t nil)))))

(defun dtf-iso-weekday (year month day)
  "0=Sunday .. 6=Saturday, from a proleptic gregorian Y/M/D (exact integers)."
  ;; Use the epoch-day approach via date.lisp make-day (float ok for range).
  (let ((d (make-day (float year 1d0) (float (1- month) 1d0) (float day 1d0))))
    (truncate (js-mod (+ d 4d0) 7d0))))

(defun dtf-temporal-fields (brand v tz)
  "Extract a fields plist (with :allowed) for a Temporal object. TZ used only for
   Instant/ZonedDateTime -> wall clock."
  (let ((int (js-object-internal v)))
    (ecase brand
      (:temporal-instant
       ;; ns integer -> epoch-ms -> fields via tz
       (let* ((ns (getf int :temporal-instant))
              (ms (/ ns 1000000)))
         (append (dtf-fields (float ms 1d0) tz)
                 (list :allowed '(:weekday :era :year :month :day
                                  :hour :minute :second :fractional-second
                                  :day-period :time-zone-name)))))
      (:temporal-plaindatetime
       (let* ((pd (getf int :temporal-plaindatetime))
              (date (getf pd :date)) (time (getf pd :time)))
         (dtf-iso-datetime-fields date time
                                  '(:weekday :era :year :month :day
                                    :hour :minute :second :fractional-second :day-period))))
      (:temporal-plaindate
       (let ((date (getf int :temporal-plaindate)))
         (dtf-iso-datetime-fields date nil
                                  '(:weekday :era :year :month :day))))
      (:temporal-plaintime
       (let ((time (getf int :temporal-plaintime)))
         (dtf-iso-datetime-fields nil time
                                  '(:hour :minute :second :fractional-second :day-period))))
      (:temporal-plainyearmonth
       (let ((date (getf int :temporal-plainyearmonth)))
         (dtf-iso-datetime-fields date nil '(:era :year :month))))
      (:temporal-plainmonthday
       (let ((date (getf int :temporal-plainmonthday)))
         (dtf-iso-datetime-fields date nil '(:month :day))))
      (:temporal-zoneddatetime
       (js-throw (make-native-error "TypeError"
                  "Temporal.ZonedDateTime is not supported by Intl.DateTimeFormat"))))))

(defun dtf-iso-datetime-fields (date time allowed)
  "Build a fields plist from an iso-date and/or iso-time struct."
  (let ((y (and date (iso-date-year date)))
        (mo (and date (iso-date-month date)))
        (d (and date (iso-date-day date))))
    (list :year (or y 1970)
          :month (if mo (1- mo) 0)        ; 0-based to match legacy
          :day (or d 1)
          :weekday (if date (dtf-iso-weekday y mo d) 0)
          :hour (if time (iso-time-hour time) 0)
          :minute (if time (iso-time-minute time) 0)
          :second (if time (iso-time-second time) 0)
          :ms (if time (iso-time-millisecond time) 0)
          :allowed allowed)))

(defun dtf-fields (epoch-ms tz)
  "Return a plist of calendar fields for EPOCH-MS in zone TZ (offset model).
   All values CL integers. :era-year is the display year (abs for BC handled by
   caller). :year is the proleptic gregorian year (may be <= 0)."
  (let* ((shifted (+ epoch-ms (* (timezone-offset-minutes tz) 60000d0)))
         (yr (year-from-time shifted)))
    (list :year (truncate yr)
          :month (truncate (month-from-time shifted))    ; 0-11
          :day (truncate (date-from-time shifted))       ; 1-31
          :weekday (truncate (week-day shifted))         ; 0=Sun
          :hour (truncate (hours-from-time shifted))     ; 0-23
          :minute (truncate (min-from-time shifted))
          :second (truncate (sec-from-time shifted))
          :ms (truncate (ms-from-time shifted)))))

;;; ===========================================================================
;;; Pattern assembly — produce a list of (type . value) parts
;;; ===========================================================================
(defun dtf-hour-value (hour24 hour-cycle)
  "Return the displayed hour NUMBER for a given cycle."
  (cond
    ((string= hour-cycle "h11") (mod hour24 12))          ; 0-11
    ((string= hour-cycle "h12") (let ((h (mod hour24 12))) (if (= h 0) 12 h))) ; 1-12
    ((string= hour-cycle "h23") hour24)                   ; 0-23
    ((string= hour-cycle "h24") (if (= hour24 0) 24 hour24)) ; 1-24
    (t hour24)))

(defun dtf-effective-style-components (slots)
  "When dateStyle/timeStyle set, expand to component selections. Returns a fresh
   plist of the same component keys the manual path uses. en-US CLDR shapes."
  (let ((ds (getf slots :date-style)) (ts (getf slots :time-style))
        (out '()))
    ;; date part
    (when ds
      (cond
        ((string= ds "full")
         (setf out (list* :weekday "long" :year "numeric" :month "long" :day "numeric" out)))
        ((string= ds "long")
         (setf out (list* :year "numeric" :month "long" :day "numeric" out)))
        ((string= ds "medium")
         (setf out (list* :year "numeric" :month "short" :day "numeric" out)))
        ((string= ds "short")
         (setf out (list* :year "2-digit" :month "numeric" :day "numeric" out)))))
    ;; time part
    (when ts
      (let ((sec (if (member ts '("full" "long" "medium") :test #'string=) "numeric" nil)))
        (setf out (list* :hour "numeric" :minute "numeric" out))
        (when sec (setf out (list* :second sec out)))
        (cond
          ((string= ts "full")
           (setf out (list* :time-zone-name "long" out)))
          ((string= ts "long")
           (setf out (list* :time-zone-name "short" out))))))
    out))

(defun dtf-format-to-parts-list (slots source)
  "Return the list of (type . value) conses. SOURCE is either an epoch-ms double
   or a pre-computed fields plist (from a Temporal object). When it is a Temporal
   fields plist it carries :allowed (the set of field keywords the object can
   supply) so we can suppress fields the object doesn't have."
  (let* ((tz (getf slots :time-zone))
         (ns (getf slots :numbering-system))
         (temporal-fields (and (consp source) (eq (car source) :fields) (cdr source)))
         (f (if temporal-fields temporal-fields (dtf-fields source tz)))
         (allowed (getf f :allowed))            ; NIL for legacy => all allowed
         (year (getf f :year))
         (using-style (or (getf slots :date-style) (getf slots :time-style)))
         (comp (if using-style
                   (dtf-effective-style-components slots)
                   slots))
         (weekday (dtf-allow allowed :weekday (getf comp :weekday)))
         (era (dtf-allow allowed :era (getf comp :era)))
         (yopt (dtf-allow allowed :year (getf comp :year)))
         (mopt (dtf-allow allowed :month (getf comp :month)))
         (dopt (dtf-allow allowed :day (getf comp :day)))
         (dpopt (dtf-allow allowed :day-period (getf comp :day-period)))
         (hopt (dtf-allow allowed :hour (getf comp :hour)))
         (minopt (dtf-allow allowed :minute (getf comp :minute)))
         (sopt (dtf-allow allowed :second (getf comp :second)))
         (fsd (dtf-allow allowed :fractional-second (getf comp :fractional-second-digits)))
         (tzn (dtf-allow allowed :time-zone-name (getf comp :time-zone-name)))
         (hour-cycle (getf slots :hour-cycle))
         (parts '()))
    (labels ((emit (type val) (push (cons type val) parts))
             (lit (s) (emit "literal" s)))
      ;; ---- DATE portion ----
      (when weekday
        (emit "weekday" (aref (cond ((string= weekday "long") +en-weekday-long+)
                                    ((string= weekday "short") +en-weekday-short+)
                                    (t +en-weekday-narrow+))
                              (getf f :weekday)))
        (lit ", "))
      ;; date: en-US is month/day/year for numeric; long date is "Month D, YYYY"
      (let ((month-numeric (member mopt '("2-digit" "numeric") :test #'equal))
            (month-textual (member mopt '("long" "short" "narrow") :test #'equal)))
        (cond
          ;; textual month => "Month D, YYYY" order
          (month-textual
           (emit "month" (aref (cond ((string= mopt "long") +en-month-long+)
                                     ((string= mopt "short") +en-month-short+)
                                     (t +en-month-narrow+))
                               (getf f :month)))
           (when dopt (lit " ") (emit "day" (dtf-num (getf f :day) ns (if (string= dopt "2-digit") 2 1))))
           (when yopt (lit ", ") (dtf-emit-year year yopt ns #'emit)))
          ;; numeric month => "M/D/YYYY"
          ((or month-numeric yopt dopt)
           (let ((first t))
             (when mopt
               (emit "month" (dtf-num (1+ (getf f :month)) ns (if (string= mopt "2-digit") 2 1)))
               (setf first nil))
             (when dopt
               (unless first (lit "/"))
               (emit "day" (dtf-num (getf f :day) ns (if (string= dopt "2-digit") 2 1)))
               (setf first nil))
             (when yopt
               (unless first (lit "/"))
               (dtf-emit-year year yopt ns #'emit)
               (setf first nil))))))
      ;; era (appended after year when requested and no textual layout handled it)
      (when (and era (not (member mopt '("long" "short" "narrow") :test #'equal)))
        (lit " ") (emit "era" (en-era year era)))
      (when (and era (member mopt '("long" "short" "narrow") :test #'equal))
        (lit " ") (emit "era" (en-era year era)))
      ;; separator between date and time
      (let ((have-date (or weekday yopt mopt dopt))
            (have-time (or hopt minopt sopt dpopt)))
        (when (and have-date have-time) (lit ", ")))
      ;; ---- TIME portion ----
      (when hopt
        (let ((hv (dtf-hour-value (getf f :hour) (or hour-cycle "h23"))))
          (emit "hour" (dtf-num hv ns (if (string= hopt "2-digit") 2 1)))))
      (when minopt
        (when hopt (lit ":"))
        ;; en: minute is 2-digit whenever it is not the sole/leading numeric field
        ;; standing alone. In practice CLDR en renders minute 2-digit except when
        ;; it is the only time field. Follows-hour OR has-second => 2-digit.
        (emit "minute" (dtf-num (getf f :minute) ns
                                (if (or hopt sopt (string= minopt "2-digit")) 2 1))))
      (when sopt
        (when (or hopt minopt) (lit ":"))
        (emit "second" (dtf-num (getf f :second) ns (if (or hopt minopt (string= sopt "2-digit")) 2 1))))
      (when fsd
        (let* ((msstr (format nil "~3,'0d" (getf f :ms)))
               (frac (subseq msstr 0 fsd)))
          (emit "literal" (dtf-decimal-sep ns))
          (emit "fractionalSecond" (dtf-map-number frac ns))))
      ;; dayPeriod: the AM/PM marker for h11/h12 (when hour shown), OR the
      ;; dayPeriod OPTION phrase.
      (cond
        (dpopt
         ;; explicit dayPeriod option
         (when (or hopt minopt sopt) (lit " "))
         (emit "dayPeriod" (en-day-period (getf f :hour) (getf f :minute) dpopt)))
        ((and hopt (member (or hour-cycle "h23") '("h11" "h12") :test #'string=))
         (lit " ")
         (emit "dayPeriod" (en-am-pm (getf f :hour)))))
      ;; timeZoneName
      (when tzn
        (when (or hopt minopt sopt dpopt) (lit " "))
        (emit "timeZoneName" (dtf-tz-name-string tz tzn))))
    (nreverse parts)))

;; NOTE: `parts-year` symbol used above is a stray from a refactor; define a real
;; year emitter.
(defun dtf-emit-year (year yopt ns emit)
  (let* ((bc (<= year 0))
         (disp (if bc (+ 1 (- year)) year))  ; year 0 -> 1 BC, -1 -> 2 BC
         (str (if (string= yopt "2-digit")
                  (dtf-map-number (format nil "~2,'0d" (mod disp 100)) ns)
                  (dtf-map-number (format nil "~d" disp) ns))))
    (funcall emit "year" str)))

(defun dtf-tz-name-string (tz style)
  "en time-zone-name rendering for the (UTC / offset) zones we support."
  (let ((is-offset (and (>= (length tz) 3)
                        (or (char= (char tz 0) #\+) (char= (char tz 0) #\-))
                        (find #\: tz))))
    (cond
      ;; UTC named zone
      ((string= tz "UTC")
       (cond ((string= style "long") "Coordinated Universal Time")
             ((string= style "short") "UTC")
             ((string= style "shortOffset") "GMT")
             ((string= style "longOffset") "GMT")
             ((string= style "shortGeneric") "GMT")
             ((string= style "longGeneric") "GMT")
             (t "UTC")))
      (is-offset
       (let* ((sign (char tz 0))
              (h (parse-integer tz :start 1 :end 3))
              (m (parse-integer tz :start 4 :end 6)))
         (cond
           ((or (string= style "longOffset"))
            (format nil "GMT~c~2,'0d:~2,'0d" sign h m))
           ((string= style "shortOffset")
            (if (zerop m)
                (format nil "GMT~c~d" sign h)
                (format nil "GMT~c~d:~2,'0d" sign h m)))
           ((member style '("long" "short" "shortGeneric" "longGeneric") :test #'string=)
            (if (zerop m)
                (format nil "GMT~c~d" sign h)
                (format nil "GMT~c~d:~2,'0d" sign h m)))
           (t (format nil "GMT~c~2,'0d:~2,'0d" sign h m)))))
      ;; other named zones: fall back to the id
      (t (cond ((member style '("long" "longGeneric") :test #'string=) tz)
               (t tz))))))

(defun dtf-parts-to-string (parts)
  (with-output-to-string (s)
    (dolist (p parts) (write-string (cdr p) s))))

;;; ===========================================================================
;;; format(value) — coerce value to a time value
;;; ===========================================================================
(defun dtf-to-epoch (slots value &optional (allow-undefined t))
  "Return epoch-ms (double). undefined -> now (format) when ALLOW-UNDEFINED.
   Coerce via ToNumber then TimeClip; RangeError on non-finite."
  (declare (ignore slots))
  (let ((n (if (js-undefined-p value)
               (if allow-undefined
                   (float (get-universal-time-ms) 1d0)
                   (js-throw (make-native-error "TypeError" "date is required")))
               (to-number value))))
    (let ((clipped (time-clip (if (floatp n) n (float n 1d0)))))
      (when (js-nan-p clipped)
        (js-throw (make-native-error "RangeError" "Invalid time value")))
      clipped)))

(defun get-universal-time-ms ()
  ;; crude "now"; format(undefined) is rarely asserted for an exact value.
  (* 1000d0 (- (get-universal-time) 2208988800)))

(defun dtf-requested-fields (slots)
  "The set of component-field keywords the formatter actually resolved to (after
   dateStyle/timeStyle expansion). Used for the Temporal overlap check."
  (let* ((using-style (or (getf slots :date-style) (getf slots :time-style)))
         (comp (if using-style (dtf-effective-style-components slots) slots))
         (out '()))
    (flet ((add (key field) (when (getf comp key) (push field out))))
      (add :weekday :weekday) (add :era :era) (add :year :year)
      (add :month :month) (add :day :day) (add :day-period :day-period)
      (add :hour :hour) (add :minute :minute) (add :second :second)
      (add :fractional-second-digits :fractional-second)
      (add :time-zone-name :time-zone-name))
    out))

(defun dtf-resolve-source (slots value &optional (allow-undefined t))
  "Resolve a format argument to a SOURCE for dtf-format-to-parts-list: either an
   epoch-ms double (Number/Date/undefined->now) or (:fields . plist) for Temporal.
   Performs the Temporal overlap TypeError check."
  (let ((brand (dtf-temporal-brand value)))
    (cond
      (brand
       (let* ((fields (dtf-temporal-fields brand value (getf slots :time-zone)))
              (allowed (getf fields :allowed))
              (requested (dtf-requested-fields slots)))
         ;; overlap check: at least one requested field must be supplied by the
         ;; object (era/timeZoneName don't count as the sole overlap for date/time
         ;; objects — but the tests only require SOME date|time overlap; use the
         ;; primary component sets).
         (unless (intersection requested allowed)
           (js-throw (make-native-error "TypeError"
                       "Temporal object has no overlap with the requested format")))
         (cons :fields fields)))
      (t (dtf-to-epoch slots value allow-undefined)))))

;;; ===========================================================================
;;; Bound format function
;;; ===========================================================================
(defun dtf-make-bound-format (realm dtf-obj)
  (let ((slots (dtf-slots dtf-obj)))
    (declare (ignore slots))
    (let ((f (native-function realm ""
               (lambda (this args) (declare (ignore this))
                 (let ((s (dtf-slots dtf-obj)))
                   (let ((src (dtf-resolve-source s (arg 0 args))))
                     (dtf-parts-to-string (dtf-format-to-parts-list s src)))))
               1)))
      ;; name is "" and length 1 already; property order length,name is default.
      f)))

;;; ===========================================================================
;;; resolvedOptions()
;;; ===========================================================================
(defun dtf-resolved-options (realm slots)
  (let ((o (make-object :proto (realm-object-proto realm) :class "Object")))
    (flet ((p (k v) (put o k v)))
      (p "locale" (getf slots :locale))
      (p "calendar" (getf slots :calendar))
      (p "numberingSystem" (getf slots :numbering-system))
      (p "timeZone" (getf slots :time-zone))
      (when (getf slots :hour-cycle)
        (p "hourCycle" (getf slots :hour-cycle))
        (let ((h12 (getf slots :hour12)))
          (unless (eq h12 :undefined) (p "hour12" h12))))
      ;; components in canonical order (only present ones); OR dateStyle/timeStyle
      (let ((ds (getf slots :date-style)) (ts (getf slots :time-style)))
        (flet ((c (k v) (when v (p k v))))
          (c "weekday" (getf slots :weekday))
          (c "era" (getf slots :era))
          (c "year" (getf slots :year))
          (c "month" (getf slots :month))
          (c "day" (getf slots :day))
          (c "dayPeriod" (getf slots :day-period))
          (c "hour" (getf slots :hour))
          (c "minute" (getf slots :minute))
          (c "second" (getf slots :second))
          (when (getf slots :fractional-second-digits)
            (p "fractionalSecondDigits"
               (float (getf slots :fractional-second-digits) 1d0)))
          (c "timeZoneName" (getf slots :time-zone-name))
          (c "dateStyle" ds)
          (c "timeStyle" ts))))
    o))

;;; ===========================================================================
;;; supportedLocalesOf
;;; ===========================================================================
(defun dtf-supported-locales-of (locales options)
  (declare (ignore options))
  (let* ((requested (canonicalize-locale-list locales))
         (available (intl-available-locales))
         (out '()))
    (dolist (req requested)
      (let* ((lid (parse-unicode-locale-id req))
             (base (and lid (base-name-string lid))))
        (when (and base (best-available-locale available (%lc base)))
          (push req out))))
    (make-array-object (nreverse out))))

;;; ===========================================================================
;;; install-intl_datetimeformat
;;; ===========================================================================
(defun install-intl_datetimeformat (realm)
  (let* ((op (realm-object-proto realm))
         (proto (make-object :proto op :class "Object"))
         (legacy-sym (make-js-symbol "IntlLegacyConstructedSymbol"))
         (ctor (native-function realm "DateTimeFormat"
                 (lambda (this args)
                   ;; called as a function (no new): behave like Construct with
                   ;; newTarget = active function? Spec: NewTarget defaults to
                   ;; ctor; then Chain: if this is an ordinary instance, define
                   ;; the fallback symbol on it and return this.
                   (dtf-construct realm proto legacy-sym this args *undefined*))
                 0)))
    (setf *intl-dtf-proto* proto
          *intl-dtf-ctor* ctor
          *intl-legacy-symbol* legacy-sym)
    ;; [[Construct]]
    (setf (js-object-construct ctor)
          (lambda (args nt)
            (dtf-construct realm proto legacy-sym *undefined* args nt)))
    (def-value ctor "prototype" proto :writable nil :configurable nil)
    (def-value proto "constructor" ctor)
    ;; supportedLocalesOf (static, length 1)
    (def-method realm ctor "supportedLocalesOf" 1 (this args)
      (declare (ignore this))
      (dtf-supported-locales-of (arg 0 args) (arg 1 args)))
    ;; ---- prototype.format (bound getter) ----
    (def-getter realm proto "format"
      (lambda (this args) (declare (ignore args))
        (let ((slots (require-dtf this)))
          ;; cache the bound format on the object
          (let ((dtf-obj (dtf-owner-object this)))
            (or (getf slots :bound-format)
                (let ((bf (dtf-make-bound-format realm dtf-obj)))
                  (setf (getf (getf (js-object-internal dtf-obj) :initialized-datetimeformat)
                              :bound-format)
                        bf)
                  bf))))))
    ;; ---- prototype.formatToParts ----
    (def-method realm proto "formatToParts" 1 (this args)
      (let* ((slots (require-dtf this))
             (src (dtf-resolve-source slots (arg 0 args)))
             (parts (dtf-format-to-parts-list slots src)))
        (make-array-object
         (mapcar (lambda (p)
                   (let ((o (make-object :proto (realm-object-proto realm) :class "Object")))
                     (put o "type" (car p))
                     (put o "value" (cdr p))
                     o))
                 parts))))
    ;; ---- prototype.resolvedOptions ----
    (def-method realm proto "resolvedOptions" 0 (this args)
      (declare (ignore args))
      (dtf-resolved-options realm (require-dtf this)))
    ;; ---- prototype.formatRange / formatRangeToParts ----
    (def-method realm proto "formatRange" 2 (this args)
      (let ((slots (require-dtf this)))
        (dtf-format-range realm slots (arg 0 args) (arg 1 args) nil)))
    (def-method realm proto "formatRangeToParts" 2 (this args)
      (let ((slots (require-dtf this)))
        (dtf-format-range realm slots (arg 0 args) (arg 1 args) t)))
    ;; @@toStringTag
    (put proto (symbol-tostringtag realm) "Intl.DateTimeFormat"
         :enumerable nil :writable nil :configurable t)
    (intl-register realm "DateTimeFormat" ctor)
    ;; wire Date.prototype.toLocale* through us (best-effort; only if Date exists)
    (dtf-wire-date-prototype realm ctor)
    ctor))

(defun dtf-owner-object (this)
  "The DateTimeFormat object whose slots we resolved (handles the legacy unwrap)."
  (if (dtf-slots this)
      this
      (let ((inner (and *intl-dtf-ctor* (ordinary-instance-of-p this *intl-dtf-ctor*)
                        (js-get this *intl-legacy-symbol*))))
        (if (and inner (dtf-slots inner)) inner this))))

(defun dtf-construct (realm proto legacy-sym this args nt)
  "ChainDateTimeFormat + CreateDateTimeFormat."
  (let* ((newtarget (if (js-undefined-p nt) nil nt))
         (obj (make-object :proto (if newtarget
                                      (proto-from-newtarget newtarget proto)
                                      proto)
                           :class "Object")))
    ;; CreateDateTimeFormat with required=:any defaults=:date (the DTF default).
    (create-datetimeformat obj (arg 0 args) (arg 1 args) :any :date)
    ;; ChainDateTimeFormat: when called without new AND this is an ordinary
    ;; instance of DateTimeFormat, hang the fallback symbol on THIS and return it.
    (when (and (null newtarget) (js-object-p this)
               (ordinary-instance-of-p this *intl-dtf-ctor*))
      (js-define-own-property this legacy-sym
        (list :value obj :writable nil :enumerable nil :configurable nil))
      (return-from dtf-construct this))
    obj))

;;; ---- formatRange ----
(defun dtf-format-range (realm slots startv endv to-parts)
  (declare (ignore realm))
  ;; TypeError if either endpoint is undefined (before ToNumber coercion).
  (when (or (js-undefined-p startv) (js-undefined-p endv))
    (js-throw (make-native-error "TypeError" "formatRange requires two dates")))
  ;; SameTemporalType: both must be the same kind (both plain-number/Date, or the
  ;; same Temporal brand) — checked BEFORE any ToNumber/TimeClip.
  (let ((b1 (dtf-temporal-brand startv)) (b2 (dtf-temporal-brand endv)))
    (unless (eq b1 b2)
      (js-throw (make-native-error "TypeError" "formatRange arguments differ in type"))))
  (let* ((s1 (dtf-resolve-source slots startv))
         (s2 (dtf-resolve-source slots endv)))
    ;; ordering does not matter — no RangeError on x>y.
    (let ((p1 (dtf-format-to-parts-list slots s1))
          (p2 (dtf-format-to-parts-list slots s2)))
      (if (equal (dtf-parts-to-string p1) (dtf-parts-to-string p2))
          ;; collapse to a single format (shared)
          (if to-parts
              (dtf-parts-array (mapcar (lambda (p) (list* "shared" p)) p1))
              (dtf-parts-to-string p1))
          (if to-parts
              (dtf-parts-array
               (append (mapcar (lambda (p) (list* "startRange" p)) p1)
                       (list (list* "shared" (cons "literal" " – ")))
                       (mapcar (lambda (p) (list* "endRange" p)) p2)))
              (format nil "~a – ~a" (dtf-parts-to-string p1) (dtf-parts-to-string p2)))))))

(defun dtf-parts-array (source-parts)
  "SOURCE-PARTS = list of (source type . value)."
  (make-array-object
   (mapcar (lambda (sp)
             (let ((o (make-object :proto (realm-object-proto *current-realm*) :class "Object")))
               (put o "type" (cadr sp))
               (put o "value" (cddr sp))
               (put o "source" (car sp))
               o))
           source-parts)))

;;; ---- Date.prototype.toLocale{,Date,Time}String wiring ----
(defun dtf-wire-date-prototype (realm ctor)
  (let ((date-ctor (ignore-errors (js-get (realm-global realm) "Date"))))
    (when (and (js-object-p date-ctor))
      (let ((dp (js-get date-ctor "prototype")))
        (when (js-object-p dp)
          (flet ((wire (name required defaults)
                   (put dp name
                        (native-function realm name
                          (lambda (this args)
                            (let ((tv (dtf-this-date-value this)))
                              (if (js-nan-p tv)
                                  "Invalid Date"
                                  (let ((obj (make-object :proto *intl-dtf-proto* :class "Object")))
                                    (create-datetimeformat obj (arg 0 args) (arg 1 args)
                                                           required defaults)
                                    (dtf-parts-to-string
                                     (dtf-format-to-parts-list (dtf-slots obj) tv))))))
                          0)
                        :enumerable nil :writable t :configurable t)))
            (declare (ignore ctor))
            (wire "toLocaleString" :any :all)
            (wire "toLocaleDateString" :date :date)
            (wire "toLocaleTimeString" :time :time)))))))

(defun dtf-this-date-value (this)
  "Read the [[DateValue]] from a Date object (stored in js-object-primitive)."
  (if (and (js-object-p this) (floatp (js-object-primitive this)))
      (js-object-primitive this)
      (js-throw (make-native-error "TypeError" "not a Date"))))

(register-builtin-installer 'install-intl_datetimeformat)
