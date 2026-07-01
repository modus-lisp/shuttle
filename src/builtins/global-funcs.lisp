;;;; See array-iteration.lisp for the convention + helpers.
(in-package #:shuttle)

;;; ---------------------------------------------------------------------------
;;; Character-set predicates (per ECMA-262 URI handling, sec. 6.1.4 / Annex B)
;;; ---------------------------------------------------------------------------
(defun uri-alphanum-p (ch)
  (let ((c (char-code ch)))
    (or (<= (char-code #\A) c (char-code #\Z))
        (<= (char-code #\a) c (char-code #\z))
        (<= (char-code #\0) c (char-code #\9)))))

;; uriMark: - _ . ! ~ * ' ( )
;; encodeURIComponent leaves: alphanum + uriMark
(defun uri-component-unescaped-p (ch)
  (or (uri-alphanum-p ch)
      (member ch '(#\- #\_ #\. #\! #\~ #\* #\' #\( #\)) :test #'char=)))

;; uriReserved: ; / ? : @ & = + $ , #   (# added: uriUnescaped = uriReserved + # + uriAlpha + DecimalDigit + uriMark)
;; encodeURI leaves: alphanum + uriMark + uriReserved + #
(defun uri-uri-unescaped-p (ch)
  (or (uri-component-unescaped-p ch)
      (member ch '(#\; #\/ #\? #\: #\@ #\& #\= #\+ #\$ #\, #\#) :test #'char=)))

;;; ---------------------------------------------------------------------------
;;; encode: percent-encode UTF-8 bytes of chars for which UNESCAPED-P is false
;;; ---------------------------------------------------------------------------
(defun %uri-encode (str unescaped-p)
  (let ((out (make-string-output-stream))
        (n (length str)) (i 0))
    (loop while (< i n) do
      (let* ((ch (char str i)) (cp (char-code ch)))
        (cond
          ((funcall unescaped-p ch) (write-char ch out) (incf i))
          ;; lone surrogate -> URIError
          ((<= #xD800 cp #xDBFF)
           ;; high surrogate: must be followed by a low surrogate
           (if (and (< (1+ i) n)
                    (<= #xDC00 (char-code (char str (1+ i))) #xDFFF))
               (let* ((lo (char-code (char str (1+ i))))
                      (combined (+ #x10000 (* (- cp #xD800) #x400) (- lo #xDC00))))
                 (%uri-write-utf8 combined out)
                 (incf i 2))
               (js-throw (make-native-error "URIError" "URI malformed"))))
          ((<= #xDC00 cp #xDFFF)
           ;; lone low surrogate
           (js-throw (make-native-error "URIError" "URI malformed")))
          (t (%uri-write-utf8 cp out) (incf i)))))
    (get-output-stream-string out)))

(defun %uri-write-utf8 (cp out)
  "Write the UTF-8 bytes of code point CP as %XX (uppercase) sequences."
  (dolist (b (%cp-to-utf8-bytes cp))
    (write-char #\% out)
    (write-char (char-upcase (digit-char (ash b -4) 16)) out)
    (write-char (char-upcase (digit-char (logand b #x0F) 16)) out)))

(defun %cp-to-utf8-bytes (cp)
  "UTF-8 encode a single code point into a list of bytes."
  (cond
    ((< cp #x80) (list cp))
    ((< cp #x800)
     (list (logior #xC0 (ash cp -6))
           (logior #x80 (logand cp #x3F))))
    ((< cp #x10000)
     (list (logior #xE0 (ash cp -12))
           (logior #x80 (logand (ash cp -6) #x3F))
           (logior #x80 (logand cp #x3F))))
    (t
     (list (logior #xF0 (ash cp -18))
           (logior #x80 (logand (ash cp -12) #x3F))
           (logior #x80 (logand (ash cp -6) #x3F))
           (logior #x80 (logand cp #x3F))))))

;;; ---------------------------------------------------------------------------
;;; decode: parse %XX -> UTF-8 bytes -> chars.  RESERVED-SET holds the *chars*
;;; that decodeURI must leave escaped (their %XX left verbatim).
;;; ---------------------------------------------------------------------------
(defun %hex-digit (ch)
  (digit-char-p ch 16))

(defun %uri-decode (str reserved-set)
  (let ((out (make-string-output-stream))
        (n (length str)) (i 0))
    (flet ((bad () (js-throw (make-native-error "URIError" "URI malformed"))))
      (loop while (< i n) do
        (let ((ch (char str i)))
          (if (char/= ch #\%)
              (progn (write-char ch out) (incf i))
              ;; %XX ...
              (progn
                (when (> (+ i 3) n) (bad))
                (let ((h1 (%hex-digit (char str (1+ i))))
                      (h2 (%hex-digit (char str (+ i 2)))))
                  (unless (and h1 h2) (bad))
                  (let ((b (+ (* 16 h1) h2)))
                    (if (< b #x80)
                        ;; single ASCII byte
                        (let ((c (code-char b)))
                          (if (and reserved-set (member c reserved-set :test #'char=))
                              ;; leave escaped verbatim (all 3 chars)
                              (progn (write-string (subseq str i (+ i 3)) out) (incf i 3))
                              (progn (write-char c out) (incf i 3))))
                        ;; multi-byte UTF-8: determine length from lead byte
                        (let ((nbytes (cond ((<= #xC0 b #xDF) 2)
                                            ((<= #xE0 b #xEF) 3)
                                            ((<= #xF0 b #xF7) 4)
                                            (t (bad)))))
                          (let ((bytes (make-array nbytes :element-type '(unsigned-byte 8))))
                            (setf (aref bytes 0) b)
                            (let ((j (+ i 3)))
                              (dotimes (k (1- nbytes))
                                (when (> (+ j 3) n) (bad))
                                (unless (char= (char str j) #\%) (bad))
                                (let ((g1 (%hex-digit (char str (1+ j))))
                                      (g2 (%hex-digit (char str (+ j 2)))))
                                  (unless (and g1 g2) (bad))
                                  (let ((cb (+ (* 16 g1) g2)))
                                    (unless (<= #x80 cb #xBF) (bad))
                                    (setf (aref bytes (1+ k)) cb)))
                                (incf j 3))
                              ;; decode the byte block; invalid UTF-8 -> URIError
                              (let ((decoded
                                      (handler-case
                                          (sb-ext:octets-to-string bytes :external-format :utf-8)
                                        (error () (bad)))))
                                ;; reject overlong / invalid that decoded to replacement or empty
                                (when (or (zerop (length decoded))
                                          (find (code-char #xFFFD) decoded))
                                  (bad))
                                (write-string decoded out)
                                (setf i j)))))))))))))
    (get-output-stream-string out)))

;;; ---------------------------------------------------------------------------
;;; escape / unescape (Annex B B.2.1)
;;; escape leaves: alphanum + @ * _ + - . /
;;; ---------------------------------------------------------------------------
(defun %escape-unescaped-p (ch)
  (or (uri-alphanum-p ch)
      (member ch '(#\@ #\* #\_ #\+ #\- #\. #\/) :test #'char=)))

(defun %escape-write-u4 (unit out)
  "Write %uXXXX for a 16-bit code UNIT."
  (write-string "%u" out)
  (loop for shift from 12 downto 0 by 4
        do (write-char (char-upcase (digit-char (logand (ash unit (- shift)) #xF) 16)) out)))

(defun %escape (str)
  (let ((out (make-string-output-stream)))
    (loop for ch across str do
      (let ((cp (char-code ch)))
        (cond
          ((%escape-unescaped-p ch) (write-char ch out))
          ;; escape works on UTF-16 code units. Our string layer may hand back a
          ;; single UCS-4 char for an astral code point; split it into the
          ;; surrogate pair the spec sees.
          ((> cp #xFFFF)
           (let ((v (- cp #x10000)))
             (%escape-write-u4 (+ #xD800 (ash v -10)) out)
             (%escape-write-u4 (+ #xDC00 (logand v #x3FF)) out)))
          ((> cp #xFF) (%escape-write-u4 cp out))
          (t
           (write-char #\% out)
           (write-char (char-upcase (digit-char (ash cp -4) 16)) out)
           (write-char (char-upcase (digit-char (logand cp #xF) 16)) out)))))
    (get-output-stream-string out)))

(defun %unescape (str)
  (let ((out (make-string-output-stream))
        (n (length str)) (i 0))
    (loop while (< i n) do
      (let ((ch (char str i)))
        (cond
          ;; %uXXXX
          ((and (char= ch #\%) (>= n (+ i 6))
                (char= (char str (1+ i)) #\u)
                (%hex-digit (char str (+ i 2))) (%hex-digit (char str (+ i 3)))
                (%hex-digit (char str (+ i 4))) (%hex-digit (char str (+ i 5))))
           (let ((code (+ (* #x1000 (%hex-digit (char str (+ i 2))))
                          (* #x100  (%hex-digit (char str (+ i 3))))
                          (* #x10   (%hex-digit (char str (+ i 4))))
                          (%hex-digit (char str (+ i 5))))))
             (write-char (code-char code) out)
             (incf i 6)))
          ;; %XX
          ((and (char= ch #\%) (>= n (+ i 3))
                (%hex-digit (char str (1+ i))) (%hex-digit (char str (+ i 2))))
           (let ((code (+ (* #x10 (%hex-digit (char str (1+ i))))
                          (%hex-digit (char str (+ i 2))))))
             (write-char (code-char code) out)
             (incf i 3)))
          (t (write-char ch out) (incf i)))))
    (get-output-stream-string out)))

;;; ---------------------------------------------------------------------------
;;; Installer
;;; ---------------------------------------------------------------------------
;; decodeURI must NOT decode escapes that encode reserved chars: ; / ? : @ & = + $ , #
;; (uriReserved + "#"); everything else decodes.
(defparameter +uri-reserved-plus-hash+
  '(#\; #\/ #\? #\: #\@ #\& #\= #\+ #\$ #\, #\#))

(defun install-global-funcs (realm)
  ;; Global function properties are { writable:true, enumerable:false,
  ;; configurable:true } (like all built-ins). define-global's plain put would
  ;; leave them enumerable, so put with explicit attributes and also declare the
  ;; binding in the global env so the name resolves as an identifier.
  (flet ((defg (name len fn)
           (let ((f (native-function realm name fn len)))
             (env-declare (realm-global-env realm) name f)
             (put (realm-global realm) name f :enumerable nil :writable t :configurable t)
             f)))
    (defg "encodeURI" 1
      (lambda (this args) (declare (ignore this))
        (%uri-encode (to-string (arg 0 args)) #'uri-uri-unescaped-p)))
    (defg "encodeURIComponent" 1
      (lambda (this args) (declare (ignore this))
        (%uri-encode (to-string (arg 0 args)) #'uri-component-unescaped-p)))
    (defg "decodeURI" 1
      (lambda (this args) (declare (ignore this))
        (%uri-decode (to-string (arg 0 args)) +uri-reserved-plus-hash+)))
    (defg "decodeURIComponent" 1
      (lambda (this args) (declare (ignore this))
        (%uri-decode (to-string (arg 0 args)) nil)))
    (defg "escape" 1
      (lambda (this args) (declare (ignore this))
        (%escape (to-string (arg 0 args)))))
    (defg "unescape" 1
      (lambda (this args) (declare (ignore this))
        (%unescape (to-string (arg 0 args)))))))

(register-builtin-installer 'install-global-funcs)
