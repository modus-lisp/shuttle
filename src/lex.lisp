;;;; lex.lisp — tokenizer. A real subset (numbers, strings, identifiers/keywords,
;;;; operators, punctuation), structured to grow. Tokens: (TYPE . VALUE) where
;;;; TYPE in {:num :str :ident :punct :eof}. (Regex/template/full-ASI: TODO.)
(in-package #:shuttle)

(defparameter *punctuators*
  ;; longest first so the maximal-munch scan matches correctly
  '(">>>=" "===" "!==" "..." ">>>" "**=" "<<=" ">>=" "&&=" "||=" "??=" "?."
    "==" "!=" "<=" ">=" "&&" "||" "??" "**" "=>" "++" "--"
    "+=" "-=" "*=" "/=" "%=" "&=" "|=" "^=" "<<" ">>"
    "+" "-" "*" "/" "%" "<" ">" "=" "(" ")" "{" "}" "[" "]" ";" "," "." ":" "!" "?" "&" "|" "~" "^"))

(defun write-str-char (ch out)
  "Write a single source/literal character CH to the string-output-stream OUT as
   UTF-16 code units: an astral char (code > #xFFFF) — which SBCL read from the
   UTF-8 file as one UCS-4 char — is split into its surrogate pair. A BMP char
   (incl. a lone surrogate) is written verbatim."
  (let ((cc (char-code ch)))
    (if (> cc #xFFFF) (write-string (utf16-encode-cp cc) out) (write-char ch out))))

(defun id-start-p (c) (or (alpha-char-p c) (char= c #\_) (char= c #\$)
                          ;; ID_Start includes a broad Unicode letter range; SBCL's
                          ;; alpha-char-p covers most. Also allow the common
                          ;; Other_ID_Start pair (U+2118, U+212E, U+309B, U+309C).
                          (member (char-code c) '(#x1885 #x1886 #x2118 #x212E #x309B #x309C))))
(defun id-part-p  (c) (or (alphanumericp c) (char= c #\_) (char= c #\$)
                          (id-start-p c)     ; ID_Continue superset of ID_Start
                          ;; ZWNJ / ZWJ and Other_ID_Continue join chars.
                          (member (char-code c) '(#x200C #x200D #x00B7 #x0387 #x1369 #x136A
                                                  #x136B #x136C #x136D #x136E #x136F #x1370
                                                  #x1371 #x19DA))))

(defparameter *reserved-words*
  ;; ReservedWord (keywords + literals); an escaped reserved word is an early error.
  '("break" "case" "catch" "class" "const" "continue" "debugger" "default"
    "delete" "do" "else" "enum" "export" "extends" "false" "finally" "for"
    "function" "if" "import" "in" "instanceof" "new" "null" "return" "super"
    "switch" "this" "throw" "true" "try" "typeof" "var" "void" "while" "with"))
(defun reserved-word-p (s) (member s *reserved-words* :test #'string=))

(defun read-id-escape (src i n)
  "At SRC[i]=#\\\\ starting a `\\u` escape inside an identifier. Returns
   (values CODEPOINT NEXT-I) or (values NIL NIL) if malformed."
  (when (and (< (1+ i) n) (char= (char src (1+ i)) #\u))
    (let ((j (+ i 2)))
      (cond
        ((and (< j n) (char= (char src j) #\{))          ; \u{ HHHH }
         (incf j) (let ((v 0) (any nil))
                    (loop while (and (< j n) (digit-char-p (char src j) 16))
                          do (setf v (+ (* v 16) (digit-char-p (char src j) 16)) any t) (incf j))
                    (if (and any (< j n) (char= (char src j) #\}) (<= v #x10FFFF))
                        (values v (1+ j)) (values nil nil))))
        (t                                                ; \uHHHH
         (let ((v 0))
           (dotimes (_ 4 (values v j))
             (if (and (< j n) (digit-char-p (char src j) 16))
                 (progn (setf v (+ (* v 16) (digit-char-p (char src j) 16))) (incf j))
                 (return-from read-id-escape (values nil nil))))))))))

(defparameter *regex-not-after-keywords*
  ;; identifier tokens after which a `/` is DIVISION, not a regex (they produce a value)
  '("this" "true" "false" "null" "super"))

(defun paren-closes-control-head-p (toks)
  "TOKS' last token is `)`.  Scan back to the matching `(` and return T when that
   parenthesized group is the head of an `if` / `while` / `for` / `with`
   statement — after such a head a statement follows, so a `/` begins a REGEX
   literal, not division (e.g. `if(a)/b/.exec(c)`).  A `)` closing a call or a
   grouping expression produces a value, so `/` there is division."
  (let ((depth 0) (i (1- (fill-pointer toks))))
    (loop
      (when (< i 0) (return nil))
      (let ((tk (aref toks i)))
        (when (eq (car tk) :punct)
          (cond ((string= (cdr tk) ")") (incf depth))
                ((string= (cdr tk) "(")
                 (decf depth)
                 (when (zerop depth)
                   (let ((prev (and (> i 0) (aref toks (1- i)))))
                     (return (and prev (eq (car prev) :ident)
                                  (member (cdr prev) '("if" "while" "for" "with")
                                          :test #'string=)))))))))
      (decf i))))

(defun regex-allowed-p (toks)
  "Given the tokens emitted so far, may a `/` begin a regex literal here?
   Regex is allowed where a value/expression is expected: at start-of-input, and
   after punctuators/keywords that cannot end an expression. Division follows a
   token that produces a value: a number, string, template, regex, most
   identifiers, or a closing `)`/`]`/`}`."
  (if (zerop (fill-pointer toks)) t
      (let* ((tok (aref toks (1- (fill-pointer toks)))) (type (car tok)) (val (cdr tok)))
        (case type
          ((:num :bigint :str :template :regex) nil)     ; these produce a value -> division
          (:ident (cond ((member val *regex-not-after-keywords* :test #'string=) nil)
                        ;; a reserved word that is NOT a value keyword: regex allowed
                        ;; (return, typeof, delete, in, of, case, do, else, yield, void, new, ...)
                        ((member val '("return" "typeof" "instanceof" "in" "of" "new" "delete"
                                       "void" "do" "else" "yield" "case" "throw" "await")
                                 :test #'string=) t)
                        ;; a plain identifier -> value -> division
                        (t nil)))
          (:punct (cond ((string= val ")")
                         ;; `)` is a value closer (division) EXCEPT when it closes an
                         ;; if/while/for/with head, where a statement — hence a regex —
                         ;; follows.
                         (paren-closes-control-head-p toks))
                        ((member val '("]" "}") :test #'string=) nil)   ; value-producing closers
                        (t t)))                  ; other punctuators expect an expression
          (t t)))))

(defun scan-regex (src i n)
  "Scan a regex literal starting at SRC[I] (which is the opening `/`). Returns
   (values PATTERN FLAGS NEW-I) or NIL if it isn't a well-formed regex."
  (let ((j (1+ i)) (in-class nil))
    (loop
      (when (>= j n) (return-from scan-regex nil))    ; unterminated -> not a regex
      (let ((c (char src j)))
        (cond
          ((char= c #\Newline) (return-from scan-regex nil))
          ((char= c #\\)                               ; escape: consume next char
           (incf j) (when (or (>= j n) (char= (char src j) #\Newline)) (return-from scan-regex nil))
           (incf j))
          ((char= c #\[) (setf in-class t) (incf j))
          ((char= c #\]) (setf in-class nil) (incf j))
          ((and (char= c #\/) (not in-class)) (return))  ; end of body
          (t (incf j)))))
    ;; The pattern is source text: an astral char must become its UTF-16
    ;; surrogate pair so the pattern string is code units like every JS string
    ;; (keeps group names / RegExp.source consistent with code-unit replacement
    ;; strings, and lets the matcher advance by code unit).
    (let ((pattern (source->code-units src (1+ i) j)))
      (incf j)                                          ; past closing /
      (let ((fstart j))
        (loop while (and (< j n) (id-part-p (char src j))) do (incf j))
        (values pattern (subseq src fstart j) j)))))

(defun source->code-units (src start end)
  "SUBSEQ of SRC[START:END] with each astral source char split into its UTF-16
   surrogate pair (BMP chars, incl. lone surrogates, pass through)."
  (let ((out (make-string-output-stream)))
    (loop for k from start below end do (write-str-char (char src k) out))
    (get-output-stream-string out)))

(defvar *escaped-idents* nil
  "Hash of token-index -> T for :ident tokens whose spelling contained a unicode
   escape AND is a reserved word. The parser rejects these only in Identifier
   position (not as an IdentifierName). Set per tokenize, read by the parser.")

(defun tokenize (src)
  (let ((i 0) (n (length src)) (toks (make-array 0 :adjustable t :fill-pointer 0))
        (*escaped-idents* (make-hash-table)))
    (labels ((peek (&optional (k 0)) (if (< (+ i k) n) (char src (+ i k)) #\Nul))
             (emit (type val) (vector-push-extend (cons type val) toks)))
      (loop while (< i n) do
        (let ((c (char src i)))
          (cond
            ((member c '(#\Space #\Tab #\Newline #\Return #\Page)) (incf i))
            ;; comments
            ((and (char= c #\/) (char= (peek 1) #\/))
             (loop while (and (< i n) (char/= (char src i) #\Newline)) do (incf i)))
            ((and (char= c #\/) (char= (peek 1) #\*))
             (incf i 2) (loop until (or (>= i n) (and (char= (char src i) #\*) (char= (peek 1) #\/))) do (incf i))
             (incf i 2))
            ;; regex literal  /pattern/flags  (only where a value/expression is expected)
            ((and (char= c #\/) (regex-allowed-p toks))
             (multiple-value-bind (pat flags nj) (scan-regex src i n)
               (if pat
                   (progn (setf i nj) (emit :regex (cons pat flags)))
                   (let ((p (find-if (lambda (p) (and (<= (+ i (length p)) n)
                                                      (string= p src :start2 i :end2 (+ i (length p)))))
                                     *punctuators*)))
                     (emit :punct p) (incf i (length p))))))
            ;; template literal  `...${expr}...`
            ((char= c #\`)
             (incf i)                          ; past opening backtick
             (let ((parts '()))                ; reversed list of (:str cooked raw) / (:expr toks)
               (loop
                 (let ((cooked (make-string-output-stream))
                       (raw (make-string-output-stream)))
                   ;; scan a string chunk until ` , ${ , or EOF
                   (loop
                     (when (>= i n) (js-throw (make-native-error "SyntaxError" "Unterminated template")))
                     (let ((ch (char src i)))
                       (cond
                         ((char= ch #\`) (return))
                         ((and (char= ch #\$) (< (1+ i) n) (char= (char src (1+ i)) #\{)) (return))
                         ((char= ch #\\)
                          (write-char ch raw)
                          (when (< (1+ i) n) (write-char (char src (1+ i)) raw))
                          (let ((e (and (< (1+ i) n) (char src (1+ i)))))
                            (incf i)            ; on the escape char
                            (case e
                              (#\n (write-char #\Newline cooked)) (#\t (write-char #\Tab cooked))
                              (#\r (write-char #\Return cooked))  (#\b (write-char #\Backspace cooked))
                              (#\f (write-char #\Page cooked))    (#\v (write-char (code-char 11) cooked))
                              (#\` (write-char #\` cooked)) (#\$ (write-char #\$ cooked))
                              (#\\ (write-char #\\ cooked))
                              (#\x                       ; \xHH -> one code unit
                               (let ((v 0) (ok t))
                                 (dotimes (_ 2)
                                   (let ((d (and (< (1+ i) n) (digit-char-p (char src (1+ i)) 16))))
                                     (if d (progn (setf v (+ (* v 16) d)) (incf i) (write-char (char src i) raw))
                                         (setf ok nil))))
                                 (write-char (if ok (code-char v) #\x) cooked)))
                              (#\u                       ; \uHHHH or \u{XXXXXX}
                               (if (and (< (1+ i) n) (char= (char src (1+ i)) #\{))
                                   (let ((v 0)) (incf i) (write-char #\{ raw)   ; skip {
                                     (loop for d = (and (< (1+ i) n) (digit-char-p (char src (1+ i)) 16))
                                           while d do (setf v (+ (* v 16) d)) (incf i) (write-char (char src i) raw))
                                     (when (and (< (1+ i) n) (char= (char src (1+ i)) #\}))
                                       (incf i) (write-char #\} raw))
                                     (write-string (utf16-encode-cp (min v #x10FFFF)) cooked))
                                   (let ((v 0) (ok t))
                                     (dotimes (_ 4)
                                       (let ((d (and (< (1+ i) n) (digit-char-p (char src (1+ i)) 16))))
                                         (if d (progn (setf v (+ (* v 16) d)) (incf i) (write-char (char src i) raw))
                                             (setf ok nil))))
                                     (write-char (if ok (code-char v) #\u) cooked))))
                              ((#\Newline) nil)
                              (t (when e (write-str-char e cooked)))))
                          (incf i))
                         (t (write-str-char ch cooked) (write-str-char ch raw) (incf i)))))
                   (push (list :str (get-output-stream-string cooked) (get-output-stream-string raw)) parts))
                 (cond
                   ((char= (char src i) #\`) (incf i) (return))     ; end of template
                   (t ;; ${ expr }
                    (incf i 2)                  ; past ${
                    (let ((depth 1) (start i))
                      (loop
                        (when (>= i n) (js-throw (make-native-error "SyntaxError" "Unterminated template expr")))
                        (let ((ch (char src i)))
                          (cond ((char= ch #\{) (incf depth) (incf i))
                                ((char= ch #\}) (decf depth) (when (zerop depth) (return)) (incf i))
                                (t (incf i)))))
                      (push (list :expr (tokenize (subseq src start i))) parts)
                      (incf i)))))              ; past closing }
               (emit :template (nreverse parts))))
            ;; string
            ((or (char= c #\") (char= c #\'))
             (let ((q c) (out (make-string-output-stream))) (incf i)
               (flet ((hexn (count)  ; read COUNT hex digits starting at i+1; leave i on the last
                        (let ((v 0))
                          (dotimes (_ count)
                            (let ((d (and (< (1+ i) n) (digit-char-p (char src (1+ i)) 16))))
                              (unless d (return-from hexn nil))
                              (setf v (+ (* v 16) d)) (incf i)))
                          v)))
                 (loop until (or (>= i n) (char= (char src i) q)) do
                   (let ((ch (char src i)))
                     (if (char= ch #\\)
                         (let ((e (char src (1+ i))))
                           (incf i)   ; i now on the escape char
                           (case e
                             (#\n (write-char #\Newline out)) (#\t (write-char #\Tab out))
                             (#\r (write-char #\Return out))  (#\b (write-char #\Backspace out))
                             (#\f (write-char #\Page out))    (#\v (write-char (code-char 11) out))
                             ;; \0 not followed by a digit -> NUL. \0-\7 followed by
                             ;; octal digits -> LegacyOctalEscapeSequence (Annex B B.1.2,
                             ;; sloppy). \8 \9 -> the digit itself (NonOctalDecimalEscape).
                             ((#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7)
                              (let* ((d0 (- (char-code e) (char-code #\0)))
                                     (val d0)
                                     ;; max digits: \0-\3 allow up to 3, \4-\7 up to 2
                                     (maxmore (if (<= d0 3) 2 1)))
                                (loop repeat maxmore
                                      while (and (< (1+ i) n)
                                                 (char<= #\0 (char src (1+ i)) #\7))
                                      do (setf val (+ (* val 8) (- (char-code (char src (1+ i))) (char-code #\0))))
                                         (incf i))
                                (write-char (code-char val) out)))
                             ((#\8 #\9) (write-char e out))    ; NonOctalDecimalEscapeSequence
                             (#\x (let ((v (hexn 2))) (write-char (code-char (or v (char-code #\x))) out)))
                             (#\u (if (and (< (1+ i) n) (char= (char src (1+ i)) #\{))
                                      (let ((v 0)) (incf i)   ; skip {
                                        (loop for d = (and (< (1+ i) n) (digit-char-p (char src (1+ i)) 16))
                                              while d do (setf v (+ (* v 16) d)) (incf i))
                                        (when (and (< (1+ i) n) (char= (char src (1+ i)) #\})) (incf i))
                                        ;; \u{XXXXXX}: astral scalar -> surrogate pair
                                        (write-string (utf16-encode-cp (min v #x10FFFF)) out))
                                      ;; \uXXXX: one code unit verbatim (may be a lone surrogate)
                                      (let ((v (hexn 4))) (write-char (code-char (or v (char-code #\u))) out))))
                             ((#\Newline) nil)   ; line continuation: emit nothing
                             (#\Return (when (and (< (1+ i) n) (char= (char src (1+ i)) #\Newline)) (incf i)))
                             (t (write-str-char e out))))
                         (write-str-char ch out))
                     (incf i))))
               (incf i) (emit :str (get-output-stream-string out))))
            ;; number (decimal / float / exponent; radix 0x/0o/0b) + BigInt `n` suffix
            ((or (digit-char-p c) (and (char= c #\.) (digit-char-p (peek 1))))
             (let ((start i)
                   (radix nil)        ; 16/8/2 for a 0x/0o/0b literal, else nil
                   (has-dot nil) (has-exp nil))
               (cond
                 ((and (char= c #\0) (member (peek 1) '(#\x #\X)))
                  (setf radix 16) (incf i 2)
                  (loop while (and (< i n) (or (digit-char-p (char src i) 16) (char= (char src i) #\_))) do (incf i)))
                 ((and (char= c #\0) (member (peek 1) '(#\o #\O)))
                  (setf radix 8) (incf i 2)
                  (loop while (and (< i n) (or (digit-char-p (char src i) 8) (char= (char src i) #\_))) do (incf i)))
                 ((and (char= c #\0) (member (peek 1) '(#\b #\B)))
                  (setf radix 2) (incf i 2)
                  (loop while (and (< i n) (or (digit-char-p (char src i) 2) (char= (char src i) #\_))) do (incf i)))
                 (t
                  (loop while (and (< i n) (or (digit-char-p (char src i)) (char= (char src i) #\_))) do (incf i))
                  (when (and (< i n) (char= (char src i) #\.))
                    (setf has-dot t) (incf i)
                    (loop while (and (< i n) (or (digit-char-p (char src i)) (char= (char src i) #\_))) do (incf i)))
                  (when (and (< i n) (member (char src i) '(#\e #\E)))
                    (setf has-exp t) (incf i) (when (member (peek) '(#\+ #\-)) (incf i))
                    (loop while (and (< i n) (or (digit-char-p (char src i)) (char= (char src i) #\_))) do (incf i)))))
               ;; A radix prefix with no digits (0x / 0o / 0b) is malformed.
               (when (and radix (= i (+ start 2)))
                 (js-throw (make-native-error "SyntaxError" "Missing digits after radix prefix")))
               ;; BigInt literal: a trailing `n`. Only on integer syntax
               ;; (no `.`/exponent, no legacy-octal like 0123n) — else SyntaxError.
               (let ((bigint (and (< i n) (char= (char src i) #\n)))
                     (text (subseq src start i)))
                 ;; numeric separators: each `_` must sit between two radix digits
                 (when (find #\_ text)
                   (let ((rdx (or radix 10)))
                     (dotimes (j (length text))
                       (when (char= (char text j) #\_)
                         (unless (and (> j 0) (< (1+ j) (length text))
                                      (digit-char-p (char text (1- j)) rdx)
                                      (digit-char-p (char text (1+ j)) rdx))
                           (js-throw (make-native-error "SyntaxError" "Invalid numeric separator")))))
                     (setf text (remove #\_ text))))
                 (if bigint
                     (progn
                       (incf i)
                       (when (or has-dot has-exp)
                         (js-throw (make-native-error "SyntaxError" "Invalid BigInt literal")))
                       ;; legacy non-radix leading-zero (0123) is disallowed with `n`
                       (when (and (null radix) (> (length text) 1) (char= (char text 0) #\0))
                         (js-throw (make-native-error "SyntaxError" "Invalid BigInt literal"))))
                     nil)
                 ;; A numeric literal may not be immediately followed by an
                 ;; IdentifierStart or DecimalDigit (e.g. 0b2n, 3in, 1.2.3).
                 (when (and (< i n)
                            (let ((nc (char src i))) (or (id-start-p nc) (digit-char-p nc))))
                   (js-throw (make-native-error "SyntaxError" "Unexpected character after numeric literal")))
                 (if bigint
                     (emit :bigint
                           (if radix (parse-integer text :start 2 :radix radix)
                               (parse-integer text)))
                     (emit :num
                           (cond
                             ((eql radix 16) (float (parse-integer text :start 2 :radix 16) 1d0))
                             ((eql radix 8)  (float (parse-integer text :start 2 :radix 8) 1d0))
                             ((eql radix 2)  (float (parse-integer text :start 2 :radix 2) 1d0))
                             ;; Correctly-rounded decimal->double via an exact
                             ;; rational (right across subnormals, where the reader
                             ;; mis-rounds). Overflow (e.g. 1E+309) -> Infinity.
                             (t (with-js-floats
                                  (let ((r (decimal-string->rational text)))
                                    (if (null r) 0d0 (rational->double r)))))))))))
            ;; identifier / keyword  (also #private-name as a lexeme). An identifier
            ;; may open with, or contain, a \uHHHH / \u{..} unicode escape whose
            ;; decoded code point is a valid ID_Start / ID_Continue char.
            ((or (id-start-p c)
                 (and (char= c #\#) (< (1+ i) n)
                      (or (id-start-p (char src (1+ i))) (char= (char src (1+ i)) #\\)))
                 (and (char= c #\\)
                      (multiple-value-bind (cp ni) (read-id-escape src i n)
                        (and cp (id-start-p (code-char cp)) ni))))
             (let ((buf (make-string-output-stream)) (escaped nil))
               (when (char= c #\#) (write-char #\# buf) (incf i))
               ;; first char (start): plain or escaped
               (if (char= (char src i) #\\)
                   (multiple-value-bind (cp ni) (read-id-escape src i n)
                     (unless (and cp (id-start-p (code-char cp)))
                       (js-throw (make-native-error "SyntaxError" "Invalid identifier escape")))
                     (write-str-char (code-char cp) buf) (setf i ni escaped t))
                   (progn (write-char (char src i) buf) (incf i)))
               ;; continuation chars
               (loop while (< i n) do
                 (let ((ch (char src i)))
                   (cond
                     ((id-part-p ch) (write-char ch buf) (incf i))
                     ((char= ch #\\)
                      (multiple-value-bind (cp ni) (read-id-escape src i n)
                        (unless (and cp (id-part-p (code-char cp)))
                          (js-throw (make-native-error "SyntaxError" "Invalid identifier escape")))
                        (write-str-char (code-char cp) buf) (setf i ni escaped t)))
                     (t (return)))))
               (let ((name (get-output-stream-string buf)))
                 ;; An escaped reserved word is an early SyntaxError ONLY where an
                 ;; Identifier is required (binding / reference) — NOT as an
                 ;; IdentifierName (property access `x.if`, object key, method
                 ;; name), where any keyword spelling is legal. We can't distinguish
                 ;; here, so record the escape on a parallel position map; the parser
                 ;; rejects an escaped reserved word only in Identifier position.
                 (when (and escaped (reserved-word-p name))
                   (setf (gethash (fill-pointer toks) *escaped-idents*) t))
                 (emit :ident name))))
            ;; punctuator (maximal munch)
            (t (let ((p (find-if (lambda (p) (and (<= (+ i (length p)) n)
                                                  (string= p src :start2 i :end2 (+ i (length p)))
                                                  ;; `?.` only when NOT followed by a digit (else it's `? .5`)
                                                  (not (and (string= p "?.")
                                                            (< (+ i 2) n) (digit-char-p (char src (+ i 2)))))))
                                 *punctuators*)))
                 (if p (progn (emit :punct p) (incf i (length p)))
                     (js-throw (make-native-error "SyntaxError" (format nil "Unexpected character ~s" c))))))))))
    (vector-push-extend (cons :eof nil) toks)
    (values toks *escaped-idents*)))
