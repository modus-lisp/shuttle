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

(defun id-start-p (c) (or (alpha-char-p c) (char= c #\_) (char= c #\$)))
(defun id-part-p  (c) (or (alphanumericp c) (char= c #\_) (char= c #\$)))

(defparameter *regex-not-after-keywords*
  ;; identifier tokens after which a `/` is DIVISION, not a regex (they produce a value)
  '("this" "true" "false" "null" "super"))

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
          (:punct (cond ((member val '(")" "]" "}") :test #'string=) nil)   ; value-producing closers
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

(defun tokenize (src)
  (let ((i 0) (n (length src)) (toks (make-array 0 :adjustable t :fill-pointer 0)))
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
                             (#\0 (if (and (< (1+ i) n) (digit-char-p (char src (1+ i))))
                                      (write-char #\0 out) (write-char #\Nul out)))
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
                  (loop while (and (< i n) (digit-char-p (char src i) 16)) do (incf i)))
                 ((and (char= c #\0) (member (peek 1) '(#\o #\O)))
                  (setf radix 8) (incf i 2)
                  (loop while (and (< i n) (digit-char-p (char src i) 8)) do (incf i)))
                 ((and (char= c #\0) (member (peek 1) '(#\b #\B)))
                  (setf radix 2) (incf i 2)
                  (loop while (and (< i n) (digit-char-p (char src i) 2)) do (incf i)))
                 (t
                  (loop while (and (< i n) (digit-char-p (char src i))) do (incf i))
                  (when (and (< i n) (char= (char src i) #\.))
                    (setf has-dot t) (incf i)
                    (loop while (and (< i n) (digit-char-p (char src i))) do (incf i)))
                  (when (and (< i n) (member (char src i) '(#\e #\E)))
                    (setf has-exp t) (incf i) (when (member (peek) '(#\+ #\-)) (incf i))
                    (loop while (and (< i n) (digit-char-p (char src i))) do (incf i)))))
               ;; A radix prefix with no digits (0x / 0o / 0b) is malformed.
               (when (and radix (= i (+ start 2)))
                 (js-throw (make-native-error "SyntaxError" "Missing digits after radix prefix")))
               ;; BigInt literal: a trailing `n`. Only on integer syntax
               ;; (no `.`/exponent, no legacy-octal like 0123n) — else SyntaxError.
               (let ((bigint (and (< i n) (char= (char src i) #\n)))
                     (text (subseq src start i)))
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
            ;; identifier / keyword  (also #private-name as a lexeme)
            ((or (id-start-p c) (and (char= c #\#) (< (1+ i) n) (id-start-p (char src (1+ i)))))
             (let ((start i)) (when (char= c #\#) (incf i))
               (loop while (and (< i n) (id-part-p (char src i))) do (incf i))
               (emit :ident (subseq src start i))))
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
    toks))
