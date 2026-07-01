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
          ((:num :str :template :regex) nil)     ; these produce a value -> division
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
    (let ((pattern (subseq src (1+ i) j)))
      (incf j)                                          ; past closing /
      (let ((fstart j))
        (loop while (and (< j n) (id-part-p (char src j))) do (incf j))
        (values pattern (subseq src fstart j) j)))))

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
                              ((#\Newline) nil)
                              (t (when e (write-char e cooked)))))
                          (incf i))
                         (t (write-char ch cooked) (write-char ch raw) (incf i)))))
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
                                        (write-char (code-char (min v #x10FFFF)) out))
                                      (let ((v (hexn 4))) (write-char (code-char (or v (char-code #\u))) out))))
                             ((#\Newline) nil)   ; line continuation: emit nothing
                             (#\Return (when (and (< (1+ i) n) (char= (char src (1+ i)) #\Newline)) (incf i)))
                             (t (write-char e out))))
                         (write-char ch out))
                     (incf i))))
               (incf i) (emit :str (get-output-stream-string out))))
            ;; number (decimal / float / exponent; hex 0x)
            ((or (digit-char-p c) (and (char= c #\.) (digit-char-p (peek 1))))
             (let ((start i))
               (if (and (char= c #\0) (member (peek 1) '(#\x #\X)))
                   (progn (incf i 2) (loop while (and (< i n) (digit-char-p (char src i) 16)) do (incf i)))
                   (progn (loop while (and (< i n) (digit-char-p (char src i))) do (incf i))
                          (when (and (< i n) (char= (char src i) #\.))
                            (incf i) (loop while (and (< i n) (digit-char-p (char src i))) do (incf i)))
                          (when (and (< i n) (member (char src i) '(#\e #\E)))
                            (incf i) (when (member (peek) '(#\+ #\-)) (incf i))
                            (loop while (and (< i n) (digit-char-p (char src i))) do (incf i)))))
               (let ((text (subseq src start i)))
                 (emit :num (if (and (> (length text) 1) (char-equal (char text 1) #\x))
                                (float (parse-integer text :start 2 :radix 16) 1d0)
                                (let ((*read-default-float-format* 'double-float))
                                  (float (read-from-string text) 1d0)))))))
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
                     (js-throw (format nil "Unexpected character ~s" c)))))))))
    (vector-push-extend (cons :eof nil) toks)
    toks))
