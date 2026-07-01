;;;; lex.lisp — tokenizer. A real subset (numbers, strings, identifiers/keywords,
;;;; operators, punctuation), structured to grow. Tokens: (TYPE . VALUE) where
;;;; TYPE in {:num :str :ident :punct :eof}. (Regex/template/full-ASI: TODO.)
(in-package #:shuttle)

(defparameter *punctuators*
  ;; longest first so the maximal-munch scan matches correctly
  '("===" "!==" "..." ">>>" "==" "!=" "<=" ">=" "&&" "||" "=>" "++" "--"
    "+=" "-=" "*=" "/=" "%=" "<<" ">>"
    "+" "-" "*" "/" "%" "<" ">" "=" "(" ")" "{" "}" "[" "]" ";" "," "." ":" "!" "?" "&" "|" "~" "^"))

(defun id-start-p (c) (or (alpha-char-p c) (char= c #\_) (char= c #\$)))
(defun id-part-p  (c) (or (alphanumericp c) (char= c #\_) (char= c #\$)))

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
            ;; identifier / keyword
            ((id-start-p c)
             (let ((start i)) (loop while (and (< i n) (id-part-p (char src i))) do (incf i))
               (emit :ident (subseq src start i))))
            ;; punctuator (maximal munch)
            (t (let ((p (find-if (lambda (p) (and (<= (+ i (length p)) n)
                                                  (string= p src :start2 i :end2 (+ i (length p)))))
                                 *punctuators*)))
                 (if p (progn (emit :punct p) (incf i (length p)))
                     (js-throw (format nil "Unexpected character ~s" c)))))))))
    (vector-push-extend (cons :eof nil) toks)
    toks))
