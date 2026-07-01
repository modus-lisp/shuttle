;;;; See array-iteration.lisp for the convention + available helpers.
(in-package #:shuttle)

;;; ===========================================================================
;;; JSON.parse — recursive-descent parser + reviver walk
;;; ===========================================================================

(defstruct (jparse (:constructor %make-jparse)) str pos len)

(defun json-syntax-error (msg)
  (js-throw (make-native-error "SyntaxError" msg)))

(defun jp-peek (p)
  (if (< (jparse-pos p) (jparse-len p)) (char (jparse-str p) (jparse-pos p)) nil))

(defun jp-next (p)
  (prog1 (char (jparse-str p) (jparse-pos p)) (incf (jparse-pos p))))

(defun jp-eof-p (p) (>= (jparse-pos p) (jparse-len p)))

(defun json-ws-char-p (c)
  ;; JSON whitespace: space, tab, LF, CR only.
  (or (char= c #\Space) (char= c #\Tab) (char= c #\Newline) (char= c #\Return)))

(defun jp-skip-ws (p)
  (loop while (and (not (jp-eof-p p)) (json-ws-char-p (jp-peek p)))
        do (incf (jparse-pos p))))

(defun jp-expect (p ch)
  (if (and (not (jp-eof-p p)) (char= (jp-peek p) ch))
      (incf (jparse-pos p))
      (json-syntax-error (format nil "Expected '~a' in JSON" ch))))

(defun json-parse-value (p)
  (jp-skip-ws p)
  (when (jp-eof-p p) (json-syntax-error "Unexpected end of JSON input"))
  (let ((c (jp-peek p)))
    (cond
      ((char= c #\{) (json-parse-object p))
      ((char= c #\[) (json-parse-array p))
      ((char= c #\") (json-parse-string p))
      ((char= c #\-) (json-parse-number p))
      ((digit-char-p c) (json-parse-number p))
      ((char= c #\t) (json-parse-lit p "true" *true*))
      ((char= c #\f) (json-parse-lit p "false" *false*))
      ((char= c #\n) (json-parse-lit p "null" *null*))
      (t (json-syntax-error (format nil "Unexpected token ~a in JSON" c))))))

(defun json-parse-lit (p word val)
  (let ((n (length word)))
    (when (> (+ (jparse-pos p) n) (jparse-len p))
      (json-syntax-error "Unexpected end of JSON input"))
    (unless (string= (jparse-str p) word :start1 (jparse-pos p) :end1 (+ (jparse-pos p) n))
      (json-syntax-error "Unexpected token in JSON"))
    (incf (jparse-pos p) n)
    val))

(defun json-parse-string (p)
  (jp-expect p #\")
  (let ((out (make-string-output-stream)))
    (loop
      (when (jp-eof-p p) (json-syntax-error "Unterminated string in JSON"))
      (let ((c (jp-next p)))
        (cond
          ((char= c #\") (return (get-output-stream-string out)))
          ((char= c #\\)
           (when (jp-eof-p p) (json-syntax-error "Unterminated string in JSON"))
           (let ((e (jp-next p)))
             (case e
               (#\" (write-char #\" out))
               (#\\ (write-char #\\ out))
               (#\/ (write-char #\/ out))
               (#\b (write-char #\Backspace out))
               (#\f (write-char #\Page out))
               (#\n (write-char #\Newline out))
               (#\r (write-char #\Return out))
               (#\t (write-char #\Tab out))
               (#\u (write-char (json-parse-unicode-escape p) out))
               (t (json-syntax-error (format nil "Bad escape \\~a in JSON" e))))))
          ((< (char-code c) #x20)
           (json-syntax-error "Bad control character in JSON string"))
          (t (write-char c out)))))))

(defun json-parse-unicode-escape (p)
  (when (> (+ (jparse-pos p) 4) (jparse-len p))
    (json-syntax-error "Bad Unicode escape in JSON"))
  (let ((code 0))
    (dotimes (i 4)
      (let ((d (digit-char-p (jp-next p) 16)))
        (unless d (json-syntax-error "Bad Unicode escape in JSON"))
        (setf code (+ (* code 16) d))))
    (code-char code)))

(defun json-parse-number (p)
  (let ((start (jparse-pos p)) (str (jparse-str p)) (len (jparse-len p)))
    (labels ((cur () (if (< (jparse-pos p) len) (char str (jparse-pos p)) nil))
             (adv () (incf (jparse-pos p)))
             (digits ()
               (let ((got nil))
                 (loop for c = (cur) while (and c (digit-char-p c)) do (adv) (setf got t))
                 got)))
      ;; sign
      (when (eql (cur) #\-) (adv))
      ;; int part: 0 or [1-9] digits
      (let ((c (cur)))
        (cond ((null c) (json-syntax-error "Unexpected end of JSON input"))
              ((char= c #\0) (adv))
              ((digit-char-p c) (digits))
              (t (json-syntax-error "Bad number in JSON"))))
      ;; fraction
      (when (eql (cur) #\.)
        (adv)
        (unless (digits) (json-syntax-error "Bad number in JSON")))
      ;; exponent
      (let ((c (cur)))
        (when (and c (or (char= c #\e) (char= c #\E)))
          (adv)
          (let ((s (cur))) (when (and s (or (char= s #\+) (char= s #\-))) (adv)))
          (unless (digits) (json-syntax-error "Bad number in JSON"))))
      (let ((token (subseq str start (jparse-pos p))))
        (or (parse-js-decimal token)
            (json-syntax-error "Bad number in JSON"))))))

(defun json-parse-array (p)
  (jp-expect p #\[)
  (jp-skip-ws p)
  (let ((elems '()))
    (when (eql (jp-peek p) #\])
      (incf (jparse-pos p))
      (return-from json-parse-array (make-array-object '())))
    (loop
      (push (json-parse-value p) elems)
      (jp-skip-ws p)
      (let ((c (jp-peek p)))
        (cond ((null c) (json-syntax-error "Unexpected end of JSON input"))
              ((char= c #\,) (incf (jparse-pos p)))
              ((char= c #\]) (incf (jparse-pos p)) (return))
              (t (json-syntax-error "Expected ',' or ']' in JSON")))))
    (make-array-object (nreverse elems))))

(defun json-parse-object (p)
  (jp-expect p #\{)
  (jp-skip-ws p)
  (let ((o (make-object :proto (realm-object-proto (symbol-value '*current-realm*)))))
    (when (eql (jp-peek p) #\})
      (incf (jparse-pos p))
      (return-from json-parse-object o))
    (loop
      (jp-skip-ws p)
      (unless (eql (jp-peek p) #\")
        (json-syntax-error "Expected string key in JSON"))
      (let ((key (json-parse-string p)))
        (jp-skip-ws p)
        (jp-expect p #\:)
        (let ((val (json-parse-value p)))
          ;; CreateDataProperty semantics: last one wins, enumerable/writable/configurable.
          (put o key val)))
      (jp-skip-ws p)
      (let ((c (jp-peek p)))
        (cond ((null c) (json-syntax-error "Unexpected end of JSON input"))
              ((char= c #\,) (incf (jparse-pos p)))
              ((char= c #\}) (incf (jparse-pos p)) (return))
              (t (json-syntax-error "Expected ',' or '}' in JSON")))))
    o))

(defun internalize-json-property (realm holder name reviver)
  "InternalizeJSONProperty: post-order walk applying REVIVER."
  (let ((val (js-get holder name)))
    (when (js-object-p val)
      (if (js-array-p val)
          (let ((len (to-int-index (js-get val "length"))))
            (dotimes (i len)
              (let* ((k (princ-to-string i))
                     (new (internalize-json-property realm val k reviver)))
                (if (js-undefined-p new)
                    (js-delete val k)
                    (js-define-own-property val k
                      (list :value new :writable t :enumerable t :configurable t))))))
          (dolist (k (remove-if-not #'stringp (enumerable-own-keys val :key)))
            (let ((new (internalize-json-property realm val k reviver)))
              (if (js-undefined-p new)
                  (js-delete val k)
                  (js-define-own-property val k
                    (list :value new :writable t :enumerable t :configurable t)))))))
    (js-call reviver holder (list name val))))

;;; ===========================================================================
;;; JSON.stringify
;;; ===========================================================================

(defstruct (jstate (:constructor %make-jstate))
  realm stack indent gap (replacer-fn nil) (prop-list nil) (has-prop-list nil))

(defun json-quote (str)
  "Serialize a string as a JSON string literal (QuoteJSONString)."
  (let ((out (make-string-output-stream)))
    (write-char #\" out)
    (loop for c across str
          for code = (char-code c) do
      (cond
        ((char= c #\") (write-string "\\\"" out))
        ((char= c #\\) (write-string "\\\\" out))
        ((char= c #\Backspace) (write-string "\\b" out))
        ((char= c #\Page) (write-string "\\f" out))
        ((char= c #\Newline) (write-string "\\n" out))
        ((char= c #\Return) (write-string "\\r" out))
        ((char= c #\Tab) (write-string "\\t" out))
        ((< code #x20)
         (format out "\\u~(~4,'0x~)" code))
        (t (write-char c out))))
    (write-char #\" out)
    (get-output-stream-string out)))

(defun json-plain-box-p (box method)
  "True when BOX carries a primitive slot and has NOT overridden its coercion
   METHOD (\"toString\"/\"valueOf\") nor @@toPrimitive as an own property."
  (and (not (null (js-object-primitive box)))
       (null (js-get-own-property box method))
       (null (js-get-own-property box "valueOf"))
       (null (js-get-own-property box "toString"))
       (or (null *symbol-to-primitive*)
           (null (js-get-own-property box *symbol-to-primitive*)))))

(defun json-serialize-property (st holder key)
  "SerializeJSONProperty: returns a JSON string or NIL (omit)."
  (let ((value (js-get holder key)))
    ;; toJSON — only for values that can carry properties (objects + boxable
    ;; primitives). Getting toJSON must propagate abrupt completions.
    (when (or (js-object-p value) (stringp value) (floatp value)
              (eq value *true*) (eq value *false*) (js-symbol-p value))
      (let ((tj (js-get value "toJSON")))
        (when (js-callable-p tj)
          (setf value (js-call tj value (list key))))))
    ;; replacer function
    (when (jstate-replacer-fn st)
      (setf value (js-call (jstate-replacer-fn st) holder (list key value))))
    ;; unwrap primitive wrapper objects (Number/String/Boolean boxes).
    ;; Per spec this is ToNumber / ToString; when a box carries an unmodified
    ;; [[NumberData]]/[[StringData]] slot we read it directly (the coercion path
    ;; would loop for plain boxes), but if the box overrides valueOf/toString we
    ;; run the real coercion so abrupt completions surface.
    (when (js-object-p value)
      (let ((cls (js-object-class value)))
        (cond ((string= cls "Number")
               (setf value (if (json-plain-box-p value "valueOf")
                               (js-object-primitive value)
                               (to-number value))))
              ((string= cls "String")
               (setf value (if (json-plain-box-p value "toString")
                               (js-object-primitive value)
                               (to-string value))))
              ((string= cls "Boolean")
               (setf value (js-object-primitive value))))))
    (cond
      ((eq value *null*) "null")
      ((eq value *true*) "true")
      ((eq value *false*) "false")
      ((stringp value) (json-quote value))
      ((floatp value)
       (if (or (js-nan-p value) (= value *inf*) (= value *-inf*)) "null"
           (number-to-string value)))
      ((js-symbol-p value) nil)
      ((and (js-object-p value) (not (js-callable-p value)))
       (if (js-array-p value)
           (json-serialize-array st value)
           (json-serialize-object st value)))
      ;; undefined, function, or leftover
      (t nil))))

(defun json-check-cycle (st value)
  (when (member value (jstate-stack st) :test #'eq)
    (js-throw (make-native-error "TypeError" "Converting circular structure to JSON")))
  (push value (jstate-stack st)))

(defun json-serialize-object (st value)
  (json-check-cycle st value)
  (let* ((stepback (jstate-indent st))
         (new-indent (concatenate 'string (jstate-indent st) (jstate-gap st)))
         (keys (if (jstate-has-prop-list st)
                   (jstate-prop-list st)
                   (remove-if-not #'stringp (enumerable-own-keys value :key))))
         (members '()))
    (setf (jstate-indent st) new-indent)
    (dolist (k keys)
      (let ((strp (json-serialize-property st value k)))
        (when strp
          (push (concatenate 'string (json-quote k)
                             (if (plusp (length (jstate-gap st))) ": " ":")
                             strp)
                members))))
    (setf (jstate-indent st) stepback)
    (pop (jstate-stack st))
    (setf members (nreverse members))
    (cond
      ((null members) "{}")
      ((zerop (length (jstate-gap st)))
       (format nil "{~{~a~^,~}}" members))
      (t
       (let ((sep (concatenate 'string "," (string #\Newline) new-indent)))
         (concatenate 'string "{" (string #\Newline) new-indent
                      (format nil (concatenate 'string "~{~a~^" sep "~}") members)
                      (string #\Newline) stepback "}"))))))

(defun json-serialize-array (st value)
  (json-check-cycle st value)
  (let* ((stepback (jstate-indent st))
         (new-indent (concatenate 'string (jstate-indent st) (jstate-gap st)))
         (len (to-int-index (js-get value "length")))
         (parts '()))
    (setf (jstate-indent st) new-indent)
    (dotimes (i len)
      (let ((strp (json-serialize-property st value (princ-to-string i))))
        (push (or strp "null") parts)))
    (setf (jstate-indent st) stepback)
    (pop (jstate-stack st))
    (setf parts (nreverse parts))
    (cond
      ((null parts) "[]")
      ((zerop (length (jstate-gap st)))
       (format nil "[~{~a~^,~}]" parts))
      (t
       (let ((sep (concatenate 'string "," (string #\Newline) new-indent)))
         (concatenate 'string "[" (string #\Newline) new-indent
                      (format nil (concatenate 'string "~{~a~^" sep "~}") parts)
                      (string #\Newline) stepback "]"))))))

(defun json-build-prop-list (replacer)
  "Build the property allow-list from an array replacer (strings + numbers,
   de-duplicated, in order)."
  (let ((len (to-int-index (js-get replacer "length"))) (out '()))
    (dotimes (i len)
      (let* ((v (js-get replacer (princ-to-string i)))
             (item (cond ((stringp v) v)
                         ((floatp v) (number-to-string v))
                         ((and (js-object-p v)
                               (let ((c (js-object-class v)))
                                 (member c '("String" "Number") :test #'string=)))
                          (to-string v))
                         (t nil))))
        (when (and item (not (member item out :test #'string=)))
          (push item out))))
    (nreverse out)))

(defun json-gap-from-space (space)
  "Compute the indent gap string from the space argument."
  ;; unwrap Number/String wrapper — coerce via ToNumber/ToString (may throw for
  ;; overridden boxes); plain boxes read their slot directly to avoid the engine's
  ;; coercion loop on unmodified wrappers.
  (when (js-object-p space)
    (let ((cls (js-object-class space)))
      (cond ((string= cls "Number")
             (setf space (if (json-plain-box-p space "valueOf")
                             (js-object-primitive space) (to-number space))))
            ((string= cls "String")
             (setf space (if (json-plain-box-p space "toString")
                             (js-object-primitive space) (to-string space)))))))
  (cond
    ((floatp space)
     (let ((n (min 10 (max 0 (truncate (to-integer-or-infinity space))))))
       (make-string n :initial-element #\Space)))
    ((stringp space)
     (if (> (length space) 10) (subseq space 0 10) space))
    (t "")))

;;; ===========================================================================
;;; Install
;;; ===========================================================================

(defun install-json (realm)
  (let ((json (make-object :proto (realm-object-proto realm))))
    (def-method realm json "parse" 2 (this args)
      (let* ((text (to-string (arg 0 args)))
             (reviver (arg 1 args))
             (p (%make-jparse :str text :pos 0 :len (length text)))
             (result (json-parse-value p)))
        (jp-skip-ws p)
        (unless (jp-eof-p p)
          (json-syntax-error "Unexpected non-whitespace character after JSON"))
        (if (js-callable-p reviver)
            (let ((holder (make-object :proto (realm-object-proto realm))))
              (put holder "" result)
              (internalize-json-property realm holder "" reviver))
            result)))
    (def-method realm json "stringify" 3 (this args)
      (let* ((value (arg 0 args))
             (replacer (arg 1 args))
             (space (arg 2 args))
             (st (%make-jstate :realm realm :stack '() :indent "" :gap "")))
        ;; replacer
        (cond
          ((js-callable-p replacer) (setf (jstate-replacer-fn st) replacer))
          ((and (js-object-p replacer) (js-array-p replacer))
           (setf (jstate-prop-list st) (json-build-prop-list replacer)
                 (jstate-has-prop-list st) t)))
        ;; space
        (setf (jstate-gap st) (json-gap-from-space space))
        ;; wrap in a holder and serialize the "" key
        (let ((holder (make-object :proto (realm-object-proto realm))))
          (put holder "" value)
          (let ((str (json-serialize-property st holder "")))
            (if str str *undefined*)))))
    (put json (symbol-tostringtag realm) "JSON" :enumerable nil :writable nil :configurable t)
    (define-global realm "JSON" json)
    ;; the JSON global itself is { writable:true, enumerable:false, configurable:true }
    (put (realm-global realm) "JSON" json :enumerable nil :writable t :configurable t)))

(register-builtin-installer 'install-json)
