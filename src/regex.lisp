;;;; regex.lisp — a clean-room backtracking regular-expression engine for shuttle.
;;;; Compiles a JS RegExp source string + flags to a matcher used by RegExp.prototype
;;;; and the String regex methods.
;;;;
;;;; Design: parse the pattern string into an AST (parser struct below), then
;;;; compile the AST into a tree of "node matchers". A node matcher is a CL
;;;; closure of signature (mc pos k) -> boolean, where MC is the match context
;;;; (the input string, flags, capture array), POS is the current index into the
;;;; input, and K is a continuation closure (pos) -> boolean that matches the
;;;; rest of the pattern. This is the standard "continuation-passing backtracking"
;;;; style of the spec's RegExp semantics: each combinator calls K to try the
;;;; tail, and backtracking is just K returning NIL.
;;;;
;;;; regex-exec returns (values match-end captures) or NIL, where captures is a
;;;; simple-vector of (start . end) conses (or NIL for unmatched groups), index 0
;;;; being the whole match.
;;;;
;;;; Deferred (see report): full \p{...} Unicode property escapes (only the common
;;;; ASCII/BMP predefined classes handled), the `v`-flag set notation, and
;;;; astral/surrogate-aware advancement under /u (BMP is handled).

(in-package #:shuttle)

;;; ===========================================================================
;;; Errors
;;; ===========================================================================
(defun regex-syntax-error (msg)
  (js-throw (make-native-error "SyntaxError" (format nil "Invalid regular expression: ~a" msg))))

;;; ===========================================================================
;;; Compiled regexp object (the internal structure regex-compile returns)
;;; ===========================================================================
(defstruct (compiled-regex (:constructor %make-compiled-regex))
  source flags
  global ignore-case multiline dot-all sticky unicode has-indices
  matcher                               ; node matcher for the whole pattern
  n-captures                            ; number of capturing groups
  group-names)                          ; alist name->index (1-based)

;;; ===========================================================================
;;; Parser
;;; ===========================================================================
(defstruct (rx-parser (:constructor make-rx-parser (src len unicode)))
  src len (pos 0) unicode
  (group-count 0)
  (names '()))

(defun rp-peek (p &optional (o 0))
  (let ((i (+ (rx-parser-pos p) o)))
    (when (< i (rx-parser-len p)) (char (rx-parser-src p) i))))
(defun rp-next (p)
  (let ((c (rp-peek p))) (incf (rx-parser-pos p)) c))
(defun rp-eof (p) (>= (rx-parser-pos p) (rx-parser-len p)))
(defun rp-eat (p ch)
  (when (eql (rp-peek p) ch) (incf (rx-parser-pos p)) t))

;;; First pass: count capturing groups + collect names, so backreferences that
;;; appear before their group (and \k) can be validated / distinguished from
;;; octal escapes.
(defun rx-count-groups (src len)
  (let ((count 0) (names '()) (i 0))
    (loop while (< i len) do
      (let ((c (char src i)))
        (cond
          ((char= c #\\) (incf i 2))
          ((char= c #\[)
           (incf i)
           (loop while (and (< i len) (not (char= (char src i) #\])))
                 do (if (char= (char src i) #\\) (incf i 2) (incf i)))
           (incf i))
          ((char= c #\()
           (cond
             ((and (< (+ i 1) len) (char= (char src (+ i 1)) #\?))
              (if (and (< (+ i 2) len) (char= (char src (+ i 2)) #\<)
                       (< (+ i 3) len)
                       (not (member (char src (+ i 3)) '(#\= #\!))))
                  (progn
                    (incf count)
                    (let ((j (+ i 3)) (start (+ i 3)))
                      (loop while (and (< j len) (not (char= (char src j) #\>))) do (incf j))
                      (push (cons (subseq src start j) count) names))
                    (incf i))
                  (incf i)))
             (t (incf count) (incf i))))
          (t (incf i)))))
    (values count (nreverse names))))

(defun regex-parse (src flags-unicode)
  (multiple-value-bind (ngroups names) (rx-count-groups src (length src))
    (let ((p (make-rx-parser src (length src) flags-unicode)))
      (let ((ast (parse-disjunction p ngroups names)))
        (unless (rp-eof p)
          (regex-syntax-error (format nil "unexpected '~a' at ~d" (rp-peek p) (rx-parser-pos p))))
        (values ast ngroups names)))))

(defun parse-disjunction (p ngroups names)
  (let ((alts (list (parse-alternative p ngroups names))))
    (loop while (rp-eat p #\|)
          do (push (parse-alternative p ngroups names) alts))
    (if (= (length alts) 1) (car alts)
        (list* :alt (nreverse alts)))))

(defun parse-alternative (p ngroups names)
  (let ((terms '()))
    (loop until (or (rp-eof p) (member (rp-peek p) '(#\| #\))))
          do (push (parse-term p ngroups names) terms))
    (list* :seq (nreverse terms))))

(defun parse-term (p ngroups names)
  (let ((c (rp-peek p)))
    (cond
      ((eql c #\^) (rp-next p) '(:bol))
      ((eql c #\$) (rp-next p) '(:eol))
      ((and (eql c #\\) (member (rp-peek p 1) '(#\b #\B)))
       (rp-next p) (let ((a (rp-next p))) (if (char= a #\b) '(:wordb) '(:not-wordb))))
      ((and (eql c #\() (eql (rp-peek p 1) #\?)
            (member (rp-peek p 2) '(#\= #\!)))
       (rp-next p) (rp-next p)
       (let ((neg (char= (rp-next p) #\!))
             (body (parse-disjunction p ngroups names)))
         (unless (rp-eat p #\)) (regex-syntax-error "unterminated lookahead"))
         (parse-quantifier-opt p (list :lookahead neg body))))
      ((and (eql c #\() (eql (rp-peek p 1) #\?)
            (eql (rp-peek p 2) #\<)
            (member (rp-peek p 3) '(#\= #\!)))
       (rp-next p) (rp-next p) (rp-next p)
       (let ((neg (char= (rp-next p) #\!))
             (body (parse-disjunction p ngroups names)))
         (unless (rp-eat p #\)) (regex-syntax-error "unterminated lookbehind"))
         (parse-quantifier-opt p (list :lookbehind neg body))))
      (t
       (let ((atom (parse-atom p ngroups names)))
         (parse-quantifier-opt p atom))))))

(defun parse-quantifier-opt (p atom)
  (let ((c (rp-peek p)))
    (multiple-value-bind (mn mx has)
        (cond
          ((eql c #\*) (rp-next p) (values 0 nil t))
          ((eql c #\+) (rp-next p) (values 1 nil t))
          ((eql c #\?) (rp-next p) (values 0 1 t))
          ((eql c #\{)
           (multiple-value-bind (lo hi ok) (try-parse-braces p)
             (if ok (values lo hi t) (values nil nil nil))))
          (t (values nil nil nil)))
      (if has
          (let ((lazy (rp-eat p #\?)))
            (when (and mx (< mx mn)) (regex-syntax-error "quantifier out of order"))
            (list :repeat mn mx lazy atom))
          atom))))

(defun try-parse-braces (p)
  (let ((save (rx-parser-pos p)))
    (rp-next p)
    (let ((lo (parse-decimal p)))
      (if (null lo)
          (progn (setf (rx-parser-pos p) save) (values nil nil nil))
          (let ((hi lo))
            (cond
              ((rp-eat p #\,) (setf hi (parse-decimal p)))
              (t (setf hi lo)))
            (if (rp-eat p #\})
                (values lo hi t)
                (progn (setf (rx-parser-pos p) save) (values nil nil nil))))))))

(defun parse-decimal (p)
  (let ((v nil))
    (loop for c = (rp-peek p) while (and c (digit-char-p c))
          do (setf v (+ (* (or v 0) 10) (digit-char-p c))) (rp-next p))
    v))

(defun parse-atom (p ngroups names)
  (let ((c (rp-peek p)))
    (cond
      ((null c) (regex-syntax-error "unexpected end of pattern"))
      ((char= c #\.) (rp-next p) '(:dot))
      ((char= c #\()
       (rp-next p)
       (cond
         ((and (eql (rp-peek p) #\?) (eql (rp-peek p 1) #\:))
          (rp-next p) (rp-next p)
          (let ((body (parse-disjunction p ngroups names)))
            (unless (rp-eat p #\)) (regex-syntax-error "unterminated group"))
            (list :group nil nil body)))
         ((and (eql (rp-peek p) #\?) (eql (rp-peek p 1) #\<))
          (rp-next p) (rp-next p)
          (let ((name (parse-group-name p)))
            (incf (rx-parser-group-count p))
            (let ((idx (rx-parser-group-count p))
                  (body (parse-disjunction p ngroups names)))
              (unless (rp-eat p #\)) (regex-syntax-error "unterminated group"))
              (list :group idx name body))))
         ((eql (rp-peek p) #\?)
          (regex-syntax-error "invalid group"))
         (t
          (incf (rx-parser-group-count p))
          (let ((idx (rx-parser-group-count p))
                (body (parse-disjunction p ngroups names)))
            (unless (rp-eat p #\)) (regex-syntax-error "unterminated group"))
            (list :group idx nil body)))))
      ((char= c #\[) (parse-char-class p))
      ((char= c #\\) (parse-atom-escape p ngroups names))
      ((char= c #\)) (regex-syntax-error "unmatched )"))
      ((and (rx-parser-unicode p) (member c '(#\{ #\} #\])))
       (regex-syntax-error "lone brace/bracket in unicode mode"))
      ((char= c #\*) (regex-syntax-error "nothing to repeat"))
      ((char= c #\+) (regex-syntax-error "nothing to repeat"))
      ((and (char= c #\?) (rx-parser-unicode p)) (regex-syntax-error "nothing to repeat"))
      (t (rp-next p) (list :char c)))))

(defun parse-group-name (p)
  (let ((start (rx-parser-pos p)))
    (loop for c = (rp-peek p) while (and c (not (char= c #\>))) do (rp-next p))
    (let ((name (subseq (rx-parser-src p) start (rx-parser-pos p))))
      (unless (rp-eat p #\>) (regex-syntax-error "unterminated group name"))
      (when (string= name "") (regex-syntax-error "empty group name"))
      name)))

(defun parse-atom-escape (p ngroups names)
  (rp-next p)
  (let ((c (rp-peek p)))
    (when (null c) (regex-syntax-error "trailing backslash"))
    (cond
      ((member c '(#\d #\D #\w #\W #\s #\S))
       (rp-next p) (list :class-escape c))
      ((char= c #\k)
       (rp-next p)
       (if (eql (rp-peek p) #\<)
           (progn (rp-next p)
                  (let ((name (parse-group-name p)))
                    (let ((idx (cdr (assoc name names :test #'string=))))
                      (unless idx (regex-syntax-error (format nil "no group named ~a" name)))
                      (list :backref idx))))
           (if (rx-parser-unicode p)
               (regex-syntax-error "\\k must be followed by <name>")
               (list :char #\k))))
      ((and (digit-char-p c) (not (char= c #\0)))
       (let ((start (rx-parser-pos p)) (n 0))
         (loop for d = (rp-peek p) while (and d (digit-char-p d))
               do (setf n (+ (* n 10) (digit-char-p d))) (rp-next p))
         (cond
           ((<= n ngroups) (list :backref n))
           ((rx-parser-unicode p) (regex-syntax-error "invalid backreference"))
           (t (setf (rx-parser-pos p) start)
              (parse-legacy-octal-or-digit p)))))
      (t (list :char (parse-char-escape-value p))))))

(defun parse-legacy-octal-or-digit (p)
  (let ((c (rp-peek p)))
    (if (and c (char<= #\0 c #\7))
        (let ((val 0) (n 0))
          (loop while (and (< n 3) (let ((d (rp-peek p))) (and d (char<= #\0 d #\7))))
                do (setf val (+ (* val 8) (digit-char-p (rp-next p)))) (incf n))
          (list :char (code-char val)))
        (list :char (rp-next p)))))

(defun parse-char-escape-value (p)
  (let ((c (rp-next p)))
    (case c
      (#\n #\Newline) (#\r #\Return) (#\t #\Tab) (#\f #\Page)
      (#\v (code-char 11)) (#\0 (code-char 0))
      (#\b (code-char 8))
      (#\c
       (let ((x (rp-peek p)))
         (if (and x (alpha-char-p x))
             (progn (rp-next p) (code-char (mod (char-code (char-upcase x)) 32)))
             #\c)))
      (#\x (or (let ((save (rx-parser-pos p)) (v (parse-hex-value p 2)))
                 (if v (code-char v) (progn (setf (rx-parser-pos p) save) nil)))
               #\x))
      (#\u (parse-unicode-escape p))
      (t c))))

(defun parse-unicode-escape (p)
  (cond
    ((eql (rp-peek p) #\{)
     (if (rx-parser-unicode p)
         (progn
           (rp-next p)
           (let ((val 0) (any nil))
             (loop for c = (rp-peek p) while (and c (digit-char-p c 16))
                   do (setf val (+ (* val 16) (digit-char-p (rp-next p) 16)) any t))
             (unless (and any (rp-eat p #\})) (regex-syntax-error "invalid \\u{} escape"))
             (when (> val #x10FFFF) (regex-syntax-error "code point out of range"))
             (code-char val)))
         #\u))                          ; non-unicode: \u{ is literal 'u'
    (t
     (let ((save (rx-parser-pos p))
           (c1 (parse-hex-value p 4)))
       (if (null c1)
           (progn (setf (rx-parser-pos p) save)
                  (if (rx-parser-unicode p) (regex-syntax-error "invalid \\u escape") #\u))
           (if (and (rx-parser-unicode p) (<= #xD800 c1 #xDBFF)
                    (eql (rp-peek p) #\\) (eql (rp-peek p 1) #\u))
               (let ((save2 (rx-parser-pos p)))
                 (rp-next p) (rp-next p)
                 (let ((c2 (parse-hex-value p 4)))
                   (if (and c2 (<= #xDC00 c2 #xDFFF))
                       (code-char (+ #x10000 (* (- c1 #xD800) #x400) (- c2 #xDC00)))
                       (progn (setf (rx-parser-pos p) save2) (code-char c1)))))
               (code-char c1)))))))

(defun parse-hex-value (p n)
  (let ((val 0))
    (dotimes (i n)
      (let ((c (rp-peek p)))
        (unless (and c (digit-char-p c 16)) (return-from parse-hex-value nil))
        (setf val (+ (* val 16) (digit-char-p (rp-next p) 16)))))
    val))

;;; ---- character classes ----
(defun parse-char-class (p)
  (rp-next p)
  (let ((neg (rp-eat p #\^)) (items '()))
    (loop
      (let ((c (rp-peek p)))
        (when (null c) (regex-syntax-error "unterminated character class"))
        (when (char= c #\]) (rp-next p) (return))
        (let ((atom (parse-class-atom p)))
          (if (and (eql (rp-peek p) #\-)
                   (rp-peek p 1)
                   (not (eql (rp-peek p 1) #\]))
                   (consp atom) (eq (car atom) :ch))
              (progn
                (rp-next p)
                (let ((hi (parse-class-atom p)))
                  (if (and (consp hi) (eq (car hi) :ch))
                      (let ((lo-c (cadr atom)) (hi-c (cadr hi)))
                        (when (> (char-code lo-c) (char-code hi-c))
                          (regex-syntax-error "range out of order in character class"))
                        (push (list :range lo-c hi-c) items))
                      (progn (push atom items)
                             (push (list :ch #\-) items)
                             (push hi items)))))
              (push atom items)))))
    (list :char-class neg (nreverse items))))

(defun parse-class-atom (p)
  (let ((c (rp-peek p)))
    (if (char= c #\\)
        (progn
          (rp-next p)
          (let ((e (rp-peek p)))
            (cond
              ((null e) (regex-syntax-error "trailing backslash in class"))
              ((member e '(#\d #\D #\w #\W #\s #\S))
               (rp-next p) (list :class-escape e))
              ((char= e #\b) (rp-next p) (list :ch (code-char 8)))
              (t (list :ch (parse-char-escape-value p))))))
        (progn (rp-next p) (list :ch c)))))

;;; ===========================================================================
;;; Predefined class membership
;;; ===========================================================================
(declaim (inline rx-digit-p rx-word-p))
(defun rx-digit-p (c) (char<= #\0 c #\9))
(defun rx-word-p (c)
  (or (char<= #\a c #\z) (char<= #\A c #\Z) (char<= #\0 c #\9) (char= c #\_)))
(defparameter +rx-space-chars+
  (list #\Space #\Tab #\Newline #\Return #\Page (code-char 11)
        (code-char #x00A0) (code-char #x2028) (code-char #x2029) (code-char #xFEFF)
        (code-char #x1680) (code-char #x2000) (code-char #x2001) (code-char #x2002)
        (code-char #x2003) (code-char #x2004) (code-char #x2005) (code-char #x2006)
        (code-char #x2007) (code-char #x2008) (code-char #x2009) (code-char #x200A)
        (code-char #x202F) (code-char #x205F) (code-char #x3000)))
(defun rx-space-p (c) (and (member c +rx-space-chars+) t))

(defun class-escape-member-p (esc c)
  (ecase esc
    (#\d (rx-digit-p c)) (#\D (not (rx-digit-p c)))
    (#\w (rx-word-p c))  (#\W (not (rx-word-p c)))
    (#\s (rx-space-p c)) (#\S (not (rx-space-p c)))))

(defun line-terminator-p (c)
  (or (char= c #\Newline) (char= c #\Return)
      (char= c (code-char #x2028)) (char= c (code-char #x2029))))

;;; ===========================================================================
;;; Match context
;;; ===========================================================================
(defstruct (mctx (:constructor make-mctx))
  input len captures
  ignore-case multiline dot-all unicode
  (steps 0 :type fixnum))

;; Bound total backtracking work per exec: a pathological pattern (nested
;; quantifiers, catastrophic backtracking) would otherwise recurse the CL
;; control stack to a FATAL, uncatchable exhaustion. On exceed we THROW
;; 'regex-overflow, caught in regex-exec -> treat as no match.
(defparameter *regex-max-steps* 1500000)
(declaim (inline regex-step))
(defun regex-step (mc)
  (when (> (the fixnum (incf (the fixnum (mctx-steps mc)))) (the fixnum *regex-max-steps*))
    (throw 'regex-overflow nil)))

(defun rx-char-eq (mc a b)
  (if (mctx-ignore-case mc)
      (char= (char-upcase a) (char-upcase b))
      (char= a b)))

;;; ===========================================================================
;;; Compile AST -> node matcher.  A node matcher: (lambda (mc pos k) ...) -> bool.
;;; ===========================================================================
(defun compile-node (node)
  (ecase (car node)
    (:seq   (compile-seq (cdr node)))
    (:alt   (compile-alt (cdr node)))
    (:char  (compile-char (cadr node)))
    (:dot   (compile-dot))
    (:bol   (compile-bol))
    (:eol   (compile-eol))
    (:wordb (compile-wordb nil))
    (:not-wordb (compile-wordb t))
    (:class-escape (compile-class-escape (cadr node)))
    (:char-class (compile-char-class (cadr node) (caddr node)))
    (:group (compile-group (cadr node) (cadddr node)))
    (:backref (compile-backref (cadr node)))
    (:repeat (compile-repeat node))
    (:lookahead (compile-lookahead (cadr node) (caddr node)))
    (:lookbehind (compile-lookbehind (cadr node) (caddr node)))))

(defun compile-seq (nodes)
  (if (null nodes)
      (lambda (mc pos k) (declare (ignore mc)) (funcall k pos))
      (let ((compiled (mapcar #'compile-node nodes)))
        (labels ((chain (ms)
                   (if (null (cdr ms))
                       (car ms)
                       (let ((head (car ms)) (rest (chain (cdr ms))))
                         (lambda (mc pos k)
                           (funcall head mc pos
                                    (lambda (p2) (funcall rest mc p2 k))))))))
          (chain compiled)))))

(defun compile-alt (alts)
  (let ((compiled (mapcar #'compile-node alts)))
    (lambda (mc pos k)
      (dolist (m compiled nil)
        (when (funcall m mc pos k) (return t))))))

(defun compile-char (c)
  (lambda (mc pos k)
    (and (< pos (mctx-len mc))
         (rx-char-eq mc (char (mctx-input mc) pos) c)
         (funcall k (1+ pos)))))

(defun compile-dot ()
  (lambda (mc pos k)
    (and (< pos (mctx-len mc))
         (or (mctx-dot-all mc)
             (not (line-terminator-p (char (mctx-input mc) pos))))
         (funcall k (1+ pos)))))

(defun compile-bol ()
  (lambda (mc pos k)
    (and (or (= pos 0)
             (and (mctx-multiline mc)
                  (line-terminator-p (char (mctx-input mc) (1- pos)))))
         (funcall k pos))))

(defun compile-eol ()
  (lambda (mc pos k)
    (and (or (= pos (mctx-len mc))
             (and (mctx-multiline mc)
                  (line-terminator-p (char (mctx-input mc) pos))))
         (funcall k pos))))

(defun rx-at-word-p (mc pos)
  (and (< pos (mctx-len mc))
       (rx-word-p (char (mctx-input mc) pos))))

(defun compile-wordb (negate)
  (lambda (mc pos k)
    (let* ((before (and (> pos 0) (rx-at-word-p mc (1- pos))))
           (after  (rx-at-word-p mc pos))
           (boundary (not (eq (and before t) (and after t)))))
      (and (if negate (not boundary) boundary)
           (funcall k pos)))))

(defun compile-class-escape (esc)
  (lambda (mc pos k)
    (and (< pos (mctx-len mc))
         (class-escape-member-p esc (char (mctx-input mc) pos))
         (funcall k (1+ pos)))))

(defun compile-char-class (negated items)
  (lambda (mc pos k)
    (and (< pos (mctx-len mc))
         (let* ((c (char (mctx-input mc) pos))
                (in (char-in-class-p mc c items)))
           (and (if negated (not in) in)
                (funcall k (1+ pos)))))))

(defun char-in-class-p (mc c items)
  (dolist (item items nil)
    (ecase (car item)
      (:ch (when (rx-char-eq mc c (cadr item)) (return t)))
      (:class-escape (when (class-escape-member-p (cadr item) c) (return t)))
      (:range
       (let ((lo (cadr item)) (hi (caddr item)))
         (if (mctx-ignore-case mc)
             (when (or (char<= lo c hi)
                       (char<= lo (char-upcase c) hi)
                       (char<= lo (char-downcase c) hi))
               (return t))
             (when (char<= lo c hi) (return t))))))))

(defun compile-group (idx body)
  (let ((m (compile-node body)))
    (if idx
        (lambda (mc pos k)
          (let ((saved (aref (mctx-captures mc) idx)))
            (or (funcall m mc pos
                         (lambda (p2)
                           (setf (aref (mctx-captures mc) idx) (cons pos p2))
                           (or (funcall k p2)
                               (progn (setf (aref (mctx-captures mc) idx) saved) nil))))
                (progn (setf (aref (mctx-captures mc) idx) saved) nil))))
        m)))

(defun compile-backref (idx)
  (lambda (mc pos k)
    (let ((cap (aref (mctx-captures mc) idx)))
      (if (null cap)
          (funcall k pos)
          (let* ((cs (car cap)) (ce (cdr cap)) (clen (- ce cs)))
            (if (> (+ pos clen) (mctx-len mc))
                nil
                (let ((ok t))
                  (dotimes (i clen)
                    (unless (rx-char-eq mc (char (mctx-input mc) (+ pos i))
                                        (char (mctx-input mc) (+ cs i)))
                      (setf ok nil) (return)))
                  (and ok (funcall k (+ pos clen))))))))))

;;; ---- quantifiers ----
(defun compile-repeat (node)
  (destructuring-bind (mn mx lazy body) (cdr node)
    (let ((m (compile-node body)))
      (lambda (mc pos k)
        (labels ((match-min (n pos)
                   (regex-step mc)
                   (if (zerop n)
                       (match-optional (if mx (- mx mn) nil) pos)
                       (funcall m mc pos (lambda (p2) (match-min (1- n) p2)))))
                 (match-optional (remaining pos)
                   (regex-step mc)
                   (if (and remaining (<= remaining 0))
                       (funcall k pos)
                       (if lazy
                           (or (funcall k pos)
                               (funcall m mc pos
                                        (lambda (p2)
                                          (if (= p2 pos) nil
                                              (match-optional (and remaining (1- remaining)) p2)))))
                           (or (funcall m mc pos
                                        (lambda (p2)
                                          (if (= p2 pos) nil
                                              (match-optional (and remaining (1- remaining)) p2))))
                               (funcall k pos))))))
          (match-min mn pos))))))

;;; ---- lookaround ----
(defun compile-lookahead (negate body)
  (let ((m (compile-node body)))
    (lambda (mc pos k)
      (let* ((saved (copy-seq (mctx-captures mc)))
             (matched (funcall m mc pos (lambda (p2) (declare (ignore p2)) t))))
        (cond
          (negate
           (replace (mctx-captures mc) saved)
           (and (not matched) (funcall k pos)))
          (t
           (if matched
               (funcall k pos)
               (progn (replace (mctx-captures mc) saved) nil))))))))

(defun compile-lookbehind (negate body)
  (let ((m (compile-node body)))
    (lambda (mc pos k)
      (let* ((saved (copy-seq (mctx-captures mc)))
             (matched
               (block found
                 (loop for s from pos downto 0 do
                   (when (funcall m mc s (lambda (p2) (= p2 pos)))
                     (return-from found t)))
                 nil)))
        (cond
          (negate
           (replace (mctx-captures mc) saved)
           (and (not matched) (funcall k pos)))
          (t
           (if matched
               (funcall k pos)
               (progn (replace (mctx-captures mc) saved) nil))))))))

;;; ===========================================================================
;;; Public: compile + exec
;;; ===========================================================================
(defun flag-set-p (flags ch) (and (position ch flags) t))

(defun validate-flags (flags)
  (let ((seen '()))
    (loop for c across flags do
      (unless (member c '(#\g #\i #\m #\s #\u #\y #\d))
        (regex-syntax-error (format nil "invalid flag '~a'" c)))
      (when (member c seen)
        (regex-syntax-error (format nil "duplicate flag '~a'" c)))
      (push c seen)))
  flags)

(defun regex-compile (source flags)
  "Compile a JS RegExp SOURCE string + FLAGS string into a compiled-regex.
   Throws a JS SyntaxError on invalid pattern/flags."
  (validate-flags flags)
  (let* ((unicode (flag-set-p flags #\u)))
    (multiple-value-bind (ast ngroups names) (regex-parse source unicode)
      (let ((matcher (compile-node ast)))
        (%make-compiled-regex
         :source source :flags flags
         :global (flag-set-p flags #\g)
         :ignore-case (flag-set-p flags #\i)
         :multiline (flag-set-p flags #\m)
         :dot-all (flag-set-p flags #\s)
         :sticky (flag-set-p flags #\y)
         :unicode unicode
         :has-indices (flag-set-p flags #\d)
         :matcher matcher
         :n-captures ngroups
         :group-names names)))))

(defun regex-exec (cre input start)
  "Attempt to match CRE against INPUT scanning from index START (respecting
   sticky). Returns (values match-end captures) with captures a simple-vector
   index->(start . end)|nil (index 0 = whole match), or NIL."
  (let* ((len (length input))
         (n (compiled-regex-n-captures cre))
         (sticky (compiled-regex-sticky cre))
         (matcher (compiled-regex-matcher cre)))
    (when (> start len) (return-from regex-exec nil))
    (catch 'regex-overflow
    (loop for pos from start to len do
      (let* ((caps (make-array (1+ n) :initial-element nil))
             (mc (make-mctx :input input :len len :captures caps
                            :ignore-case (compiled-regex-ignore-case cre)
                            :multiline (compiled-regex-multiline cre)
                            :dot-all (compiled-regex-dot-all cre)
                            :unicode (compiled-regex-unicode cre)))
             (end nil))
        (when (funcall matcher mc pos (lambda (p) (setf end p) t))
          (setf (aref caps 0) (cons pos end))
          (return-from regex-exec (values end caps)))
        (when sticky (return-from regex-exec nil))))
    nil)))
