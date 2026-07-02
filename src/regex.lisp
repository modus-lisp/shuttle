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
;;;; \p{...} / \P{...} Unicode property escapes are supported under /u and /v
;;;; (General_Category, Script, Script_Extensions, and the ES2025 binary
;;;; properties), backed by the vendored Unicode 17 tables in unicode-props.lisp
;;;; (sb-unicode's data is Unicode 10, too old for test262). Deferred: the
;;;; `v`-flag set notation and properties-of-strings (\p{RGI_Emoji} etc.).

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
  global ignore-case multiline dot-all sticky unicode unicode-sets has-indices
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
;; Decode a RegExpIdentifierName starting at index I (just past the '<') up to
;; the terminating '>'. \u HHHH and \u{ H+ } escapes are resolved (and combine a
;; surrogate pair into an astral code point). Returns (values decoded-name
;; index-of-'>'). Does not validate; callers that need error-checking use
;; PARSE-GROUP-NAME. Used by the group-counting pre-pass so its name keys match
;; the decoded names the real parser produces.
(defun decode-group-name (src len i)
  (let ((out (make-string-output-stream)))
    ;; Strings here are UTF-16 code units (astral chars appear as surrogate
    ;; pairs). We keep literal characters exactly as-is (so a surrogate pair in
    ;; the source stays a pair, matching how the JS string / groups-object key is
    ;; represented). Only a \u{cp} escape yielding an astral code point is
    ;; expanded into its surrogate pair.
    (flet ((emit-cp (cp)
             (if (> cp #xFFFF)
                 (let ((c (- cp #x10000)))
                   (write-char (code-char (+ #xD800 (ash c -10))) out)
                   (write-char (code-char (+ #xDC00 (logand c #x3FF))) out))
                 (write-char (code-char cp) out))))
      (loop while (and (< i len) (not (char= (char src i) #\>))) do
        (if (and (char= (char src i) #\\) (< (1+ i) len) (char= (char src (1+ i)) #\u))
            (progn
              (incf i 2)
              (if (and (< i len) (char= (char src i) #\{))
                  (progn (incf i)
                         (let ((v 0))
                           (loop while (and (< i len) (digit-char-p (char src i) 16))
                                 do (setf v (+ (* v 16) (digit-char-p (char src i) 16))) (incf i))
                           (when (and (< i len) (char= (char src i) #\})) (incf i))
                           (emit-cp v)))
                  (let ((v 0))
                    (dotimes (k 4)
                      (when (and (< i len) (digit-char-p (char src i) 16))
                        (setf v (+ (* v 16) (digit-char-p (char src i) 16))) (incf i)))
                    ;; a plain \uHHHH is a single code unit (may be a lone
                    ;; surrogate that pairs with an adjacent literal one)
                    (write-char (code-char v) out))))
            (progn (write-char (char src i) out) (incf i)))))
    (values (get-output-stream-string out) i)))

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
                    (multiple-value-bind (name j) (decode-group-name src len (+ i 3))
                      (declare (ignore j))
                      (push (cons name count) names))
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
        (check-duplicate-group-names ast)
        (values ast ngroups names)))))

(defun check-duplicate-group-names (ast)
  "ES2025 duplicate named groups: a name may repeat only across the branches of
   a Disjunction (mutually exclusive), never twice within one alternative. Walk
   the AST returning the set of names reachable in a node; the branches of an
   :alt may overlap with each other, but a :seq's children must not share names,
   and no name may appear twice within a single subtree otherwise."
  (labels ((names-in (node)
             ;; Returns the list of group names in NODE; signals on an in-scope
             ;; duplicate (two decls that are not in disjoint alternatives).
             (cond
               ((not (consp node)) '())
               (t
                (case (car node)
                  (:group
                   (let ((nm (caddr node))          ; (:group idx name body)
                         (inner (names-in (cadddr node))))
                     (if nm (union-check (list nm) inner) inner)))
                  (:seq
                   (reduce #'union-check (mapcar #'names-in (cdr node))
                           :initial-value '()))
                  (:alt
                   ;; branches are mutually exclusive: their name sets may
                   ;; overlap. Each branch is checked internally; the result is
                   ;; the union (dedup) so an OUTER seq still catches a name used
                   ;; both inside and outside the alternation.
                   (let ((acc '()))
                     (dolist (b (cdr node))
                       (dolist (n (names-in b)) (pushnew n acc :test #'string=)))
                     acc))
                  (:repeat (names-in (car (last node))))
                  ((:lookahead :lookbehind) (names-in (caddr node)))
                  (:modifier (names-in (cadddr node)))
                  (t '())))))
           (union-check (a b)
             ;; union of two name-sets that must be disjoint (else duplicate)
             (dolist (n b)
               (when (member n a :test #'string=)
                 (regex-syntax-error (format nil "duplicate capture group name '~a'" n)))
               (push n a))
             a))
    (names-in ast)))

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
         ;; In /u mode a lookahead is not a QuantifiableAssertion: a following
         ;; quantifier is a SyntaxError. (Annex B allows it in non-unicode.)
         (if (rx-parser-unicode p)
             (list :lookahead neg body)
             (parse-quantifier-opt p (list :lookahead neg body)))))
      ((and (eql c #\() (eql (rp-peek p 1) #\?)
            (eql (rp-peek p 2) #\<)
            (member (rp-peek p 3) '(#\= #\!)))
       (rp-next p) (rp-next p) (rp-next p)
       (let ((neg (char= (rp-next p) #\!))
             (body (parse-disjunction p ngroups names)))
         (unless (rp-eat p #\)) (regex-syntax-error "unterminated lookbehind"))
         ;; A lookbehind is never a QuantifiableAssertion in either mode.
         (list :lookbehind neg body)))
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
            ;; A quantifier applied to a quantifier is a SyntaxError in every
            ;; mode: `a**`, `a???`, `x{1}{1,}`, etc. (grammar: Term := Atom
            ;; Quantifier?, so a second quantifier has no Atom to bind).
            (when (quantifier-follows-p p)
              (regex-syntax-error "nothing to repeat"))
            (list :repeat mn mx lazy atom))
          atom))))

(defun quantifier-follows-p (p)
  "True if the next token is a quantifier: *, +, ? or a valid {n}/{n,}/{n,m}.
   (A `{` that is not a valid quantifier is not one — Annex B treats it as a
   literal, so it does not count here.) Does not consume input."
  (let ((c (rp-peek p)))
    (cond
      ((member c '(#\* #\+ #\?)) t)
      ((eql c #\{)
       (let ((save (rx-parser-pos p)))
         (multiple-value-bind (lo hi ok) (try-parse-braces p)
           (declare (ignore lo hi))
           (setf (rx-parser-pos p) save)   ; peek only
           ok)))
      (t nil))))

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
         ;; Pattern modifiers (ES2025): (?ims-ims: ... ) / (?ims: ...) / (?-ims: ...)
         ;; Enabled/disabled flags are drawn from {i,m,s}; each may appear on at
         ;; most one side, and the group must actually toggle something.
         ((and (eql (rp-peek p) #\?)
               (member (rp-peek p 1) '(#\i #\m #\s #\-)))
          (rp-next p)                   ; consume '?'
          (multiple-value-bind (add rem) (parse-modifier-flags p)
            (unless (rp-eat p #\:) (regex-syntax-error "invalid modifier group"))
            (let ((body (parse-disjunction p ngroups names)))
              (unless (rp-eat p #\)) (regex-syntax-error "unterminated group"))
              (list :modifier add rem body))))
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
      ((char= c #\?) (regex-syntax-error "nothing to repeat"))
      (t (rp-next p) (list :char c)))))

(defun parse-modifier-flags (p)
  "Parse a RegularExpressionModifiers sequence: added flags, optional '-' then
   removed flags, from {i,m,s}. Returns (values add-list rem-list). Errors on a
   duplicate/overlapping/empty specification."
  (let ((add '()) (rem '()))
    (loop for c = (rp-peek p) while (member c '(#\i #\m #\s)) do
      (when (member c add) (regex-syntax-error "duplicate modifier flag"))
      (push c add) (rp-next p))
    ;; A trailing '-' with no removed flags is valid: (?i-:...) toggles nothing on
    ;; the remove side. But (?-:...) with nothing on either side is a SyntaxError.
    (let ((had-dash (rp-eat p #\-)))
      (when had-dash
        (loop for c = (rp-peek p) while (member c '(#\i #\m #\s)) do
          (when (or (member c rem) (member c add))
            (regex-syntax-error "duplicate/overlapping modifier flag"))
          (push c rem) (rp-next p)))
      (when (and (null add) (null rem)) (regex-syntax-error "empty modifier group")))
    (values (nreverse add) (nreverse rem))))

(defun parse-group-name (p)
  ;; RegExpIdentifierName: raw identifier chars plus \u escapes, decoded to the
  ;; actual code points (so `(?<A>)` names the group "A"). Full Unicode
  ;; ID_Start/ID_Continue validation needs property tables (out of scope), so we
  ;; accept any non-empty decoded name and only reject a clearly-empty one.
  (multiple-value-bind (name end)
      (decode-group-name (rx-parser-src p) (rx-parser-len p) (rx-parser-pos p))
    (setf (rx-parser-pos p) end)
    (unless (rp-eat p #\>) (regex-syntax-error "unterminated group name"))
    (when (string= name "") (regex-syntax-error "empty group name"))
    name))

(defun ascii-letter-p (c) (or (char<= #\a c #\z) (char<= #\A c #\Z)))

(defun parse-atom-escape (p ngroups names)
  (rp-next p)
  (let ((c (rp-peek p)))
    (when (null c) (regex-syntax-error "trailing backslash"))
    (cond
      ((member c '(#\d #\D #\w #\W #\s #\S))
       (rp-next p) (list :class-escape c))
      ;; \p{...} / \P{...} Unicode property escape — only under /u (or /v).
      ;; In non-unicode mode \p stays the Annex B identity escape (handled by
      ;; the general case below).
      ((and (member c '(#\p #\P)) (rx-parser-unicode p))
       (rp-next p)
       (parse-unicode-property p (char= c #\P)))
      ;; \c followed by an ASCII letter is a control escape; otherwise, in
      ;; non-/u mode, the '\' is a literal character and 'c' is parsed as an
      ;; ordinary atom next (Annex B ControlEscape fallback: \cД, \c9, ...).
      ((and (char= c #\c) (not (rx-parser-unicode p))
            (let ((x (rp-peek p 1))) (not (and x (ascii-letter-p x)))))
       (list :char #\\))
      ((char= c #\k)
       ;; \k is a named backreference only when the pattern actually declares
       ;; named groups (or /u forces the strict grammar). Otherwise (Annex B,
       ;; non-/u, no named groups) it is the literal identity escape 'k'.
       (if (or (rx-parser-unicode p) names)
           (progn
             (rp-next p)
             (if (eql (rp-peek p) #\<)
                 (progn (rp-next p)
                        (let ((name (parse-group-name p)))
                          ;; Duplicate group names (ES2025) mean a name can map to
                          ;; several indices; \k<name> references whichever such
                          ;; group is currently captured.
                          (let ((idxs (loop for (nm . idx) in names
                                            when (string= nm name) collect idx)))
                            (unless idxs (regex-syntax-error (format nil "no group named ~a" name)))
                            (list :named-backref idxs))))
                 (if (rx-parser-unicode p)
                     (regex-syntax-error "\\k must be followed by <name>")
                     (list :char #\k))))
           (progn (rp-next p) (list :char #\k))))
      ((and (digit-char-p c) (not (char= c #\0)))
       (let ((start (rx-parser-pos p)) (n 0))
         (loop for d = (rp-peek p) while (and d (digit-char-p d))
               do (setf n (+ (* n 10) (digit-char-p d))) (rp-next p))
         (cond
           ((<= n ngroups) (list :backref n))
           ((rx-parser-unicode p) (regex-syntax-error "invalid backreference"))
           (t (setf (rx-parser-pos p) start)
              (parse-legacy-octal-or-digit p)))))
      ;; \0 followed by another octal digit (non-/u) is a LegacyOctalEscape,
      ;; e.g. \011 = 0o11. (Bare \0 not followed by a digit is NUL, handled by
      ;; parse-char-escape-value; /u keeps \0 strictly NUL-only.)
      ((and (char= c #\0) (not (rx-parser-unicode p))
            (let ((d (rp-peek p 1))) (and d (char<= #\0 d #\7))))
       (parse-legacy-octal-or-digit p))
      (t (list :char (parse-char-escape-value p))))))

(defun parse-unicode-property (p negated)
  "Parse the {Name} / {Name=Value} tail of a \\p / \\P escape (the p/P is already
   consumed; unicode mode only). Property names/values are matched EXACTLY
   against the UCD alias tables — no loose matching (case/space/hyphen variants
   are SyntaxErrors), per UnicodeMatchProperty / UnicodeMatchPropertyValue.
   Returns (:uprop negated range-vector)."
  (unless (rp-eat p #\{)
    (regex-syntax-error "\\p must be followed by {...} in unicode mode"))
  (flet ((scan (value-p)
           ;; UnicodePropertyName: ControlLetter | '_'. UnicodePropertyValue
           ;; additionally allows DecimalDigit. Anything else ends the token
           ;; (and if it isn't '=' or '}', the escape is malformed).
           (let ((out (make-string-output-stream)))
             (loop for c = (rp-peek p)
                   while (and c (or (ascii-letter-p c) (char= c #\_)
                                    (and value-p (char<= #\0 c #\9))))
                   do (write-char (rp-next p) out))
             (get-output-stream-string out))))
    (let ((name (scan nil)))
      (cond
        ((rp-eat p #\=)
         (let ((value (scan t)))
           (unless (rp-eat p #\})
             (regex-syntax-error "malformed \\p{...} property escape"))
           (let ((table (unicode-property-table name value)))
             (unless table
               (regex-syntax-error
                (format nil "unknown property in \\p{~a=~a}" name value)))
             (list :uprop negated table))))
        ((rp-eat p #\})
         (let ((table (and (string/= name "") (unicode-property-table name nil))))
           (unless table
             (regex-syntax-error (format nil "unknown property in \\p{~a}" name)))
           (list :uprop negated table)))
        (t (regex-syntax-error "malformed \\p{...} property escape"))))))

(defun parse-legacy-octal-or-digit (p)
  (let ((c (rp-peek p)))
    (if (and c (char<= #\0 c #\7))
        ;; LegacyOctalEscapeSequence: 1–3 octal digits, but a 3rd digit is only
        ;; part of the escape when the first is 0–3 (so the value stays ≤ 255).
        ;; `\770` is therefore \77 followed by a literal '0'; `\400` is \40 + '0'.
        (let ((max (if (char<= #\0 c #\3) 3 2)) (val 0) (n 0))
          (loop while (and (< n max) (let ((d (rp-peek p))) (and d (char<= #\0 d #\7))))
                do (setf val (+ (* val 8) (digit-char-p (rp-next p)))) (incf n))
          (list :char (code-char val)))
        (list :char (rp-next p)))))

(defun parse-char-escape-value (p &optional in-class)
  (let ((c (rp-next p)))
    (case c
      (#\n #\Newline) (#\r #\Return) (#\t #\Tab) (#\f #\Page)
      (#\v (code-char 11))
      (#\0 (when (and (rx-parser-unicode p)
                      (let ((d (rp-peek p))) (and d (digit-char-p d))))
             (regex-syntax-error "\\0 must not be followed by a digit in unicode mode"))
           (code-char 0))
      (#\b (code-char 8))
      (#\c
       (let ((x (rp-peek p)))
         (if (and x (ascii-letter-p x))
             (progn (rp-next p) (code-char (mod (char-code (char-upcase x)) 32)))
             ;; \c not followed by an ASCII letter: in /u mode a SyntaxError.
             ;; In non-/u it is not a control escape at all — the '\' is a
             ;; literal (handled by the caller emitting a literal backslash and
             ;; leaving the 'c'); this branch is only reached in /u mode.
             (regex-syntax-error "invalid \\c escape"))))
      (#\x (let ((save (rx-parser-pos p)) (v (parse-hex-value p 2)))
             (cond
               (v (code-char v))
               ((rx-parser-unicode p) (regex-syntax-error "invalid \\x escape"))
               (t (setf (rx-parser-pos p) save) #\x))))
      (#\u (parse-unicode-escape p))
      (t (unless (valid-identity-escape-p p c in-class)
           (regex-syntax-error (format nil "invalid identity escape \\~a" c)))
         c))))

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

;;; In /u mode, IdentityEscape is restricted to SyntaxCharacter + '/'.
;;; (Class context additionally allows '-'.)  Returns T if CH is a valid
;;; identity escape for the current mode/context.
(defun syntax-character-p (c)
  (member c '(#\^ #\$ #\\ #\. #\* #\+ #\? #\( #\) #\[ #\] #\{ #\} #\| )))
(defun valid-identity-escape-p (p c in-class)
  (if (rx-parser-unicode p)
      (or (syntax-character-p c) (char= c #\/) (and in-class (char= c #\-)))
      t))

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
                   (consp atom)
                   ;; A range needs a low bound. In /u the low bound must be a
                   ;; single char (a class-escape / property escape as a bound
                   ;; is a SyntaxError, diagnosed below).
                   (or (eq (car atom) :ch)
                       (and (rx-parser-unicode p)
                            (member (car atom) '(:class-escape :uprop)))))
              (progn
                (rp-next p)
                (let ((hi (parse-class-atom p)))
                  (cond
                    ((and (eq (car atom) :ch) (consp hi) (eq (car hi) :ch))
                     (let ((lo-c (cadr atom)) (hi-c (cadr hi)))
                       (when (> (char-code lo-c) (char-code hi-c))
                         (regex-syntax-error "range out of order in character class"))
                       (push (list :range lo-c hi-c) items)))
                    ;; /u: a class-escape on either side of '-' is invalid.
                    ((rx-parser-unicode p)
                     (regex-syntax-error "invalid class range with character-class escape"))
                    (t
                     (push atom items)
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
              ;; \p{...} / \P{...} inside a class (unicode mode only; in
              ;; non-unicode mode it's the identity escape via the fall-through).
              ((and (member e '(#\p #\P)) (rx-parser-unicode p))
               (rp-next p)
               (parse-unicode-property p (char= e #\P)))
              ((char= e #\b) (rp-next p) (list :ch (code-char 8)))
              ;; Annex B ClassControlLetter also accepts a DecimalDigit or '_'
              ;; after \c (non-/u). In /u mode only ASCII letters are valid.
              ((and (char= e #\c) (not (rx-parser-unicode p))
                    (let ((x (rp-peek p 1))) (and x (or (alpha-char-p x) (digit-char-p x) (char= x #\_)))))
               (rp-next p)              ; consume 'c'
               (let ((x (rp-next p)))
                 (list :ch (code-char (mod (char-code (char-upcase x)) 32)))))
              ;; \c not followed by a valid control letter: the '\' is a literal
              ;; ClassAtom on its own (Annex B); leave 'c' for the next atom.
              ((and (char= e #\c) (not (rx-parser-unicode p)))
               (list :ch #\\))
              ;; Legacy octal / decimal escapes in a class (non-/u): \1..\7 are
              ;; octal char values; \8 \9 are the literal digits.
              ((and (not (rx-parser-unicode p)) (digit-char-p e))
               (if (char<= #\0 e #\7)
                   (let ((max (if (char<= #\0 e #\3) 3 2)) (val 0) (n 0))
                     (loop while (and (< n max)
                                      (let ((d (rp-peek p))) (and d (char<= #\0 d #\7))))
                           do (setf val (+ (* val 8) (digit-char-p (rp-next p)))) (incf n))
                     (list :ch (code-char val)))
                   (progn (rp-next p) (list :ch e))))
              (t (list :ch (parse-char-escape-value p t))))))
        ;; Under /u, a literal high surrogate followed by a low surrogate is one
        ;; astral code point (stored as a single code-char > #xFFFF), so the
        ;; class matches the whole code point rather than either half.
        (progn
          (rp-next p)
          (if (and (rx-parser-unicode p) (high-surrogate-p c)
                   (let ((n (rp-peek p))) (and n (low-surrogate-p n))))
              (let ((lo (rp-next p)))
                (list :ch (code-char (+ #x10000
                                        (* (- (char-code c) #xD800) #x400)
                                        (- (char-code lo) #xDC00)))))
              (list :ch c))))))

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

;; Match direction for the node currently being COMPILED: +1 forward, -1 when
;; inside a lookbehind (matching proceeds right-to-left there, which is what
;; makes a repeated group's final capture the LEFTMOST iteration). Bound around
;; a lookbehind body in COMPILE-LOOKBEHIND; character-consuming matchers and the
;; sequence combinator read it at compile time so no per-step branch is needed.
(defvar *compile-direction* 1)

;; Bound total backtracking work per exec: a pathological pattern (nested
;; quantifiers, catastrophic backtracking) would otherwise recurse the CL
;; control stack to a FATAL, uncatchable exhaustion. On exceed we THROW
;; 'regex-overflow, caught in regex-exec -> treat as no match.
;; Set together with the runner's --control-stack-size (inspect/run262.sh): the
;; general (recursive) matcher nests one frame per quantifier repetition of a
;; COMPLEX body (group/alternation), so the budget must fit in the stack. The
;; common case — a quantifier over a single code point (literal / . / class) —
;; now runs through COMPILE-REPEAT-SINGLE, which is ITERATIVE (no per-char frame)
;; and only touches the step budget as a linear counter, so the budget no longer
;; has to be small to protect the stack. Raised to 10M so genuine long-input
;; single-char scans complete; the budget is shared across ALL candidate start
;; positions of one regex-exec (mctx is reused), so an O(n^2) start-position ×
;; backtrack scan of a NON-matching pattern over a long string bails at the
;; ceiling (-> correct "no match") in well under a second instead of hanging,
;; and a truly exponential group blowup still bails well before a FATAL,
;; uncatchable stack exhaustion.
(defparameter *regex-max-steps* 10000000)
(declaim (inline regex-step))
(defun regex-step (mc)
  (when (> (the fixnum (incf (the fixnum (mctx-steps mc)))) (the fixnum *regex-max-steps*))
    (throw 'regex-overflow nil)))

(defun rx-char-eq (mc a b)
  (if (mctx-ignore-case mc)
      (char= (char-upcase a) (char-upcase b))
      (char= a b)))

(declaim (inline high-surrogate-p low-surrogate-p))
(defun high-surrogate-p (c) (<= #xD800 (char-code c) #xDBFF))
(defun low-surrogate-p (c)  (<= #xDC00 (char-code c) #xDFFF))

;; Width (in UTF-16 code units) of the code point starting at POS. Under /u a
;; high surrogate followed by a low surrogate is a single 2-unit code point;
;; everything else (and all of non-unicode mode) is 1 unit.
(defun rx-cp-width (mc pos)
  (if (and (mctx-unicode mc)
           (< (1+ pos) (mctx-len mc))
           (high-surrogate-p (char (mctx-input mc) pos))
           (low-surrogate-p (char (mctx-input mc) (1+ pos))))
      2 1))

;; Width of the code point ENDING at POS (i.e. the one to the left), for
;; backward (lookbehind) matching: a low surrogate at pos-1 preceded by a high
;; surrogate at pos-2 is one 2-unit code point.
(defun rx-cp-width-back (mc pos)
  (if (and (mctx-unicode mc)
           (>= (- pos 2) 0)
           (low-surrogate-p (char (mctx-input mc) (1- pos)))
           (high-surrogate-p (char (mctx-input mc) (- pos 2))))
      2 1))

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
    (:uprop (compile-uprop (cadr node) (caddr node)))
    (:char-class (compile-char-class (cadr node) (caddr node)))
    (:group (compile-group (cadr node) (cadddr node)))
    (:backref (compile-backref (cadr node)))
    (:named-backref (compile-named-backref (cadr node)))
    (:repeat (compile-repeat node))
    (:lookahead (compile-lookahead (cadr node) (caddr node)))
    (:lookbehind (compile-lookbehind (cadr node) (caddr node)))
    (:modifier (compile-modifier (cadr node) (caddr node) (cadddr node)))))

(defun compile-modifier (add rem body)
  "Match BODY with the i/m/s flags in ADD forced on and those in REM forced off,
   for the duration of the enclosed group. Flags are restored on the way out
   (including via the continuation, so backtracking sees the outer flags)."
  (let ((m (compile-node body))
        (add-i (and (member #\i add) t)) (rem-i (and (member #\i rem) t))
        (add-m (and (member #\m add) t)) (rem-m (and (member #\m rem) t))
        (add-s (and (member #\s add) t)) (rem-s (and (member #\s rem) t)))
    (lambda (mc pos k)
      (let ((old-i (mctx-ignore-case mc))
            (old-m (mctx-multiline mc))
            (old-s (mctx-dot-all mc)))
        (flet ((restore () (setf (mctx-ignore-case mc) old-i
                                 (mctx-multiline mc) old-m
                                 (mctx-dot-all mc) old-s)))
          (when add-i (setf (mctx-ignore-case mc) t))
          (when rem-i (setf (mctx-ignore-case mc) nil))
          (when add-m (setf (mctx-multiline mc) t))
          (when rem-m (setf (mctx-multiline mc) nil))
          (when add-s (setf (mctx-dot-all mc) t))
          (when rem-s (setf (mctx-dot-all mc) nil))
          ;; The continuation K runs the *rest* of the pattern, which is outside
          ;; this group and must see the outer flags — so restore before calling K
          ;; and re-apply if K fails and the body backtracks into us.
          (prog1
              (funcall m mc pos
                       (lambda (p2)
                         (restore)
                         (or (funcall k p2)
                             (progn  ; re-enter group scope for further backtracking
                               (when add-i (setf (mctx-ignore-case mc) t))
                               (when rem-i (setf (mctx-ignore-case mc) nil))
                               (when add-m (setf (mctx-multiline mc) t))
                               (when rem-m (setf (mctx-multiline mc) nil))
                               (when add-s (setf (mctx-dot-all mc) t))
                               (when rem-s (setf (mctx-dot-all mc) nil))
                               nil))))
            (restore)))))))

(defun compile-seq (nodes)
  (if (null nodes)
      (lambda (mc pos k) (declare (ignore mc)) (funcall k pos))
      ;; In a lookbehind (backward direction) the terms must be matched
      ;; right-to-left, so compile them in reversed order.
      (let ((compiled (mapcar #'compile-node
                              (if (minusp *compile-direction*) (reverse nodes) nodes))))
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
  (let ((backward (minusp *compile-direction*)))
    (if (> (char-code c) #xFFFF)
        ;; An astral pattern char (from \u{...} in /u mode) must match the two
        ;; UTF-16 code units of its surrogate-pair encoding in the input.
        (let* ((cp (- (char-code c) #x10000))
               (hi (code-char (+ #xD800 (ash cp -10))))
               (lo (code-char (+ #xDC00 (logand cp #x3FF)))))
          (if backward
              (lambda (mc pos k)
                (and (>= (- pos 2) 0)
                     (char= (char (mctx-input mc) (- pos 2)) hi)
                     (char= (char (mctx-input mc) (- pos 1)) lo)
                     (funcall k (- pos 2))))
              (lambda (mc pos k)
                (and (< (1+ pos) (mctx-len mc))
                     (char= (char (mctx-input mc) pos) hi)
                     (char= (char (mctx-input mc) (1+ pos)) lo)
                     (funcall k (+ pos 2))))))
        (if backward
            (lambda (mc pos k)
              (and (> pos 0)
                   (rx-char-eq mc (char (mctx-input mc) (1- pos)) c)
                   (funcall k (1- pos))))
            (lambda (mc pos k)
              (and (< pos (mctx-len mc))
                   (rx-char-eq mc (char (mctx-input mc) pos) c)
                   (funcall k (1+ pos))))))))

(defun compile-dot ()
  (if (minusp *compile-direction*)
      (lambda (mc pos k)
        (and (> pos 0)
             (let ((w (rx-cp-width-back mc pos)))
               (and (or (mctx-dot-all mc)
                        (not (line-terminator-p (char (mctx-input mc) (- pos w)))))
                    (funcall k (- pos w))))))
      (lambda (mc pos k)
        (and (< pos (mctx-len mc))
             (or (mctx-dot-all mc)
                 (not (line-terminator-p (char (mctx-input mc) pos))))
             ;; In /u a '.' consumes a whole code point (a surrogate pair counts once).
             (funcall k (+ pos (rx-cp-width mc pos)))))))

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
  (if (minusp *compile-direction*)
      (lambda (mc pos k)
        (and (> pos 0)
             (class-escape-member-p esc (char (mctx-input mc) (1- pos)))
             (funcall k (1- pos))))
      (lambda (mc pos k)
        (and (< pos (mctx-len mc))
             (class-escape-member-p esc (char (mctx-input mc) pos))
             (funcall k (1+ pos))))))

(declaim (inline uprop-match-p))
(defun uprop-match-p (negated table c)
  "Does code-point char C satisfy the \\p (or, NEGATED, \\P) escape whose range
   table is TABLE?"
  (let ((in (ucp-range-member-p (char-code c) table)))
    (if negated (not in) in)))

(defun compile-uprop (negated table)
  "\\p{...} / \\P{...} in atom position: match one full code point (a surrogate
   pair counts once under /u) whose property membership matches."
  (if (minusp *compile-direction*)
      (lambda (mc pos k)
        (and (> pos 0)
             (multiple-value-bind (c w) (class-input-cp-back mc pos)
               (and (uprop-match-p negated table c)
                    (funcall k (- pos w))))))
      (lambda (mc pos k)
        (and (< pos (mctx-len mc))
             (multiple-value-bind (c w) (class-input-cp mc pos)
               (and (uprop-match-p negated table c)
                    (funcall k (+ pos w))))))))

(defun class-input-cp (mc pos)
  "Return (values code-point-char width) for the code point starting at POS,
   combining a surrogate pair into one astral char under /u."
  (let* ((in (mctx-input mc)) (c (char in pos)))
    (if (and (mctx-unicode mc) (high-surrogate-p c)
             (< (1+ pos) (mctx-len mc)) (low-surrogate-p (char in (1+ pos))))
        (values (code-char (+ #x10000
                              (* (- (char-code c) #xD800) #x400)
                              (- (char-code (char in (1+ pos))) #xDC00)))
                2)
        (values c 1))))

(defun class-input-cp-back (mc pos)
  "As CLASS-INPUT-CP but for the code point ending at POS (lookbehind)."
  (let* ((in (mctx-input mc)) (c (char in (1- pos))))
    (if (and (mctx-unicode mc) (low-surrogate-p c)
             (>= (- pos 2) 0) (high-surrogate-p (char in (- pos 2))))
        (values (code-char (+ #x10000
                              (* (- (char-code (char in (- pos 2))) #xD800) #x400)
                              (- (char-code c) #xDC00)))
                2)
        (values c 1))))

(defun compile-char-class (negated items)
  (if (minusp *compile-direction*)
      (lambda (mc pos k)
        (and (> pos 0)
             (multiple-value-bind (c w) (class-input-cp-back mc pos)
               (let ((in (char-in-class-p mc c items)))
                 (and (if negated (not in) in)
                      (funcall k (- pos w)))))))
      (lambda (mc pos k)
        (and (< pos (mctx-len mc))
             (multiple-value-bind (c w) (class-input-cp mc pos)
               (let ((in (char-in-class-p mc c items)))
                 (and (if negated (not in) in)
                      (funcall k (+ pos w)))))))))

(defun char-in-class-p (mc c items)
  (dolist (item items nil)
    (ecase (car item)
      (:ch (when (rx-char-eq mc c (cadr item)) (return t)))
      (:class-escape (when (class-escape-member-p (cadr item) c) (return t)))
      (:uprop (when (uprop-match-p (cadr item) (caddr item) c) (return t)))
      (:range
       (let ((lo (cadr item)) (hi (caddr item)))
         (if (mctx-ignore-case mc)
             (when (or (char<= lo c hi)
                       (char<= lo (char-upcase c) hi)
                       (char<= lo (char-downcase c) hi))
               (return t))
             (when (char<= lo c hi) (return t))))))))

(defun compile-group (idx body)
  (let ((m (compile-node body))
        (backward (minusp *compile-direction*)))
    (if idx
        (lambda (mc pos k)
          (let ((saved (aref (mctx-captures mc) idx)))
            (or (funcall m mc pos
                         (lambda (p2)
                           ;; The span is (start . end) with start <= end. Forward
                           ;; matching ends at p2 >= pos; backward (lookbehind)
                           ;; matching ends at p2 <= pos.
                           (setf (aref (mctx-captures mc) idx)
                                 (if backward (cons p2 pos) (cons pos p2)))
                           (or (funcall k p2)
                               (progn (setf (aref (mctx-captures mc) idx) saved) nil))))
                (progn (setf (aref (mctx-captures mc) idx) saved) nil))))
        m)))

(defun match-backref-cap (mc cap pos k &optional backward)
  "Try to match the captured span CAP (a (start . end) cons or NIL) at POS,
   calling K on success. An unset capture matches the empty string. BACKWARD
   matches the span ending at POS (moving left), for use inside a lookbehind."
  (if (null cap)
      (funcall k pos)
      (let* ((cs (car cap)) (ce (cdr cap)) (clen (- ce cs)))
        (if backward
            (if (< (- pos clen) 0)
                nil
                (let ((ok t) (base (- pos clen)))
                  (dotimes (i clen)
                    (unless (rx-char-eq mc (char (mctx-input mc) (+ base i))
                                        (char (mctx-input mc) (+ cs i)))
                      (setf ok nil) (return)))
                  (and ok (funcall k base))))
            (if (> (+ pos clen) (mctx-len mc))
                nil
                (let ((ok t))
                  (dotimes (i clen)
                    (unless (rx-char-eq mc (char (mctx-input mc) (+ pos i))
                                        (char (mctx-input mc) (+ cs i)))
                      (setf ok nil) (return)))
                  (and ok (funcall k (+ pos clen)))))))))

(defun compile-backref (idx)
  (let ((backward (minusp *compile-direction*)))
    (lambda (mc pos k)
      (match-backref-cap mc (aref (mctx-captures mc) idx) pos k backward))))

(defun compile-named-backref (idxs)
  "\\k<name> where NAME may map to several (duplicate-named) group indices: use
   whichever one is currently captured, else match the empty string."
  (if (null (cdr idxs))
      (compile-backref (car idxs))
      (let ((backward (minusp *compile-direction*)))
        (lambda (mc pos k)
          (let ((cap (loop for i in idxs
                           for c = (aref (mctx-captures mc) i)
                           when c return c)))
            (match-backref-cap mc cap pos k backward))))))

;;; ---- single-char stepper (iterative-quantifier fast path) ----
;;; A "single-char" body is one whose match always consumes exactly ONE code
;;; point (1 or 2 UTF-16 units under /u) and never captures: :char, :dot,
;;; :class-escape, :char-class. For a quantifier over such a body we can match
;;; greedily in a forward (or backward, under lookbehind) SCAN — recording each
;;; boundary in a stack — and then backtrack by popping boundaries, WITHOUT the
;;; O(n)-deep recursion of the general CPS RepeatMatcher. This is what keeps
;;; `X*`, `X+`, `X{n,m}` (and their lazy forms) from blowing the control stack /
;;; step budget on long inputs, including the pathological backtracking cases
;;; (`a+b`, `.*x` on a long run of matching chars).
;;;
;;; SINGLE-CHAR-STEPPER returns, for a single-char BODY, a closure
;;;   (lambda (mc pos) -> next-pos | nil)
;;; that tries to consume one code point at POS in the current compile direction
;;; (advancing right for forward, left for backward) and returns the new index,
;;; or NIL if the body does not match there. Returns NIL (not a closure) when
;;; BODY is not a single-char matcher, so the caller falls back to the general
;;; recursive path.
(defun single-char-stepper (body)
  (let ((backward (minusp *compile-direction*)))
    (case (car body)
      (:char
       (let ((c (cadr body)))
         (if (> (char-code c) #xFFFF)
             ;; astral literal: two code units
             (let* ((cp (- (char-code c) #x10000))
                    (hi (code-char (+ #xD800 (ash cp -10))))
                    (lo (code-char (+ #xDC00 (logand cp #x3FF)))))
               (if backward
                   (lambda (mc pos)
                     (when (and (>= (- pos 2) 0)
                                (char= (char (mctx-input mc) (- pos 2)) hi)
                                (char= (char (mctx-input mc) (1- pos)) lo))
                       (- pos 2)))
                   (lambda (mc pos)
                     (when (and (< (1+ pos) (mctx-len mc))
                                (char= (char (mctx-input mc) pos) hi)
                                (char= (char (mctx-input mc) (1+ pos)) lo))
                       (+ pos 2)))))
             (if backward
                 (lambda (mc pos)
                   (when (and (> pos 0)
                              (rx-char-eq mc (char (mctx-input mc) (1- pos)) c))
                     (1- pos)))
                 (lambda (mc pos)
                   (when (and (< pos (mctx-len mc))
                              (rx-char-eq mc (char (mctx-input mc) pos) c))
                     (1+ pos)))))))
      (:dot
       (if backward
           (lambda (mc pos)
             (when (> pos 0)
               (let ((w (rx-cp-width-back mc pos)))
                 (when (or (mctx-dot-all mc)
                           (not (line-terminator-p (char (mctx-input mc) (- pos w)))))
                   (- pos w)))))
           (lambda (mc pos)
             (when (and (< pos (mctx-len mc))
                        (or (mctx-dot-all mc)
                            (not (line-terminator-p (char (mctx-input mc) pos)))))
               (+ pos (rx-cp-width mc pos))))))
      (:class-escape
       (let ((esc (cadr body)))
         (if backward
             (lambda (mc pos)
               (when (and (> pos 0)
                          (class-escape-member-p esc (char (mctx-input mc) (1- pos))))
                 (1- pos)))
             (lambda (mc pos)
               (when (and (< pos (mctx-len mc))
                          (class-escape-member-p esc (char (mctx-input mc) pos)))
                 (1+ pos))))))
      (:uprop
       (let ((negated (cadr body)) (table (caddr body)))
         (if backward
             (lambda (mc pos)
               (when (> pos 0)
                 (multiple-value-bind (c w) (class-input-cp-back mc pos)
                   (when (uprop-match-p negated table c) (- pos w)))))
             (lambda (mc pos)
               (when (< pos (mctx-len mc))
                 (multiple-value-bind (c w) (class-input-cp mc pos)
                   (when (uprop-match-p negated table c) (+ pos w))))))))
      (:char-class
       (let ((negated (cadr body)) (items (caddr body)))
         (if backward
             (lambda (mc pos)
               (when (> pos 0)
                 (multiple-value-bind (c w) (class-input-cp-back mc pos)
                   (let ((in (char-in-class-p mc c items)))
                     (when (if negated (not in) in) (- pos w))))))
             (lambda (mc pos)
               (when (< pos (mctx-len mc))
                 (multiple-value-bind (c w) (class-input-cp mc pos)
                   (let ((in (char-in-class-p mc c items)))
                     (when (if negated (not in) in) (+ pos w)))))))))
      (t nil))))

(defun compile-repeat-single (mn mx lazy step)
  "Iterative RepeatMatcher for a single-code-point body. STEP is the closure from
   SINGLE-CHAR-STEPPER. Greedily scans up to MX (or end of matchable run) counting
   from MN, recording each boundary, then hands successive extents to the
   continuation K — from the greediest down to MN (greedy) or from MN up (lazy).
   No recursion depth proportional to the match length."
  (lambda (mc pos k)
    (block matched
      ;; Scan forward collecting boundaries. BOUNDS[i] is the index after i steps;
      ;; BOUNDS[0] = POS. We stop at MX steps (if bounded), at a non-match, or when
      ;; a zero-width step would loop (STEP returns the same index).
      (let ((bounds (make-array 16 :adjustable t :fill-pointer 1 :initial-element pos))
            (cur pos) (count 0))
        (loop
          (when (and mx (>= count mx)) (return))
          (regex-step mc)
          (let ((next (funcall step mc cur)))
            (when (or (null next) (= next cur)) (return))
            (setf cur next) (incf count)
            (vector-push-extend cur bounds)))
        ;; COUNT = number of matched code points (>= 0). Need at least MN.
        (when (< count mn) (return-from matched nil))
        (if lazy
            ;; lazy: fewest first — try MN, then MN+1, ... up to COUNT
            (loop for i from mn to count do
              (regex-step mc)
              (let ((r (funcall k (aref bounds i))))
                (when r (return-from matched r))))
            ;; greedy: most first — try COUNT, then COUNT-1, ... down to MN
            (loop for i from count downto mn do
              (regex-step mc)
              (let ((r (funcall k (aref bounds i))))
                (when r (return-from matched r)))))
        nil))))

;;; ---- quantifiers ----
(defun collect-capture-indices (node)
  "The set of capturing-group indices that appear anywhere inside NODE (used to
   reset them per quantifier iteration, per the spec's RepeatMatcher)."
  (let ((acc '()))
    (labels ((walk (n)
               (when (consp n)
                 (case (car n)
                   (:group (when (cadr n) (push (cadr n) acc)) (walk (cadddr n)))
                   ((:seq :alt) (mapc #'walk (cdr n)))
                   (:repeat (walk (car (last n))))
                   ((:lookahead :lookbehind) (walk (caddr n)))
                   (:modifier (walk (cadddr n)))))))
      (walk node))
    (nreverse acc)))

(defun compile-repeat (node)
  (destructuring-bind (mn mx lazy body) (cdr node)
    ;; Fast path: a quantifier over a single-code-point, non-capturing body
    ;; (literal / . / class-escape / char-class) is matched iteratively, avoiding
    ;; the O(match-length)-deep recursion (and step-budget blowup) of the general
    ;; RepeatMatcher — the big win for long inputs and backtracking-heavy patterns.
    (let ((step (single-char-stepper body)))
      (when step
        (return-from compile-repeat (compile-repeat-single mn mx lazy step))))
    (let ((m (compile-node body))
          ;; Captures inside the body are cleared before each iteration so that,
          ;; e.g., a group that failed to match on the current pass reads as
          ;; undefined rather than leaking a value from a previous iteration.
          (body-caps (collect-capture-indices body)))
      (lambda (mc pos k)
        (labels ((try-iteration (pos body-k)
                   ;; Clear this body's captures, run the body, and on failure of
                   ;; the whole continuation restore them — so a speculative
                   ;; extra iteration that ultimately fails doesn't wipe the
                   ;; captures the last *successful* iteration produced.
                   (let ((saved (when body-caps
                                  (mapcar (lambda (i) (aref (mctx-captures mc) i)) body-caps))))
                     (dolist (i body-caps) (setf (aref (mctx-captures mc) i) nil))
                     (or (funcall m mc pos body-k)
                         (progn
                           (when body-caps
                             (loop for i in body-caps for v in saved
                                   do (setf (aref (mctx-captures mc) i) v)))
                           nil))))
                 (match-min (n pos)
                   (regex-step mc)
                   (if (zerop n)
                       (match-optional (if mx (- mx mn) nil) pos)
                       (try-iteration pos (lambda (p2) (match-min (1- n) p2)))))
                 (match-optional (remaining pos)
                   (regex-step mc)
                   (if (and remaining (<= remaining 0))
                       (funcall k pos)
                       (flet ((more (p)
                                (try-iteration p
                                 (lambda (p2)
                                   (if (= p2 p) nil
                                       (match-optional (and remaining (1- remaining)) p2))))))
                         (if lazy
                             (or (funcall k pos) (more pos))
                             (or (more pos) (funcall k pos)))))))
          (match-min mn pos))))))

;;; ---- lookaround ----
(defun compile-lookahead (negate body)
  ;; A lookahead always matches forward, even when it appears inside a
  ;; lookbehind (its Disjunction is evaluated with +1 direction).
  (let ((m (let ((*compile-direction* 1)) (compile-node body))))
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
  ;; The body is compiled in backward (-1) direction: matching starts at POS and
  ;; consumes leftward, so a repeated group's final capture is its LEFTMOST
  ;; iteration and captures reflect right-to-left evaluation (per spec). The
  ;; continuation just needs to succeed once; the resulting captures are kept
  ;; (positive lookbehind) so back-references outside can see them.
  (let ((m (let ((*compile-direction* -1)) (compile-node body))))
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

;;; ===========================================================================
;;; Public: compile + exec
;;; ===========================================================================
(defun flag-set-p (flags ch) (and (position ch flags) t))

(defun validate-flags (flags)
  (let ((seen '()))
    (loop for c across flags do
      (unless (member c '(#\g #\i #\m #\s #\u #\y #\d #\v))
        (regex-syntax-error (format nil "invalid flag '~a'" c)))
      (when (member c seen)
        (regex-syntax-error (format nil "duplicate flag '~a'" c)))
      (push c seen)))
  ;; u and v are mutually exclusive.
  (when (and (find #\u flags) (find #\v flags))
    (regex-syntax-error "the 'u' and 'v' flags cannot both be set"))
  flags)

(defun regex-compile (source flags)
  "Compile a JS RegExp SOURCE string + FLAGS string into a compiled-regex.
   Throws a JS SyntaxError on invalid pattern/flags."
  (validate-flags flags)
  (let* ((unicode-sets (flag-set-p flags #\v))
         ;; Under either u or v the engine parses in "unicode mode" and advances
         ;; by whole code points. (Full v-flag set notation is not implemented;
         ;; a pattern that uses it will raise a SyntaxError.)
         (unicode (or (flag-set-p flags #\u) unicode-sets)))
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
         :unicode-sets unicode-sets
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
         (unicode (compiled-regex-unicode cre))
         (matcher (compiled-regex-matcher cre)))
    (when (> start len) (return-from regex-exec nil))
    (catch 'regex-overflow
    ;; Scan candidate start positions. Under /u we advance by whole code
    ;; points (AdvanceStringIndex), so a match is never anchored in the middle
    ;; of a surrogate pair.
    ;; ONE match-context is reused across all candidate start positions so the
    ;; step budget (mctx-steps) accumulates over the whole exec rather than
    ;; resetting per start. This bounds the O(n^2) start-position × backtrack
    ;; work of a non-matching pattern on a long string to a single 10M-step
    ;; ceiling (bail -> no match), instead of paying the full budget at *every*
    ;; start. Captures and the modifier-mutable flags are reset each iteration.
    (let* ((caps (make-array (1+ n) :initial-element nil))
           (base-i (compiled-regex-ignore-case cre))
           (base-m (compiled-regex-multiline cre))
           (base-s (compiled-regex-dot-all cre))
           (mc (make-mctx :input input :len len :captures caps
                          :ignore-case base-i :multiline base-m :dot-all base-s
                          :unicode unicode))
           (pos start))
      (loop
        (fill caps nil)
        (setf (mctx-ignore-case mc) base-i
              (mctx-multiline mc) base-m
              (mctx-dot-all mc) base-s)
        (let ((end nil))
          (when (funcall matcher mc pos (lambda (p) (setf end p) t))
            (setf (aref caps 0) (cons pos end))
            (return-from regex-exec (values end caps)))
          (when sticky (return-from regex-exec nil))
          (when (>= pos len) (return))
          (incf pos (if (and unicode
                             (< (1+ pos) len)
                             (high-surrogate-p (char input pos))
                             (low-surrogate-p (char input (1+ pos))))
                        2 1)))))
    nil)))
