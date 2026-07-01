;;;; builtins/regexp.lisp — the RegExp global + RegExp.prototype (test/exec/flags/
;;;; source/lastIndex/@@match/@@replace/@@split/@@search). Uses src/regex.lisp.
(in-package #:shuttle)

;;; Well-known symbols Symbol.match/replace/search/split/matchAll. The kernel
;;; only creates iterator/toPrimitive/etc., so we create these here and hang them
;;; on the Symbol constructor + stash module-globals for delegation.
(defvar *symbol-match* nil)
(defvar *symbol-replace* nil)
(defvar *symbol-search* nil)
(defvar *symbol-split* nil)
(defvar *symbol-match-all* nil)
(defvar *symbol-species* nil)
;; RegExp intrinsics (so String methods can construct/dispatch)
(defvar *regexp-ctor* nil)
(defvar *regexp-proto* nil)

;;; ---------------------------------------------------------------------------
;;; Internal-slot access: the compiled-regex lives in the object's internal plist
;;; under :regex; the ORIGINAL source/flags strings under :re-source/:re-flags.
;;; ---------------------------------------------------------------------------
(defun regexp-object-p (o)
  (and (js-object-p o) (getf (js-object-internal o) :regex-set)))
(defun regexp-compiled (o) (getf (js-object-internal o) :regex))
(defun (setf regexp-compiled) (v o)
  (setf (getf (js-object-internal o) :regex) v
        (getf (js-object-internal o) :regex-set) t))

(defun this-regexp (this &optional (what "RegExp.prototype method"))
  (unless (regexp-object-p this)
    (js-throw (make-native-error "TypeError" (format nil "~a called on non-RegExp" what))))
  this)

;;; ---------------------------------------------------------------------------
;;; Building a RegExp object from a pattern + flags
;;; ---------------------------------------------------------------------------
(defun make-regexp-object (realm pattern flags &optional proto)
  "Compile PATTERN/FLAGS (CL strings) and return a fresh RegExp object.
   Signals JS SyntaxError on bad input."
  (let* ((cre (regex-compile pattern flags))
         (o (make-object :proto (or proto *regexp-proto* (realm-object-proto realm))
                         :class "RegExp")))
    (setf (regexp-compiled o) cre)
    (put o "lastIndex" 0d0 :enumerable nil :writable t :configurable nil)
    o))

(defun regexp-source-of (o)
  (let ((cre (regexp-compiled o)))
    (if cre (compiled-regex-source cre) "(?:)")))

(defun escape-regex-source (src)
  "The value of RegExp.prototype.source: '/' the empty pattern is '(?:)', and
   line terminators / '/' are escaped so the result re-lexes as a literal."
  (if (string= src "") "(?:)"
      (with-output-to-string (out)
        (loop for c across src
              with prev-backslash = nil do
          (cond
            (prev-backslash (write-char c out) (setf prev-backslash nil))
            ((char= c #\\) (write-char c out) (setf prev-backslash t))
            ((char= c #\/) (write-string "\\/" out))
            ((char= c #\Newline) (write-string "\\n" out))
            ((char= c #\Return) (write-string "\\r" out))
            ((char= c (code-char #x2028)) (write-string "\\u2028" out))
            ((char= c (code-char #x2029)) (write-string "\\u2029" out))
            (t (write-char c out)))))))

;;; ---------------------------------------------------------------------------
;;; exec — the core matching entry point
;;; ---------------------------------------------------------------------------
(defun regexp-flags-string (o)
  "The flags of the RegExp object O, read from its own getters (spec-observable
   ordering d,g,i,m,s,u,y). Here we read the compiled flags directly."
  (let ((cre (regexp-compiled o)))
    (if cre (compiled-regex-flags cre) "")))

(defun set-lastindex-or-throw (re v)
  "Set(RE, \"lastIndex\", V, true): a failed [[Set]] (e.g. non-writable) throws."
  (when (eq (js-set re "lastIndex" v) *false*)
    (js-throw (make-native-error "TypeError" "cannot set lastIndex"))))

(defun regexp-do-exec (realm re s)
  "RegExpBuiltinExec: run RE against string S honoring lastIndex for g/y.
   Returns a JS match array or *null*."
  (declare (ignorable realm))
  (let* ((cre (regexp-compiled re))
         (global (compiled-regex-global cre))
         (sticky (compiled-regex-sticky cre))
         ;; Step 4: Get(R,"lastIndex") is ALWAYS performed (observable via a
         ;; poisoned/valueOf lastIndex). The value is only USED as the starting
         ;; position (and written back) when global or sticky is set.
         (last-index (to-length (js-get re "lastIndex")))
         (li (if (or global sticky) (truncate last-index) 0)))
    (when (> li (length s))
      (when (or global sticky) (set-lastindex-or-throw re 0d0))
      (return-from regexp-do-exec *null*))
    (multiple-value-bind (end caps) (regex-exec cre s li)
      (if (null end)
          (progn (when (or global sticky) (set-lastindex-or-throw re 0d0)) *null*)
          (let ((mstart (car (aref caps 0))))
            (when (or global sticky) (set-lastindex-or-throw re (float end 1d0)))
            (build-match-array realm cre s caps mstart))))))

(defun build-match-array (realm cre s caps mstart)
  (let* ((n (length caps))
         (arr (make-array-object nil))
         (has-groups (compiled-regex-group-names cre)))
    (put arr "length" (float n 1d0))
    (dotimes (i n)
      (let ((cap (aref caps i)))
        (put arr (princ-to-string i)
             (if (null cap) *undefined* (subseq s (car cap) (cdr cap))))))
    (put arr "index" (float mstart 1d0))
    (put arr "input" s)
    ;; groups object (named captures)
    (if has-groups
        (let ((g (make-object :proto *null*))
              (seen '()))
          ;; A name may map to several (duplicate-named) group indices; expose it
          ;; once, preferring whichever index actually captured.
          (dolist (nm (compiled-regex-group-names cre))
            (let* ((name (car nm)) (idx (cdr nm)) (cap (aref caps idx)))
              (cond
                ((not (member name seen :test #'string=))
                 (push name seen)
                 (put g name (if (null cap) *undefined* (subseq s (car cap) (cdr cap)))))
                (cap
                 (put g name (subseq s (car cap) (cdr cap)))))))
          (put arr "groups" g))
        (put arr "groups" *undefined*))
    ;; hasIndices -> 'indices' array of [start,end] pairs
    (when (compiled-regex-has-indices cre)
      (let ((ind (make-array-object nil)))
        (put ind "length" (float n 1d0))
        (dotimes (i n)
          (let ((cap (aref caps i)))
            (put ind (princ-to-string i)
                 (if (null cap) *undefined*
                     (make-array-object (list (float (car cap) 1d0) (float (cdr cap) 1d0)))))))
        (if has-groups
            (let ((g (make-object :proto *null*))
                  (seen '()))
              (dolist (nm (compiled-regex-group-names cre))
                (let* ((name (car nm)) (idx (cdr nm)) (cap (aref caps idx)))
                  (flet ((pair () (make-array-object (list (float (car cap) 1d0) (float (cdr cap) 1d0)))))
                    (cond
                      ((not (member name seen :test #'string=))
                       (push name seen)
                       (put g name (if (null cap) *undefined* (pair))))
                      (cap (put g name (pair)))))))
              (put ind "groups" g))
            (put ind "groups" *undefined*))
        (put arr "indices" ind)))
    arr))

(defun regexp-exec-abstract (realm re s)
  "RegExpExec(R, S): call R.exec if it's a callable custom exec, else builtin."
  (let ((exec (js-get re "exec")))
    (if (js-callable-p exec)
        (let ((r (js-call exec re (list s))))
          (unless (or (eq r *null*) (js-object-p r))
            (js-throw (make-native-error "TypeError" "exec must return object or null")))
          r)
        (progn
          (this-regexp re "RegExp.prototype.exec")
          (regexp-do-exec realm re s)))))

;;; ---------------------------------------------------------------------------
;;; @@ symbol method implementations (the routing targets for String methods)
;;; ---------------------------------------------------------------------------
(defun advance-string-index (s index unicode)
  (if (and unicode (< (1+ index) (length s))
           (<= #xD800 (char-code (char s index)) #xDBFF)
           (<= #xDC00 (char-code (char s (1+ index))) #xDFFF))
      (+ index 2)
      (+ index 1)))

(defun regexp-unicode-p (re)
  (js-truthy (js-get re "unicode")))

(defun symbol-match-impl (realm re args)
  (let* ((s (to-string (arg 0 args)))
         ;; Spec: read the flags STRING once (Get(rx,"flags")); derive
         ;; global/unicode from it rather than reading separate getters.
         (flags (to-string (js-get re "flags")))
         (global (and (find #\g flags) t)))
    (if (not global)
        (regexp-exec-abstract realm re s)
        (progn
          (js-set re "lastIndex" 0d0)
          (let ((results '()) (unicode (and (or (find #\u flags) (find #\v flags)) t)))
            (loop
              (let ((r (regexp-exec-abstract realm re s)))
                (when (eq r *null*) (return))
                (let ((m (to-string (js-get r "0"))))
                  (push m results)
                  (when (string= m "")
                    (let ((li (to-length (js-get re "lastIndex"))))
                      (js-set re "lastIndex" (float (advance-string-index s (truncate li) unicode) 1d0)))))))
            (if (null results) *null*
                (make-array-object (nreverse results))))))))

(defun symbol-search-impl (realm re args)
  (let* ((s (to-string (arg 0 args)))
         (previous (js-get re "lastIndex")))
    (unless (same-value previous 0d0) (js-set re "lastIndex" 0d0))
    (let ((r (regexp-exec-abstract realm re s)))
      (let ((current (js-get re "lastIndex")))
        (unless (same-value current previous) (js-set re "lastIndex" previous)))
      (if (eq r *null*) -1d0 (js-get r "index")))))

(defun symbol-split-impl (realm re args)
  (let* ((s (to-string (arg 0 args)))
         (limit-arg (arg 1 args))
         (flags (to-string (js-get re "flags")))
         (unicode (or (find #\u flags) nil))
         (new-flags (if (find #\y flags) flags (concatenate 'string flags "y")))
         (splitter (js-construct (species-regexp-ctor realm re) (list re new-flags)))
         (lim (if (js-undefined-p limit-arg) #xFFFFFFFF (to-uint32 limit-arg)))
         (out '()) (size (length s)))
    (when (zerop lim) (return-from symbol-split-impl (make-array-object '())))
    (when (zerop size)
      (let ((z (regexp-exec-abstract realm splitter s)))
        (return-from symbol-split-impl
          (make-array-object (if (eq z *null*) (list s) '())))))
    (let ((p 0) (q 0))
      (loop while (< q size) do
        (js-set splitter "lastIndex" (float q 1d0))
        (let ((z (regexp-exec-abstract realm splitter s)))
          (if (eq z *null*)
              (setf q (advance-string-index s q unicode))
              (let ((e (min (truncate (to-length (js-get splitter "lastIndex"))) size)))
                (if (= e p)
                    (setf q (advance-string-index s q unicode))
                    (progn
                      (push (subseq s p q) out)
                      (when (>= (length out) lim)
                        (return-from symbol-split-impl (make-array-object (nreverse out))))
                      ;; push captured groups
                      (let ((ncap (truncate (to-length (js-get z "length")))))
                        (loop for i from 1 below ncap do
                          (push (js-get z (princ-to-string i)) out)
                          (when (>= (length out) lim)
                            (return-from symbol-split-impl (make-array-object (nreverse out))))))
                      (setf p e q p)))))))
      (push (subseq s p size) out)
      (make-array-object (nreverse out)))))

(defun default-regexp-ctor (realm)
  (or *regexp-ctor* (js-get (realm-global realm) "RegExp")))

(defun species-constructor (realm o default-ctor)
  "SpeciesConstructor(O, defaultConstructor)."
  (let ((c (js-get o "constructor")))
    (if (js-undefined-p c)
        default-ctor
        (progn
          (unless (js-object-p c) (js-throw (make-native-error "TypeError" "constructor is not an object")))
          (let ((s (if (js-symbol-p *symbol-species*) (js-get c *symbol-species*) *undefined*)))
            (if (js-null-or-undef s)
                default-ctor
                (if (and (js-object-p s) (js-object-construct s)) s
                    (js-throw (make-native-error "TypeError" "@@species is not a constructor")))))))))

(defun species-regexp-ctor (realm re)
  (species-constructor realm re (default-regexp-ctor realm)))

(defun get-substitution (matched s position captures named replacement)
  "Perform $-substitution: $$ $& $` $' $n $nn $<name>. MATCHED is the matched
   string, POSITION its start in S, CAPTURES a list of capture strings/undefined
   (1-based conceptually: captures[0] is group 1), NAMED the groups object or nil."
  (let ((out (make-string-output-stream))
        (rlen (length replacement))
        (tail-pos (+ position (length matched)))
        (i 0))
    (loop while (< i rlen) do
      (let ((c (char replacement i)))
        (if (and (char= c #\$) (< (1+ i) rlen))
            (let ((d (char replacement (1+ i))))
              (cond
                ((char= d #\$) (write-char #\$ out) (incf i 2))
                ((char= d #\&) (write-string matched out) (incf i 2))
                ((char= d #\`) (write-string (subseq s 0 position) out) (incf i 2))
                ((char= d #\') (write-string (subseq s (min tail-pos (length s))) out) (incf i 2))
                ((char= d #\<)
                 (if named
                     (let ((close (position #\> replacement :start (+ i 2))))
                       (if close
                           (let* ((name (subseq replacement (+ i 2) close))
                                  (v (js-get named name)))
                             (unless (js-undefined-p v) (write-string (to-string v) out))
                             (setf i (1+ close)))
                           (progn (write-char #\$ out) (incf i))))
                     (progn (write-char #\$ out) (incf i))))
                ((digit-char-p d)
                 ;; try two-digit then one-digit
                 (let* ((n-caps (length captures))
                        (two (and (< (+ i 2) rlen) (digit-char-p (char replacement (+ i 2)))))
                        (d2 (and two (+ (* 10 (digit-char-p d)) (digit-char-p (char replacement (+ i 2))))))
                        (d1 (digit-char-p d)))
                   (cond
                     ((and d2 (>= d2 1) (<= d2 n-caps))
                      (let ((cap (nth (1- d2) captures)))
                        (unless (or (null cap) (js-undefined-p cap)) (write-string (to-string cap) out)))
                      (incf i 3))
                     ((and (>= d1 1) (<= d1 n-caps))
                      (let ((cap (nth (1- d1) captures)))
                        (unless (or (null cap) (js-undefined-p cap)) (write-string (to-string cap) out)))
                      (incf i 2))
                     (t (write-char #\$ out) (incf i)))))
                (t (write-char #\$ out) (incf i))))
            (progn (write-char c out) (incf i)))))
    (get-output-stream-string out)))

(defun symbol-replace-impl (realm re args)
  (let* ((s (to-string (arg 0 args)))
         (replace-value (arg 1 args))
         (functional (js-callable-p replace-value))
         (rep-str (unless functional (to-string replace-value)))
         ;; Spec: read the flags STRING once; derive global/unicode from it.
         (flags (to-string (js-get re "flags")))
         (global (and (find #\g flags) t))
         (unicode (and (or (find #\u flags) (find #\v flags)) t)))
    (when global (js-set re "lastIndex" 0d0))
    (let ((results '()))
      ;; collect all matches
      (loop
        (let ((r (regexp-exec-abstract realm re s)))
          (when (eq r *null*) (return))
          (push r results)
          (unless global (return))
          (let ((m (to-string (js-get r "0"))))
            (when (string= m "")
              (let ((li (to-length (js-get re "lastIndex"))))
                (js-set re "lastIndex"
                        (float (advance-string-index s (truncate li) unicode) 1d0)))))))
      (setf results (nreverse results))
      (let ((accumulated (make-string-output-stream)) (next-source 0))
        (dolist (result results)
          (let* ((n-caps (max 0 (1- (truncate (to-length (js-get result "length"))))))
                 (matched (to-string (js-get result "0")))
                 (position (min (max 0 (to-int-index (js-get result "index"))) (length s)))
                 (captures (loop for i from 1 to n-caps
                                 collect (let ((c (js-get result (princ-to-string i))))
                                           (if (js-undefined-p c) *undefined* (to-string c)))))
                 (named-groups (js-get result "groups"))
                 (replacement
                   (if functional
                       (to-string
                        (js-call replace-value *undefined*
                                 (append (list matched)
                                         captures
                                         (list (float position 1d0) s)
                                         (unless (js-undefined-p named-groups) (list named-groups)))))
                       (get-substitution matched s position captures
                                         (unless (js-undefined-p named-groups) named-groups)
                                         rep-str))))
            (when (>= position next-source)
              (write-string (subseq s next-source position) accumulated)
              (write-string replacement accumulated)
              (setf next-source (+ position (length matched))))))
        (when (< next-source (length s))
          (write-string (subseq s next-source) accumulated))
        (get-output-stream-string accumulated)))))

;;; matchAll: returns a RegExp String Iterator
(defun symbol-match-all-impl (realm re args)
  (let* ((s (to-string (arg 0 args)))
         (flags (to-string (js-get re "flags")))
         (matcher (js-construct (species-regexp-ctor realm re) (list re flags))))
    (js-set matcher "lastIndex" (to-length (js-get re "lastIndex")))
    (make-regexp-string-iterator realm matcher s
                                 (and (find #\g flags) t)
                                 (and (find #\u flags) t))))

(defun make-regexp-string-iterator (realm re s global unicode)
  (let ((done nil)
        (it (make-object :proto (realm-object-proto realm) :class "RegExp String Iterator")))
    (put it *symbol-iterator*
         (native-function realm "[Symbol.iterator]" (lambda (this args) (declare (ignore args)) this) 0)
         :enumerable nil :writable t :configurable t)
    (put it "next"
         (native-function realm "next"
           (lambda (this args) (declare (ignore this args))
             (let ((res (make-object :proto (realm-object-proto realm))))
               (if done
                   (progn (put res "value" *undefined*) (put res "done" *true*))
                   (let ((m (regexp-exec-abstract realm re s)))
                     (if (eq m *null*)
                         (progn (setf done t) (put res "value" *undefined*) (put res "done" *true*))
                         (progn
                           (when (not global) (setf done t))
                           (when global
                             (let ((ms (to-string (js-get m "0"))))
                               (when (string= ms "")
                                 (let ((li (to-length (js-get re "lastIndex"))))
                                   (js-set re "lastIndex"
                                           (float (advance-string-index s (truncate li) unicode) 1d0))))))
                           (put res "value" m) (put res "done" *false*)))))
               res)) 0)
         :enumerable nil :writable t :configurable t)
    it))

;;; ---------------------------------------------------------------------------
;;; RegExp.escape  (ES2025 EncodeForRegExpEscape)
;;; ---------------------------------------------------------------------------
(defparameter +regex-syntax-chars+
  '(#\^ #\$ #\\ #\. #\* #\+ #\? #\( #\) #\[ #\] #\{ #\} #\| #\/))
;; "other punctuators" the spec always hex-escapes so the result stays inert.
(defparameter +regex-escape-punctuators+
  ",-=<>#&!%:;@~'`\"")

(defun regex-escape-hex (code)
  "Return \\xHH for code <= 0xFF, else \\uHHHH, with lowercase hex digits."
  (if (<= code #xFF)
      (format nil "\\x~(~2,'0x~)" code)
      (format nil "\\u~(~4,'0x~)" code)))

(defun regex-escapable-p (c)
  "T if code point C must be hex-escaped by RegExp.escape (whitespace, C0/C1
   control, lone surrogate, or a listed punctuator)."
  (let ((code (char-code c)))
    (or (find c +regex-escape-punctuators+)
        (rx-space-p c)                  ; WhiteSpace + LineTerminator set
        (<= code #x1F) (<= #x7F code #x9F)
        (<= #xD800 code #xDFFF))))       ; lone surrogate code unit

(defun regexp-escape-string (v)
  "RegExp.escape(S): throw TypeError unless S is a String; return an escaped
   copy safe to embed literally in a pattern."
  (unless (stringp v)
    (js-throw (make-native-error "TypeError" "RegExp.escape argument must be a string")))
  (with-output-to-string (out)
    (loop for i from 0 below (length v)
          for c = (char v i) do
      (cond
        ;; First code point that is ASCII alnum: hex-escape so the escaped string
        ;; can never merge with a preceding token or begin an identifier-ish run.
        ((and (= i 0)
              (or (char<= #\0 c #\9) (char<= #\a c #\z) (char<= #\A c #\Z)))
         (write-string (regex-escape-hex (char-code c)) out))
        ((member c +regex-syntax-chars+)
         (write-char #\\ out) (write-char c out))
        ((char= c #\Tab) (write-string "\\t" out))
        ((char= c #\Newline) (write-string "\\n" out))
        ((char= c (code-char 11)) (write-string "\\v" out))
        ((char= c #\Page) (write-string "\\f" out))
        ((char= c #\Return) (write-string "\\r" out))
        ((regex-escapable-p c) (write-string (regex-escape-hex (char-code c)) out))
        (t (write-char c out))))))

;;; ---------------------------------------------------------------------------
;;; Install
;;; ---------------------------------------------------------------------------
(defun install-regexp (realm)
  (let* ((op (realm-object-proto realm))
         (proto (make-object :proto op :class "Object")))
    (setf *regexp-proto* proto)
    ;; --- well-known symbols ---
    (let ((sym-ctor (js-get (realm-global realm) "Symbol")))
      (setf *symbol-match*     (make-js-symbol "Symbol.match")
            *symbol-replace*   (make-js-symbol "Symbol.replace")
            *symbol-search*    (make-js-symbol "Symbol.search")
            *symbol-split*     (make-js-symbol "Symbol.split")
            *symbol-match-all* (make-js-symbol "Symbol.matchAll"))
      ;; reuse an existing Symbol.species if the kernel made one, else create it
      (let ((existing-species (and (js-object-p sym-ctor)
                                   (let ((s (ignore-errors (js-get sym-ctor "species"))))
                                     (and (js-symbol-p s) s)))))
        (setf *symbol-species* (or existing-species (make-js-symbol "Symbol.species"))))
      (when (js-object-p sym-ctor)
        (def-value sym-ctor "match" *symbol-match* :writable nil :configurable nil)
        (def-value sym-ctor "replace" *symbol-replace* :writable nil :configurable nil)
        (def-value sym-ctor "search" *symbol-search* :writable nil :configurable nil)
        (def-value sym-ctor "split" *symbol-split* :writable nil :configurable nil)
        (def-value sym-ctor "matchAll" *symbol-match-all* :writable nil :configurable nil)
        (unless (and (ignore-errors (js-get sym-ctor "species"))
                     (js-symbol-p (js-get sym-ctor "species")))
          (def-value sym-ctor "species" *symbol-species* :writable nil :configurable nil))))
    ;; --- constructor ---
    (let ((ctor (native-function realm "RegExp"
                  (lambda (this args) (declare (ignore this))
                    ;; called as a function: NewTarget := active function (RegExp),
                    ;; the short-circuit path applies.
                    (regexp-construct realm args :call)) 2)))
      (setf *regexp-ctor* ctor)
      (setf (js-object-construct ctor)
            ;; called with new: no short-circuit, always create a fresh object.
            (lambda (args nt) (declare (ignore nt)) (regexp-construct realm args nil)))
      (def-value ctor "prototype" proto :writable nil :configurable nil)
      (def-value proto "constructor" ctor)
      ;; Symbol.species getter
      (when (js-symbol-p *symbol-species*)
        (put-accessor ctor *symbol-species*
                      :get (native-function realm "get [Symbol.species]"
                             (lambda (this args) (declare (ignore args)) this) 0)
                      :enumerable nil :configurable t))
      ;; RegExp.escape (ES2025): escape a string for literal use in a pattern.
      (def-value ctor "escape"
                 (native-function realm "escape"
                   (lambda (this args) (declare (ignore this))
                     (regexp-escape-string (arg 0 args))) 1)
                 :writable t :configurable t)
      (install-regexp-proto realm proto)
      (define-global realm "RegExp" ctor))))

(defun is-regexp (v)
  "IsRegExp(V): object with truthy @@match, or (if @@match undefined) a RegExp
   exotic object."
  (and (js-object-p v)
       (let ((m (and *symbol-match* (js-get v *symbol-match*))))
         (if (js-undefined-p m)
             (regexp-object-p v)
             (js-truthy m)))))

(defun regexp-construct (realm args new-target)
  (let* ((pattern (arg 0 args))
         (flags (arg 1 args))
         (pattern-is-regexp (is-regexp pattern)))
    ;; short-circuit (call path only): RegExp(re) with flags undefined and
    ;; re.constructor === RegExp returns re unchanged.
    (when (and (eq new-target :call) pattern-is-regexp (js-undefined-p flags))
      (let ((pc (js-get pattern "constructor")))
        (when (same-value pc *regexp-ctor*)
          (return-from regexp-construct pattern))))
    (multiple-value-bind (src fl)
        (cond
          ;; a genuine RegExp exotic: read its internal source/flags directly
          ((regexp-object-p pattern)
           (values (regexp-source-of pattern)
                   (if (js-undefined-p flags)
                       (regexp-flags-string pattern)
                       (to-string flags))))
          ;; a regexp-like object (has @@match): read source/flags via getters
          (pattern-is-regexp
           (values (to-string (js-get pattern "source"))
                   (if (js-undefined-p flags)
                       (to-string (js-get pattern "flags"))
                       (to-string flags))))
          ((js-undefined-p pattern)
           (values "" (if (js-undefined-p flags) "" (to-string flags))))
          (t
           (values (to-string pattern)
                   (if (js-undefined-p flags) "" (to-string flags)))))
      (make-regexp-object realm src fl))))

(defun install-regexp-proto (realm proto)
  ;; exec
  (def-method realm proto "exec" 1 (this args)
    (this-regexp this "RegExp.prototype.exec")
    (regexp-do-exec realm this (to-string (arg 0 args))))
  ;; test
  (def-method realm proto "test" 1 (this args)
    (this-regexp this "RegExp.prototype.test")
    (js-bool (not (eq (regexp-exec-abstract realm this (to-string (arg 0 args))) *null*))))
  ;; toString
  (def-method realm proto "toString" 0 (this args)
    (unless (js-object-p this) (js-throw (make-native-error "TypeError" "not an object")))
    (concatenate 'string "/" (to-string (js-get this "source")) "/" (to-string (js-get this "flags"))))
  ;; compile (Annex B): recompile in place
  (def-method realm proto "compile" 2 (this args)
    (this-regexp this "RegExp.prototype.compile")
    (let* ((pattern (arg 0 args)) (flags (arg 1 args)))
      (multiple-value-bind (src fl)
          (if (regexp-object-p pattern)
              (progn
                (unless (js-undefined-p flags)
                  (js-throw (make-native-error "TypeError" "cannot supply flags when constructing one RegExp from another")))
                (values (regexp-source-of pattern) (regexp-flags-string pattern)))
              (values (if (js-undefined-p pattern) "" (to-string pattern))
                      (if (js-undefined-p flags) "" (to-string flags))))
        (setf (regexp-compiled this) (regex-compile src fl))
        (js-set this "lastIndex" 0d0)
        this)))
  ;; --- getters ---
  (flet ((flag-getter (name char)
           (def-getter realm proto name
             (lambda (this args) (declare (ignore args))
               (cond
                 ((regexp-object-p this)
                  (js-bool (find char (regexp-flags-string this))))
                 ((eq this proto) *undefined*)
                 (t (js-throw (make-native-error "TypeError" "not a RegExp"))))))))
    (flag-getter "global" #\g)
    (flag-getter "ignoreCase" #\i)
    (flag-getter "multiline" #\m)
    (flag-getter "dotAll" #\s)
    (flag-getter "sticky" #\y)
    (flag-getter "unicode" #\u)
    (flag-getter "unicodeSets" #\v)
    (flag-getter "hasIndices" #\d))
  (def-getter realm proto "source"
    (lambda (this args) (declare (ignore args))
      (cond
        ((regexp-object-p this) (escape-regex-source (regexp-source-of this)))
        ((eq this proto) "(?:)")
        (t (js-throw (make-native-error "TypeError" "not a RegExp"))))))
  (def-getter realm proto "flags"
    (lambda (this args) (declare (ignore args))
      (unless (js-object-p this) (js-throw (make-native-error "TypeError" "not an object")))
      (with-output-to-string (out)
        (when (js-truthy (js-get this "hasIndices")) (write-char #\d out))
        (when (js-truthy (js-get this "global")) (write-char #\g out))
        (when (js-truthy (js-get this "ignoreCase")) (write-char #\i out))
        (when (js-truthy (js-get this "multiline")) (write-char #\m out))
        (when (js-truthy (js-get this "dotAll")) (write-char #\s out))
        (when (js-truthy (js-get this "unicode")) (write-char #\u out))
        (when (js-truthy (js-get this "unicodeSets")) (write-char #\v out))
        (when (js-truthy (js-get this "sticky")) (write-char #\y out)))))
  ;; --- @@ symbol methods ---
  (put proto *symbol-match*
       (native-function realm "[Symbol.match]"
         (lambda (this args)
           (unless (js-object-p this) (js-throw (make-native-error "TypeError" "not an object")))
           (symbol-match-impl realm this args)) 1)
       :enumerable nil :writable t :configurable t)
  (put proto *symbol-search*
       (native-function realm "[Symbol.search]"
         (lambda (this args)
           (unless (js-object-p this) (js-throw (make-native-error "TypeError" "not an object")))
           (symbol-search-impl realm this args)) 1)
       :enumerable nil :writable t :configurable t)
  (put proto *symbol-split*
       (native-function realm "[Symbol.split]"
         (lambda (this args)
           (unless (js-object-p this) (js-throw (make-native-error "TypeError" "not an object")))
           (symbol-split-impl realm this args)) 2)
       :enumerable nil :writable t :configurable t)
  (put proto *symbol-replace*
       (native-function realm "[Symbol.replace]"
         (lambda (this args)
           (unless (js-object-p this) (js-throw (make-native-error "TypeError" "not an object")))
           (symbol-replace-impl realm this args)) 2)
       :enumerable nil :writable t :configurable t)
  (put proto *symbol-match-all*
       (native-function realm "[Symbol.matchAll]"
         (lambda (this args)
           (unless (js-object-p this) (js-throw (make-native-error "TypeError" "not an object")))
           (symbol-match-all-impl realm this args)) 1)
       :enumerable nil :writable t :configurable t))

(register-builtin-installer 'install-regexp)
