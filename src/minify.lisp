;;;; minify.lisp — make the emitted JS smaller by deleting only what carries no meaning.
;;;;
;;;; ============================================================================================
;;;; WHAT THIS DOES, AND THE MUCH LARGER THING IT DELIBERATELY DOES NOT
;;;; ============================================================================================
;;;;
;;;; This is a WHITESPACE-AND-COMMENT minifier.  It re-emits the token stream with the gaps
;;;; between tokens shrunk to nothing wherever nothing depends on them.  It does NOT rename
;;;; identifiers, fold constants, drop dead code, or reorder anything.
;;;;
;;;; That line is not timidity, it is where the risk changes character.  Deleting whitespace can
;;;; be justified one token pair at a time, from the lexical grammar alone: two tokens either run
;;;; together into a different third token or they do not.  RENAMING cannot be justified locally
;;;; at all -- it needs a correct model of every scope in the program, and getting it wrong
;;;; produces a bundle that loads, runs, and is silently wrong somewhere far from the rename.
;;;; The output here is verifiable by construction: TOKENIZE the output and you must get the same
;;;; token sequence back.  MINIFY checks exactly that before it returns, so a bug in the
;;;; separator rules is a build failure rather than a broken page.
;;;;
;;;; ============================================================================================
;;;; THE TWO RULES
;;;; ============================================================================================
;;;;
;;;; 1. SEPARATION.  Two adjacent tokens need a space between them only if the lexer would
;;;;    otherwise read them as one token, or as a comment.  `var x` needs it; `x=1` does not;
;;;;    `a + +b` does, because `++` is a token; `a / /re/` does, because `//` starts a comment.
;;;;    The test is mechanical -- take the last character of one and the first of the next, and
;;;;    ask whether that pair begins any punctuator.
;;;;
;;;; 2. LINE TERMINATORS, which are where the real care is.  A newline is not whitespace in
;;;;    JavaScript: automatic semicolon insertion reads it, so deleting one can change a program's
;;;;    meaning or make it stop parsing.  `a = 1 \n b = 2` needs its newline; without it there is
;;;;    no statement boundary and no valid parse.
;;;;
;;;;    Doing this fully is a PARSER's job -- a real minifier knows where statements end and
;;;;    writes explicit semicolons.  This one does not have that knowledge at this layer, so it
;;;;    uses the half of the question it can answer from the token stream alone: ASI can only ever
;;;;    fire after a token that could END a statement.  After `;` `,` `{` `(` `[` or any operator,
;;;;    no semicolon was ever inserted, so the newline was decoration and goes.  After `)` `]` `}`
;;;;    `++` `--`, an identifier, or a literal, it MIGHT have fired, so the newline stays.
;;;;
;;;;    Keeping a newline costs one byte and gzip pays for almost none of them.  Guessing wrong
;;;;    costs a page that does not load.  The asymmetry decides it.

(in-package #:shuttle)

(defparameter *punct-pairs*
  (let ((h (make-hash-table :test #'equal)))
    ;; Every two-character prefix of a real punctuator: if a pair of adjacent characters is one of
    ;; these, the lexer's maximal munch would swallow both and produce a token that is not there in
    ;; the input.  Built from the lexer's OWN table so the two cannot drift apart.
    (dolist (p *punctuators*)
      (when (>= (length p) 2) (setf (gethash (subseq p 0 2) h) t)))
    ;; Comment openers are not punctuators but merge exactly the same way, and far more
    ;; destructively: `//` eats the rest of the line.
    (setf (gethash "//" h) t (gethash "/*" h) t)
    ;; `<!--` opens an HTML-style line comment in sloppy scripts (Annex B.1.3).
    (setf (gethash "<!" h) t)
    h)
  "Two-character sequences that must never be produced by butting two tokens together.")

(declaim (inline js-ident-char-p))
(defun js-ident-char-p (c)
  "Could C continue an identifier, a number, or a keyword?  Two such characters must not touch."
  (or (alphanumericp c) (char= c #\_) (char= c #\$) (char= c #\\) (>= (char-code c) 128)))

(defun %needs-space-p (prev next prev-type)
  "Would emitting NEXT immediately after PREV change how the result lexes?"
  (let ((a (char prev (1- (length prev)))) (b (char next 0)))
    (or (and (js-ident-char-p a) (js-ident-char-p b))
        (gethash (coerce (list a b) 'string) *punct-pairs*)
        ;; `1 .toString()` -- the lexer reads `1.` as one number, so the property access vanishes.
        (and (member prev-type '(:num :bigint)) (char= b #\.))
        ;; A REGEX ENDS IN `/`, WHICH IS NOT AN IDENTIFIER CHARACTER -- AND ITS FLAGS ARE.  Looking
        ;; only at the last character says these two tokens cannot merge, and they merge anyway:
        ;; `/(?:)/ instanceof RegExp` becomes `/(?:)/instanceof`, one regex whose flags are
        ;; `instanceof`.  The token is greedy to its RIGHT in a way its final character does not
        ;; advertise, so it needs its own clause.  (test262 language/literals/regexp/S7.8.5_A4.1)
        (and (eq prev-type :regex) (js-ident-char-p b)))))

(defun %newline-can-matter-p (prev-type prev)
  "Could automatic semicolon insertion have fired after this token?

Only after something that can END a statement.  Everything else -- an open bracket, a comma, an
operator, a semicolon that already did the job -- leaves the newline as pure decoration."
  (case prev-type
    ((:num :bigint :str :template :regex :ident) t)   ; a value, or a keyword like `return`
    (:punct (and (member prev '(")" "]" "}" "++" "--") :test #'string=) t))
    (t t)))                                            ; unknown: keep it

(defun minify-source (source &key (check t))
  "SOURCE with every comment and every insignificant space, tab and newline removed.

Signals a MINIFY-ERROR if the result does not lex back to the same tokens, which is the whole
safety argument: the transformation is only allowed to delete characters the lexer discards."
  (multiple-value-bind (toks esc starts ends) (tokenize source)
    (declare (ignore esc))
    (let* ((n (1- (fill-pointer toks)))          ; drop :eof
           (out (make-string-output-stream))
           (prev nil) (prev-type nil))
      ;; A hashbang is not a token and not a comment; it is only legal as the first bytes of the
      ;; file, so it is copied through rather than regenerated.
      (when (and (>= (length source) 2) (string= "#!" source :end2 2))
        (let ((eol (position-if #'js-line-terminator-p source)))
          (write-string (subseq source 0 (or eol (length source))) out)
          (write-char #\Newline out)))
      (dotimes (i n)
        (let* ((tok (aref toks i))
               (text (subseq source (aref starts i) (aref ends i)))
               (had-newline (and prev (find-if #'js-line-terminator-p source
                                               :start (aref ends (1- i)) :end (aref starts i)))))
          (when (plusp (length text))
            (cond ((null prev))
                  ((and had-newline (%newline-can-matter-p prev-type prev))
                   (write-char #\Newline out))
                  ((%needs-space-p prev text prev-type) (write-char #\Space out)))
            (write-string text out)
            (setf prev text prev-type (car tok)))))
      (let ((result (get-output-stream-string out)))
        ;; :CHECK NIL is for debugging the emitter itself -- it is the only way to SEE output that
        ;; the check rejects.  Builds never pass it.
        (when check (%check-minify source result))
        result))))

(define-condition minify-error (error)
  ((text :initarg :text :reader minify-error-text))
  (:report (lambda (c s) (write-string (minify-error-text c) s))))

(defun %check-minify (source result)
  "Re-lex RESULT and demand the same token sequence as SOURCE.

This is not a smoke test, it is the correctness argument.  A whitespace minifier is exactly the
claim `these characters do not affect tokenization`, so tokenizing the output and comparing is a
DIRECT check of the claim rather than a proxy for it -- and it runs on every single build, over
whatever the real input happens to be, which no fixture suite can match for coverage."
  (labels ((same (x y)
             ;; EQUAL is not enough: a template token carries the token VECTOR of each `${...}`
             ;; part, and EQUAL compares vectors by identity, so two identical templates compare
             ;; unequal and the check reports a change that did not happen.  Descend instead.
             (cond ((and (vectorp x) (vectorp y) (not (stringp x)))
                    (and (= (length x) (length y))
                         (every #'same x y)))
                   ((and (consp x) (consp y)) (and (same (car x) (car y)) (same (cdr x) (cdr y))))
                   (t (equal x y)))))
  (let ((a (tokenize source))
        (b (handler-case (tokenize result)
             (error (e) (error 'minify-error :text (format nil "output does not lex: ~a" e))))))
    (unless (= (fill-pointer a) (fill-pointer b))
      (error 'minify-error :text (format nil "token count changed: ~d in, ~d out"
                                         (fill-pointer a) (fill-pointer b))))
    (dotimes (i (fill-pointer a))
      (let ((x (aref a i)) (y (aref b i)))
        (unless (same x y)
          (error 'minify-error
                 :text (format nil "token ~d changed: ~s became ~s" i x y))))))))
