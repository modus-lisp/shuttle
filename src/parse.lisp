;;;; parse.lisp — a Pratt parser: expressions (full precedence) + core
;;;; statements. AST = lists tagged by keyword. (Destructuring, classes,
;;;; generators, modules, full ASI: TODO — the grammar grows from here.)
(in-package #:shuttle)

(defvar *toks*) (defvar *pos*)
(defun cur () (aref *toks* *pos*))
(defun cur-type () (car (cur)))
(defun cur-val () (cdr (cur)))
(defun adv () (prog1 (cur) (incf *pos*)))
(defun punct? (v) (and (eq (cur-type) :punct) (string= (cur-val) v)))
(defun check-escaped-ident ()
  "Early error: the current token is an escaped reserved word used in Identifier
   (binding/reference) position, which is not allowed (a keyword may not be spelled
   with a unicode escape). Legal as an IdentifierName (property/key/method name)."
  (when (and *escaped-idents* (gethash *pos* *escaped-idents*))
    (js-throw (make-native-error "SyntaxError"
               (format nil "Keyword '~a' must not contain escaped characters" (cur-val))))))
(defun kw? (v) (and (eq (cur-type) :ident) (string= (cur-val) v)))
(defun eat (v) (if (punct? v) (adv) (js-throw (make-native-error "SyntaxError" (format nil "Expected '~a'" v)))))
(defun opt (v) (when (punct? v) (adv) t))

(defparameter *binops*
  ;; op -> binding power (left); equality/relational/etc.
  '(("||" . 3) ("&&" . 4) ("|" . 5) ("^" . 6) ("&" . 7)
    ("==" . 8) ("!=" . 8) ("===" . 8) ("!==" . 8)
    ("<" . 9) (">" . 9) ("<=" . 9) (">=" . 9)
    ("<<" . 10) (">>" . 10) (">>>" . 10)
    ("+" . 11) ("-" . 11) ("*" . 12) ("/" . 12) ("%" . 12)
    ("**" . 14)))                       ; ** right-assoc, handled specially below
(defparameter *assignops* '("=" "+=" "-=" "*=" "/=" "%=" "**="
                            "<<=" ">>=" ">>>=" "&=" "|=" "^=" "&&=" "||=" "??="))
(defparameter *nullish-op* "??")        ; parsed with logical precedence
(defvar *no-in* nil)          ; NoIn context: `in` is NOT a binary op (for-in head LHS)

(defun parse-program (src)
  (multiple-value-bind (toks escaped) (tokenize src)
    (let ((*toks* toks) (*escaped-idents* escaped) (*pos* 0) (stmts '()))
      (loop until (eq (cur-type) :eof) do (push (parse-stmt) stmts))
      (list :block (nreverse stmts)))))

;;; ---- statements ----
(defun parse-stmt ()
  (cond
    ((punct? "{") (parse-block))
    ((or (kw? "var") (kw? "let") (kw? "const")) (parse-var))
    ((kw? "function") (parse-function nil))
    ((async-function-follows-p) (adv) (parse-function nil t))   ; async function decl
    ((kw? "class") (parse-class nil))
    ((kw? "return") (adv) (let ((e (if (or (punct? ";") (punct? "}") (eq (cur-type) :eof)) *undefined-ast*
                                       (parse-expr 1)))) (opt ";") (list :return e)))
    ((kw? "if") (parse-if))
    ((kw? "while") (adv) (eat "(") (let ((c (parse-expr 1))) (eat ")") (list :while c (parse-stmt))))
    ((kw? "do") (adv) (let ((body (parse-stmt)))
                        (unless (kw? "while") (js-throw (make-native-error "SyntaxError" "Expected 'while' after do-body")))
                        (adv) (eat "(") (let ((c (parse-expr 1))) (eat ")") (opt ";")
                          (list :do-while c body))))
    ((kw? "for") (parse-for))
    ((kw? "switch") (parse-switch))
    ((kw? "break") (adv) (let ((l (when (label-ident-follows-p) (prog1 (cur-val) (adv))))) (opt ";") (list :break l)))
    ((kw? "continue") (adv) (let ((l (when (label-ident-follows-p) (prog1 (cur-val) (adv))))) (opt ";") (list :continue l)))
    ((kw? "with") (adv) (eat "(") (let ((obj (parse-expr 1))) (eat ")") (list :with obj (parse-stmt))))
    ((kw? "try") (parse-try))
    ((kw? "throw") (adv) (let ((e (parse-expr 1))) (opt ";") (list :throw e)))
    ((punct? ";") (adv) (list :empty))
    ((labeled-stmt-follows-p)
     (let ((name (cur-val))) (adv) (adv)          ; consume IDENT and ':'
       (list :label name (parse-stmt))))
    (t (let ((e (parse-expr 1))) (opt ";") (list :expr e)))))

(defparameter *reserved-labels*
  '("break" "case" "catch" "class" "const" "continue" "default" "delete" "do"
    "else" "extends" "false" "finally" "for" "function" "if" "import" "in"
    "instanceof" "new" "null" "return" "super" "switch" "this" "throw" "true"
    "try" "typeof" "var" "void" "while" "with"))

(defun labeled-stmt-follows-p ()
  "Is the current position `IDENT :` (a labeled statement)? IDENT must not be a
   reserved word."
  (and (eq (cur-type) :ident)
       (not (member (cur-val) *reserved-labels* :test #'string=))
       (let ((nxt (aref *toks* (1+ *pos*))))
         (and (eq (car nxt) :punct) (string= (cdr nxt) ":")))))

(defun label-ident-follows-p ()
  "After `break`/`continue`, is the current token a label identifier (not a
   reserved word / statement terminator)?"
  (and (eq (cur-type) :ident)
       (not (member (cur-val) *reserved-labels* :test #'string=))))

(defparameter *undefined-ast* '(:undefined))
(defun parse-block () (eat "{") (let ((s '())) (loop until (punct? "}") do (push (parse-stmt) s)) (eat "}")
                        (list :block (nreverse s))))
(defun parse-if () (adv) (eat "(") (let ((c (parse-expr 1))) (eat ")")
                    (let ((then (parse-stmt)) (else (when (kw? "else") (adv) (parse-stmt))))
                      (list :if c then else))))
(defun parse-var-decl ()                 ; no trailing semicolon (for use in `for`)
  (let ((kind (cur-val))) (adv)
    (let ((decls '()))
      (loop (let ((tgt (parse-binding-target)))    ; name string OR (:apat ..)/(:opat ..)
              (push (cons tgt (when (opt "=") (parse-expr 2))) decls))
            (unless (opt ",") (return)))
      (list :var kind (nreverse decls)))))
(defun parse-var () (prog1 (parse-var-decl) (opt ";")))

(defun parse-for ()
  (adv)
  (let ((await (when (kw? "await") (adv) t)))   ; for await (... of ...)
    (when (and await (not *in-async*))
      (js-throw (make-native-error "SyntaxError" "for await is only valid in async functions")))
    (return-from parse-for (parse-for-tail await)))
  (parse-for-tail nil))

(defun parse-for-tail (await)
  (eat "(")
  ;; detect for-in / for-of: parse the head, then look for `in`/`of`
  (let ((decl-kind nil) (init nil))
    (cond ((punct? ";") (setf init nil))
          ((or (kw? "var") (kw? "let") (kw? "const"))
           (setf decl-kind (cur-val)) (adv)
           (let ((name (parse-binding-target)))
             (cond ((or (kw? "in") (kw? "of"))
                    (let ((kind (cur-val))) (adv)
                      (let ((obj (parse-expr 1))) (eat ")")
                        (return-from parse-for-tail
                          (list (cond ((string= kind "in") :for-in) (await :for-await-of) (t :for-of))
                                (list :var decl-kind (list (cons name nil))) obj (parse-stmt))))))
                   (t (let ((decls (list (cons name (when (opt "=") (parse-expr 2))))))
                        (loop while (opt ",")
                              do (let ((n2 (parse-binding-target)))
                                   (push (cons n2 (when (opt "=") (parse-expr 2))) decls)))
                        (setf init (list :var decl-kind (nreverse decls))))))))
          (t (let ((e (let ((*no-in* t)) (parse-expr 1))))
               (cond ((or (kw? "in") (kw? "of"))
                      (let ((kind (cur-val))) (adv)
                        (unless (assignable-target-p e "=")
                          (js-throw (make-native-error "SyntaxError"
                                     "Invalid left-hand side in for-in/of")))
                        (let ((obj (parse-expr 1))) (eat ")")
                          (return-from parse-for-tail
                            (list (cond ((string= kind "in") :for-in) (await :for-await-of) (t :for-of))
                                  e obj (parse-stmt))))))
                     (t (setf init (list :expr e)))))))
    (eat ";")
    (let ((test (unless (punct? ";") (parse-expr 1)))) (eat ";")
      (let ((update (unless (punct? ")") (parse-expr 1)))) (eat ")")
        (list :for init test update (parse-stmt))))))

(defun parse-switch ()
  (adv) (eat "(") (let ((disc (parse-expr 1))) (eat ")") (eat "{")
    ;; Clauses are kept in SOURCE ORDER — fall-through (incl. default-before-case)
    ;; needs the physical clause sequence. A clause is (TEST-or-:default . BODY).
    (let ((clauses '()) (seen-default nil))
      (loop until (punct? "}") do
        (flet ((body () (let ((s '()))
                          (loop until (or (kw? "case") (kw? "default") (punct? "}")) do (push (parse-stmt) s))
                          (nreverse s))))
          (cond ((kw? "case") (adv) (let ((e (parse-expr 1))) (eat ":") (push (cons e (body)) clauses)))
                ((kw? "default")
                 (when seen-default (js-throw (make-native-error "SyntaxError" "more than one default clause in switch")))
                 (setf seen-default t)
                 (adv) (eat ":") (push (cons :default (body)) clauses))
                (t (js-throw (make-native-error "SyntaxError" "malformed switch"))))))
      (eat "}") (list :switch disc (nreverse clauses)))))

(defun parse-try ()
  (adv) (let ((blk (parse-block)) (param nil) (catch nil) (fin nil))
          (when (kw? "catch") (adv)
            ;; Catch binding is a BindingIdentifier OR a BindingPattern
            ;; (ES2015): `catch([a,b])` / `catch({x})` destructure the thrown
            ;; value.  PARSE-BINDING-TARGET yields a name string or an :apat/:opat
            ;; pattern node, which the compiler's :try binds via BIND-TARGET.
            (when (punct? "(") (adv) (setf param (parse-binding-target)) (eat ")"))
            (setf catch (parse-block)))
          (when (kw? "finally") (adv) (setf fin (parse-block)))
          (list :try blk param catch fin)))
(defun parse-param-list ()
  "Parse `( ... )` param list. Consumes the opening `(` must already be eaten
   by caller? No — here we DON'T eat `(`; caller does. Returns a list of params,
   each: NAME-STRING | (:default NAME EXPR) | (:rest NAME) | (:pat PATTERN [DEFAULT])."
  (let ((params '()))
    (loop until (punct? ")") do
      (cond
        ((punct? "...")
         (adv)
         (let ((tgt (parse-binding-target)))
           (push (list :rest tgt) params))
         (return))                         ; rest must be last
        (t (let ((tgt (parse-binding-target)))
             (if (punct? "=")
                 (progn (adv) (push (list :default tgt (parse-expr 2)) params))
                 (push tgt params)))))
      (unless (punct? ")") (eat ",")))
    (nreverse params)))

(defun parse-binding-target ()
  "A binding target: a plain name, or an array/object destructuring pattern."
  (cond
    ((punct? "[") (parse-array-pattern))
    ((punct? "{") (parse-object-pattern))
    ((eq (cur-type) :ident) (check-escaped-ident) (prog1 (cur-val) (adv)))
    (t (js-throw (make-native-error "SyntaxError" "Invalid binding target")))))

;;; ---- destructuring patterns ----
;;; Pattern AST: (:apat ELEMS) / (:opat PROPS).
;;;   array elem: nil (hole) | TARGET | (:default TARGET EXPR) | (:rest TARGET)
;;;   object prop: (KEYFORM TARGET) | (KEYFORM TARGET DEFAULT) | (:rest NAME)
;;;   TARGET is itself a binding target (name or nested pattern).
(defun parse-array-pattern ()
  (eat "[")
  (let ((elems '()))
    (loop until (punct? "]") do
      (cond
        ((punct? ",") (push nil elems) (adv))   ; hole; consume comma, continue
        ((punct? "...")
         (adv) (push (list :rest (parse-binding-target)) elems)
         (return))
        (t (let ((tgt (parse-binding-target)))
             (if (punct? "=")
                 (progn (adv) (push (list :default tgt (parse-expr 2)) elems))
                 (push tgt elems)))
           (unless (punct? "]") (eat ",")))))
    (eat "]")
    (list :apat (nreverse elems))))

(defun parse-object-pattern ()
  (eat "{")
  (let ((props '()))
    (loop until (punct? "}") do
      (cond
        ((punct? "...")
         (adv) (push (list :rest (ident-or-keyword-name)) props)
         (return))
        (t (let ((key (parse-property-key)))
             (cond
               ((punct? ":")
                (adv) (let ((tgt (parse-binding-target)))
                        (if (punct? "=")
                            (progn (adv) (push (list key tgt (parse-expr 2)) props))
                            (push (list key tgt) props))))
               ((eq (car key) :lit)         ; shorthand {x} or {x = d}
                (if (punct? "=")
                    (progn (adv) (push (list key (second key) (parse-expr 2)) props))
                    (push (list key (second key)) props)))
               (t (js-throw (make-native-error "SyntaxError" "Invalid object pattern")))))))
      (unless (punct? "}") (eat ",")))
    (eat "}")
    (list :opat (nreverse props))))

;;; ---- classes ----
;;; AST: (:class NAME SUPER-EXPR-OR-NIL MEMBERS)
;;;   member: (:ctor FUNC)
;;;           (:method KIND KEY FUNC STATIC)  ; KIND in :method :get :set
;;;           (:field KEY INIT-OR-NIL STATIC)
(defun parse-class (exprp)
  (declare (ignore exprp))
  (adv)                                          ; 'class'
  (let ((name (when (and (eq (cur-type) :ident) (not (kw? "extends")))
                (prog1 (cur-val) (adv))))
        (super nil))
    (when (kw? "extends") (adv) (setf super (parse-lhs-expr)))
    (eat "{")
    (let ((members '()) (ctor nil))
      (loop until (punct? "}") do
        (cond
          ((punct? ";") (adv))                   ; empty element
          (t
           (let ((static nil) (gen nil) (kind :method))
             ;; `static` prefix (unless it's the member name `static(){}` / `static = ...`)
             (when (and (kw? "static") (not (member-name-terminator-p)))
               (adv) (setf static t))
             (cond
               ;; static initialization block: `static { ... }`
               ((and static (punct? "{"))
                (let ((*in-generator* nil) (*in-async* nil))
                  (push (list :static-block (parse-block)) members)))
               (t
                (cond
                  ((and (kw? "async") (async-method-follows-p))   ; async / async* method
                   (adv) (if (punct? "*") (progn (adv) (setf gen :async-gen)) (setf gen :async)))
                  ((punct? "*") (adv) (setf gen t))
                  ((and (kw? "get") (not (member-name-terminator-p))) (adv) (setf kind :get))
                  ((and (kw? "set") (not (member-name-terminator-p))) (adv) (setf kind :set)))
                (let ((key (parse-class-key)))
                  (cond
                    ((punct? "(")                 ; method / accessor / constructor
                     (let ((fn (parse-method-tail (key-name key) gen)))
                       (if (and (not static) (eq kind :method)
                                (eq (car key) :lit) (string= (second key) "constructor"))
                           (setf ctor fn)
                           (push (list :method kind key fn static) members))))
                    (t                            ; field: key [= init] ;
                     (let ((init (when (opt "=") (parse-expr 2))))
                       (opt ";")
                       (push (list :field key init static) members)))))))))))
      (eat "}")
      (list :class name super (nreverse members) ctor))))

(defun member-name-terminator-p ()
  "After a possible modifier keyword (static/get/set), is the NEXT token one that
   means the keyword was actually the member NAME (i.e. `(`, `=`, `;`, `}`)?"
  (let ((nxt (aref *toks* (1+ *pos*))))
    (and (eq (car nxt) :punct)
         (member (cdr nxt) '("(" "=" ";" "}") :test #'string=))))

(defun parse-class-key ()
  "A class member key: identifier/string/number/computed. Private names (#x) not
   fully supported; treated as a string key."
  (cond
    ((punct? "[") (adv) (let ((e (parse-expr 2))) (eat "]") (list :computed e)))
    ((eq (cur-type) :str) (list :lit (prog1 (cur-val) (adv))))
    ((eq (cur-type) :num) (list :lit (number-to-string (prog1 (cur-val) (adv)))))
    ((eq (cur-type) :bigint) (list :lit (bigint-to-string (prog1 (cur-val) (adv)))))
    ((private-name-token-p) (list :private (prog1 (cur-val) (adv))))
    ((eq (cur-type) :ident) (list :lit (prog1 (cur-val) (adv))))
    (t (js-throw (make-native-error "SyntaxError" "Unexpected token in class member")))))

(defun private-name-token-p ()
  "Is the current token a #private-name lexeme?"
  (and (eq (cur-type) :ident) (> (length (cur-val)) 0) (char= (char (cur-val) 0) #\#)))

(defun parse-lhs-expr ()
  "A left-hand-side expression (for `extends` clause): member/call chain, no
   binary operators."
  (parse-member (parse-primary)))

(defvar *in-generator* nil)   ; is `yield` a keyword in the current parse context?
(defvar *in-async* nil)       ; is `await` a keyword in the current parse context?

(defun async-function-follows-p ()
  "At an `async` identifier token: does a FunctionDeclaration/Expression follow on
   the same line (no LineTerminator between `async` and `function`)? We don't track
   newlines in the token stream, so approximate: the next token is `function`."
  (and (kw? "async")
       (let ((nxt (aref *toks* (1+ *pos*))))
         (and (eq (car nxt) :ident) (string= (cdr nxt) "function")))))

(defun parse-function (exprp &optional async)
  (adv)                                       ; 'function'
  (let ((gen (opt "*")))                      ; function* -> generator
    (let ((name (when (eq (cur-type) :ident) (prog1 (cur-val) (adv)))))
      (eat "(")
      (let* ((*in-generator* gen) (*in-async* async)
             (params (parse-param-list)))
        (eat ")")
        (let ((body (parse-block)))
          (declare (ignore exprp))
          (cond
            ((and gen async) (list :asyncgenfunc name params body))
            (gen (list :genfunc name params body))
            (async (list :asyncfunc name params body))
            (t (list :func name params body))))))))

;;; ---- expressions (Pratt) ----
(defun assignable-target-p (node op)
  "Is NODE a valid AssignmentTarget for assignment operator OP?
   Simple (=): identifiers, member accesses, and (for plain =) destructuring
   patterns. Compound ops require a simple reference."
  (case (car node)
    (:ident t)
    (:member t)
    (:private-member t)
    ((:array :object) (string= op "="))     ; destructuring only for plain assignment
    (t nil)))

(defun parse-expr (min-bp)
  ;; yield: an AssignmentExpression-level form, only inside a generator body.
  (when (and *in-generator* (kw? "yield") (<= min-bp 2))
    (adv)
    (let ((delegate (opt "*")))
      ;; yield with no argument: followed by a token that can't start an expression
      (if (or delegate (not (yield-argument-follows-p)))
          (if delegate (return-from parse-expr (list :yield* (parse-expr 2)))
              (return-from parse-expr (list :yield nil)))
          (return-from parse-expr (list :yield (parse-expr 2))))))
  (let ((left (parse-unary)))
    (loop
      (let ((tt (cur-type)) (tv (cur-val)))
        (cond
          ;; sequence / comma operator: lowest precedence of all, only at the
          ;; Expression level (min-bp <= 1). AssignmentExpression contexts use
          ;; min-bp 2 (args, array elements, declarator inits, ternary branches),
          ;; so the comma there stays a delimiter, never a sequence.
          ((and (eq tt :punct) (string= tv ",") (<= min-bp 1))
           (adv)
           (let ((rest (list (parse-expr 2))))
             (loop while (punct? ",") do (adv) (push (parse-expr 2) rest))
             (setf left (list* :seq left (nreverse rest)))))
          ;; assignment (right-assoc), lowest
          ((and (eq tt :punct) (member tv *assignops* :test #'string=) (>= 1 (1- min-bp)))
           (unless (assignable-target-p left tv)
             (js-throw (make-native-error "SyntaxError" "Invalid left-hand side in assignment")))
           (adv) (setf left (list :assign tv left (parse-expr 2))))
          ;; conditional ?:
          ((and (punct? "?") (>= 2 min-bp))
           (adv) (let ((then (parse-expr 1))) (eat ":")
                   (setf left (list :cond left then (parse-expr 2)))))
          ;; instanceof / in (keyword operators, relational precedence). In a NoIn
          ;; context (for-in head LHS), `in` is not consumed as a binary op so the
          ;; for-tail can recognize it as the iteration keyword.
          ((and (eq tt :ident) (string= tv "instanceof") (>= 9 min-bp))
           (adv) (setf left (list :bin tv left (parse-expr 10))))
          ((and (eq tt :ident) (string= tv "in") (>= 9 min-bp) (not *no-in*))
           (adv) (setf left (list :bin tv left (parse-expr 10))))
          ;; nullish coalescing ?? (logical, short-circuits on null/undefined)
          ((and (eq tt :punct) (string= tv "??") (>= 5 min-bp))
           (adv) (setf left (list :logical "??" left (parse-expr 6))))
          ;; ** right-associative (recurse at same bp, not bp+1)
          ((and (eq tt :punct) (string= tv "**") (>= 14 min-bp))
           (adv) (setf left (list :bin "**" left (parse-expr 14))))
          ;; binary / logical
          ((and (eq tt :punct) (assoc tv *binops* :test #'string=))
           (let ((bp (cdr (assoc tv *binops* :test #'string=))))
             (if (< bp min-bp) (return)
                 (progn (adv) (setf left (let ((r (parse-expr (1+ bp))))
                                           (if (member tv '("&&" "||") :test #'string=)
                                               (list :logical tv left r) (list :bin tv left r))))))))
          (t (return)))))
    left))

(defun yield-argument-follows-p ()
  "After `yield`, does an expression argument follow (vs. bare yield)?"
  (let ((tt (cur-type)) (tv (cur-val)))
    (not (or (eq tt :eof)
             (and (eq tt :punct) (member tv '(")" "]" "}" ";" "," ":") :test #'string=))))))

(defun parse-unary ()
  (let ((tt (cur-type)) (tv (cur-val)))
    (cond
      ((and (eq tt :punct) (member tv '("!" "-" "+" "~") :test #'string=)) (adv) (list :unary tv (parse-unary)))
      ((and *in-async* (kw? "await")) (adv) (list :await (parse-unary)))
      ((kw? "typeof") (adv) (list :unary "typeof" (parse-unary)))
      ((kw? "void") (adv) (list :unary "void" (parse-unary)))
      ((kw? "delete") (adv) (list :delete (parse-unary)))
      ((kw? "new")
       (adv)
       (if (punct? ".")                              ; new.target meta-property
           (progn (adv)
                  (unless (and (eq (cur-type) :ident) (equal (cur-val) "target"))
                    (js-throw (make-native-error "SyntaxError" "expected 'target' after 'new.'")))
                  (adv)
                  (parse-member (list :new-target)))  ; new.target can be a member base: new.target.foo
           (let* ((callee (parse-member (parse-primary) nil)) ; member, but NOT the call
                  (newexpr (list :new callee (if (punct? "(") (parse-args) '()))))
             (parse-member newexpr))))    ; trailing .m() / [k] / () after new
      ((or (punct? "++") (punct? "--")) (let ((op tv)) (adv) (list :update op t (parse-unary))))
      (t (parse-postfix)))))

(defun parse-postfix ()
  (let ((e (parse-member (parse-primary))))
    (if (or (punct? "++") (punct? "--")) (prog1 (list :update (cur-val) nil e) (adv)) e)))

(defun parse-member (e &optional (allow-call t))   ; . [] () ?. chains + tagged templates
  (loop
    (cond ((punct? ".")
           (adv)
           (if (private-name-token-p)
               (setf e (list :private-member e (prog1 (cur-val) (adv))))
               (progn (setf e (list :member e (list :str (cur-val)) nil)) (adv))))
          ((punct? "?.")
           (adv)
           (cond ((punct? "(") (setf e (list :ocall e (parse-args))))    ; ?.( args )
                 ((punct? "[") (adv) (let ((k (let ((*no-in* nil)) (parse-expr 1)))) (eat "]")
                                       (setf e (list :omember e k t))))  ; ?.[ expr ]
                 ((private-name-token-p)
                  (setf e (list :oprivate-member e (prog1 (cur-val) (adv)))))
                 (t (setf e (list :omember e (list :str (cur-val)) nil)) (adv)))) ; ?.ident
          ((punct? "[") (adv) (let ((k (let ((*no-in* nil)) (parse-expr 1)))) (eat "]") (setf e (list :member e k t))))
          ((and allow-call (punct? "(")) (setf e (list :call e (parse-args))))
          ((eq (cur-type) :template)                                     ; tagged template
           (setf e (list :tagged-template e (parse-template-node))))
          (t (return e)))))

(defun parse-args ()
  (eat "(") (let ((args '()) (*no-in* nil))
              (loop until (punct? ")") do
                (if (punct? "...")
                    (progn (adv) (push (list :spread (parse-expr 2)) args))
                    (push (parse-expr 2) args))
                (unless (punct? ")") (eat ",")))
              (eat ")") (nreverse args)))

(defun parse-array-literal ()
  "Array literal with holes ([1,,3] -> nil element) and spread ([...a])."
  (eat "[")
  (let ((elems '()) (*no-in* nil))
    (loop until (punct? "]") do
      (cond
        ((punct? ",") (push nil elems) (adv))         ; elision
        ((punct? "...") (adv) (push (list :spread (parse-expr 2)) elems)
                        (unless (punct? "]") (eat ",")))
        (t (push (parse-expr 2) elems)
           (unless (punct? "]") (eat ",")))))
    (eat "]")
    (list :array (nreverse elems))))

(defun %next-punct-p (v)
  (let ((nx (aref *toks* (1+ *pos*))))
    (and (eq (car nx) :punct) (string= (cdr nx) v))))

(defun parse-primary ()
  (let ((tt (cur-type)) (tv (cur-val)))
    (cond
      ((eq tt :num) (adv) (list :num tv))
      ((eq tt :bigint) (adv) (list :bigint tv))
      ((eq tt :str) (adv) (list :str tv))
      ((eq tt :regex) (adv) (list :regex (car tv) (cdr tv)))   ; (:regex pattern flags)
      ((eq tt :template) (parse-template-node))
      ((kw? "true") (adv) '(:bool t)) ((kw? "false") (adv) '(:bool nil))
      ((kw? "null") (adv) '(:null)) ((kw? "undefined") (adv) '(:undefined))
      ((kw? "this") (adv) '(:this))
      ((kw? "super")
       (adv)
       (cond
         ((punct? "(") (list :super-call (parse-args)))               ; super(...)
         ((punct? ".") (adv) (prog1 (list :super-member (list :str (cur-val)) nil) (adv)))
         ((punct? "[") (adv) (let ((k (parse-expr 1))) (eat "]") (list :super-member k t)))
         (t (js-throw (make-native-error "SyntaxError" "Unexpected 'super'")))))
      ;; `import(...)` and `import.meta` are EXPRESSIONS.  Without these two arms `import` falls
      ;; through to the identifier case and the program dies at runtime with "import is not
      ;; defined" -- a name lookup for a keyword, which is how it read before modules existed.
      ((and (kw? "import") (%next-punct-p "("))
       (adv) (eat "(")
       (let ((spec (parse-expr 2)))
         (opt ",")                                  ; the import-attributes argument, accepted
         (unless (punct? ")") (parse-expr 2))       ; ...and evaluated for effect, not honoured
         (eat ")")
         (list :dynamic-import spec)))
      ((and (kw? "import") (%next-punct-p "."))
       (adv) (adv)
       (unless (kw? "meta")
         (js-throw (make-native-error "SyntaxError" "Expected 'meta' after 'import.'")))
       (adv)
       (list :import-meta))
      ((kw? "function") (parse-function t))
      ((async-function-follows-p) (adv) (parse-function t t))   ; async function expression
      ((and (kw? "async") (async-arrow-follows-p)) (parse-async-arrow))
      ((kw? "class") (parse-class t))
      ((private-name-token-p)          ; only valid as LHS of `#x in obj`
       (list :private-ref (prog1 (cur-val) (adv))))
      ((punct? "(") (parse-paren-or-arrow))
      ((punct? "[") (parse-array-literal))
      ((punct? "{") (parse-object-literal))
      ((eq tt :ident)
       ;; `await` is a reserved word (not a usable identifier) in async context.
       (when (and *in-async* (string= tv "await"))
         (js-throw (make-native-error "SyntaxError" "await is reserved in async functions")))
       (check-escaped-ident)      ; an escaped reserved word can't be an Identifier
       (adv) (if (punct? "=>")                  ; id => body  (arrow)
                 (progn (adv) (list :arrow (list tv) (parse-arrow-body)))
                 (list :ident tv)))
      (t (js-throw (make-native-error "SyntaxError" (format nil "Unexpected token ~a ~s" tt tv)))))))

(defun async-arrow-follows-p ()
  "At `async`: is this an async arrow head — `async IDENT =>` or `async (`
   (with a `=>` after the parens)? Approximate by peeking one token."
  (and (kw? "async")
       (let ((nxt (aref *toks* (1+ *pos*))))
         (or (and (eq (car nxt) :ident)                 ; async x => ...
                  (not (string= (cdr nxt) "function")))
             (and (eq (car nxt) :punct) (string= (cdr nxt) "("))))))  ; async ( ... ) =>

(defun parse-async-arrow ()
  "Parse an async arrow: `async ident => body` or `async (params) => body`.
   On a bare `async ( ... )` that is NOT an arrow, backtrack to a call expression."
  (let ((start *pos*))
    (adv)                                        ; 'async'
    (cond
      ;; async ident => body
      ((and (eq (cur-type) :ident) (not (punct? "(")))
       (let ((param (cur-val)))
         (adv)
         (if (punct? "=>")
             (progn (adv) (let ((*in-async* t)) (list :async-arrow (list param) (parse-arrow-body))))
             (progn (setf *pos* start) (parse-async-as-ident)))))
      ;; async ( params ) => body   (speculative; backtrack to a call if no =>)
      ((punct? "(")
       (or (ignore-errors
             (let ((*in-async* t))
               (eat "(")
               (let ((params (parse-param-list)))
                 (eat ")")
                 (when (punct? "=>")
                   (adv) (list :async-arrow params (parse-arrow-body))))))
           (progn (setf *pos* start) (parse-async-as-ident))))
      (t (setf *pos* start) (parse-async-as-ident)))))

(defun parse-async-as-ident ()
  "`async` used as a plain identifier (or the callee of `async(...)`)."
  (adv) (list :ident "async"))

(defun sub-parse-expr (toks)
  "Parse a full expression from a pre-tokenized vector (template substitution)."
  (let ((*toks* toks) (*pos* 0))
    (prog1 (parse-expr 1)
      (unless (eq (cur-type) :eof)
        (js-throw (make-native-error "SyntaxError" "Unexpected token in template expression"))))))

(defun template-parts->node (parts)
  "PARTS is the lexer's list of (:str cooked raw) and (:expr toks). Build
   (:template (COOKED...) (RAW...) (EXPR-AST...))."
  (let ((cooked '()) (raw '()) (exprs '()))
    (dolist (p parts)
      (ecase (car p)
        (:str (push (second p) cooked) (push (third p) raw))
        (:expr (push (sub-parse-expr (second p)) exprs))))
    (list :template (nreverse cooked) (nreverse raw) (nreverse exprs))))

(defun parse-template-node ()
  (let ((parts (cur-val))) (adv) (template-parts->node parts)))

(defun parse-arrow-body ()
  (if (punct? "{") (parse-block) (list :block (list (list :return (parse-expr 2))))))

(defun parse-paren-or-arrow ()
  ;; ( ... ); if followed by =>, its contents are arrow params (which may include
  ;; defaults, rest, and destructuring patterns). Speculatively parse as a param
  ;; list; on failure, backtrack and parse as a parenthesized expression.
  (let ((start *pos*) (*no-in* nil))
    (or (ignore-errors
          (eat "(")
          (let ((params (parse-param-list)))
            (eat ")")
            (when (punct? "=>")
              (adv) (list :arrow params (parse-arrow-body)))))
        (progn
          (setf *pos* start)
          (eat "(")
          (when (punct? ")") (js-throw (make-native-error "SyntaxError" "empty ()")))
          (prog1 (parse-expr 1) (eat ")"))))))

(defun ident-or-keyword-name ()
  "Consume an identifier/keyword token as a plain name string (property key context)."
  (if (eq (cur-type) :ident) (prog1 (cur-val) (adv))
      (js-throw (make-native-error "SyntaxError" "Expected property name"))))

(defun parse-property-key ()
  "Parse a property key. Returns (:lit STRING) or (:computed EXPR)."
  (cond
    ((punct? "[") (adv) (let ((e (parse-expr 2))) (eat "]") (list :computed e)))
    ((eq (cur-type) :str) (list :lit (prog1 (cur-val) (adv))))
    ((eq (cur-type) :num) (list :lit (number-to-string (prog1 (cur-val) (adv)))))
    ((eq (cur-type) :bigint) (list :lit (bigint-to-string (prog1 (cur-val) (adv)))))
    ((eq (cur-type) :ident) (list :lit (prog1 (cur-val) (adv))))
    (t (js-throw (make-native-error "SyntaxError" "Unexpected token in object literal")))))

(defun async-method-follows-p ()
  "At `async` in a method context: is it the async-method modifier (followed by a
   key or `*`) rather than a member named `async` (followed by `(` `:` `,` `}` `=`)?"
  (let ((nxt (aref *toks* (1+ *pos*))))
    (not (and (eq (car nxt) :punct)
              (member (cdr nxt) '("(" ":" "," "}" "=" ";") :test #'string=)))))

(defun parse-method-tail (name-string &optional gen)
  "Parse `(params){body}` as a function expression AST for a method/accessor.
   GEN: nil=plain, t=generator, :async=async method, :async-gen=async generator."
  (eat "(")
  (let* ((generatorp (member gen '(t :async-gen)))
         (asyncp (member gen '(:async :async-gen)))
         (*in-generator* generatorp) (*in-async* asyncp)
         (params (parse-param-list)))
    (eat ")")
    (let ((body (parse-block)))
      (cond
        ((eq gen :async-gen) (list :asyncgenfunc name-string params body))
        ((eq gen :async) (list :asyncfunc name-string params body))
        (generatorp (list :genfunc name-string params body))
        ;; concise method / accessor: same shape as :func but NOT constructable
        ;; (new'ing it is a TypeError) — a distinct node so hoisting never treats it
        ;; as a function declaration.
        (t (list :method-func name-string params body))))))

(defun parse-object-literal ()
  (eat "{")
  (let ((props '()) (*no-in* nil))
    (loop until (punct? "}") do
      (cond
        ;; spread: ...expr
        ((punct? "...")
         (adv) (push (list :spread (parse-expr 2)) props))
        ;; get/set accessor: `get key(){}` — but only if `get`/`set` is followed by a key
        ((and (kw? "get") (accessor-follows-p))
         (adv) (let ((key (parse-property-key)))
                 (push (list :get key (parse-method-tail (key-name key))) props)))
        ((and (kw? "set") (accessor-follows-p))
         (adv) (let ((key (parse-property-key)))
                 (push (list :set key (parse-method-tail (key-name key))) props)))
        ;; async method / async generator method: `async key(){}` / `async *key(){}`
        ((and (kw? "async") (async-method-follows-p))
         (adv)
         (let ((agen (opt "*")))
           (let ((key (parse-property-key)))
             (push (list :init key (parse-method-tail (key-name key) (if agen :async-gen :async))) props))))
        ;; generator method: *key(...){...}
        ((punct? "*")
         (adv) (let ((key (parse-property-key)))
                 (push (list :init key (parse-method-tail (key-name key) t)) props)))
        (t
         (let ((key (parse-property-key)))
           (cond
             ;; method: key(...){...}
             ((punct? "(")
              (push (list :init key (parse-method-tail (key-name key))) props))
             ;; key: value  (literal __proto__: v sets the prototype, per B.3.1)
             ((punct? ":")
              (adv)
              (if (and (eq (car key) :lit) (string= (second key) "__proto__"))
                  (push (list :proto (parse-expr 2)) props)
                  (push (list :init key (parse-expr 2)) props)))
             ;; shorthand {x} or {x = default} (the latter only valid in patterns; store init)
             ((eq (car key) :lit)
              (if (punct? "=")
                  (progn (adv)   ; shorthand with default (destructuring pattern context)
                         (push (list :init key (list :ident (second key)) (parse-expr 2)) props))
                  (push (list :init key (list :ident (second key))) props)))
             (t (js-throw (make-native-error "SyntaxError" "Invalid shorthand property")))))))
      (unless (punct? "}") (eat ",")))
    (eat "}")
    (list :object (nreverse props))))

(defun accessor-follows-p ()
  "After a `get`/`set` token, is there a real accessor key (not `:` `,` `(` `}`)?
   Peek the next token."
  (let ((nxt (aref *toks* (1+ *pos*))))
    (not (and (eq (car nxt) :punct)
              (member (cdr nxt) '(":" "," "(" "}" "=") :test #'string=)))))

(defun key-name (key)
  "A string name for a literal key, or a placeholder for a computed one."
  (if (eq (car key) :lit) (second key) ""))
