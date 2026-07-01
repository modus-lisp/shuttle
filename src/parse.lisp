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
(defun kw? (v) (and (eq (cur-type) :ident) (string= (cur-val) v)))
(defun eat (v) (if (punct? v) (adv) (js-throw (format nil "Expected '~a'" v))))
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

(defun parse-program (src)
  (let ((*toks* (tokenize src)) (*pos* 0) (stmts '()))
    (loop until (eq (cur-type) :eof) do (push (parse-stmt) stmts))
    (list :block (nreverse stmts))))

;;; ---- statements ----
(defun parse-stmt ()
  (cond
    ((punct? "{") (parse-block))
    ((or (kw? "var") (kw? "let") (kw? "const")) (parse-var))
    ((kw? "function") (parse-function nil))
    ((kw? "class") (parse-class nil))
    ((kw? "return") (adv) (let ((e (if (or (punct? ";") (punct? "}") (eq (cur-type) :eof)) *undefined-ast*
                                       (parse-expr 1)))) (opt ";") (list :return e)))
    ((kw? "if") (parse-if))
    ((kw? "while") (adv) (eat "(") (let ((c (parse-expr 1))) (eat ")") (list :while c (parse-stmt))))
    ((kw? "for") (parse-for))
    ((kw? "switch") (parse-switch))
    ((kw? "break") (adv) (opt ";") (list :break))
    ((kw? "continue") (adv) (opt ";") (list :continue))
    ((kw? "try") (parse-try))
    ((kw? "throw") (adv) (let ((e (parse-expr 1))) (opt ";") (list :throw e)))
    ((punct? ";") (adv) (list :empty))
    (t (let ((e (parse-expr 1))) (opt ";") (list :expr e)))))

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
  (adv) (eat "(")
  ;; detect for-in / for-of: parse the head, then look for `in`/`of`
  (let ((decl-kind nil) (init nil))
    (cond ((punct? ";") (setf init nil))
          ((or (kw? "var") (kw? "let") (kw? "const"))
           (setf decl-kind (cur-val)) (adv)
           (let ((name (parse-binding-target)))
             (cond ((or (kw? "in") (kw? "of"))
                    (let ((kind (cur-val))) (adv)
                      (let ((obj (parse-expr 1))) (eat ")")
                        (return-from parse-for
                          (list (if (string= kind "in") :for-in :for-of)
                                (list :var decl-kind (list (cons name nil))) obj (parse-stmt))))))
                   (t (let ((decls (list (cons name (when (opt "=") (parse-expr 2))))))
                        (loop while (opt ",")
                              do (let ((n2 (parse-binding-target)))
                                   (push (cons n2 (when (opt "=") (parse-expr 2))) decls)))
                        (setf init (list :var decl-kind (nreverse decls))))))))
          (t (let ((e (parse-expr 1)))
               (cond ((or (kw? "in") (kw? "of"))
                      (let ((kind (cur-val))) (adv)
                        (let ((obj (parse-expr 1))) (eat ")")
                          (return-from parse-for
                            (list (if (string= kind "in") :for-in :for-of) e obj (parse-stmt))))))
                     (t (setf init (list :expr e)))))))
    (eat ";")
    (let ((test (unless (punct? ";") (parse-expr 1)))) (eat ";")
      (let ((update (unless (punct? ")") (parse-expr 1)))) (eat ")")
        (list :for init test update (parse-stmt))))))

(defun parse-switch ()
  (adv) (eat "(") (let ((disc (parse-expr 1))) (eat ")") (eat "{")
    (let ((cases '()) (default nil))
      (loop until (punct? "}") do
        (flet ((body () (let ((s '()))
                          (loop until (or (kw? "case") (kw? "default") (punct? "}")) do (push (parse-stmt) s))
                          (nreverse s))))
          (cond ((kw? "case") (adv) (let ((e (parse-expr 1))) (eat ":") (push (cons e (body)) cases)))
                ((kw? "default") (adv) (eat ":") (setf default (body)))
                (t (js-throw "malformed switch")))))
      (eat "}") (list :switch disc (nreverse cases) default))))

(defun parse-try ()
  (adv) (let ((blk (parse-block)) (param nil) (catch nil) (fin nil))
          (when (kw? "catch") (adv)
            (when (punct? "(") (adv) (setf param (cur-val)) (adv) (eat ")"))
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
    ((eq (cur-type) :ident) (prog1 (cur-val) (adv)))
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
               ((punct? "*") (adv) (setf gen t))
               ((and (kw? "get") (not (member-name-terminator-p))) (adv) (setf kind :get))
               ((and (kw? "set") (not (member-name-terminator-p))) (adv) (setf kind :set)))
             (let ((key (parse-class-key)))
               (cond
                 ((punct? "(")                   ; method / accessor / constructor
                  (let ((fn (parse-method-tail (key-name key) gen)))
                    (if (and (not static) (eq kind :method)
                             (eq (car key) :lit) (string= (second key) "constructor"))
                        (setf ctor fn)
                        (push (list :method kind key fn static) members))))
                 (t                              ; field: key [= init] ;
                  (let ((init (when (opt "=") (parse-expr 2))))
                    (opt ";")
                    (push (list :field key init static) members)))))))))
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
    ((eq (cur-type) :ident) (list :lit (prog1 (cur-val) (adv))))
    (t (js-throw (make-native-error "SyntaxError" "Unexpected token in class member")))))

(defun parse-lhs-expr ()
  "A left-hand-side expression (for `extends` clause): member/call chain, no
   binary operators."
  (parse-member (parse-primary)))

(defvar *in-generator* nil)   ; is `yield` a keyword in the current parse context?

(defun parse-function (exprp)
  (adv)                                       ; 'function'
  (let ((gen (opt "*")))                      ; function* -> generator
    (let ((name (when (eq (cur-type) :ident) (prog1 (cur-val) (adv)))))
      (eat "(")
      (let ((params (parse-param-list)))
        (eat ")")
        (let* ((*in-generator* gen) (body (parse-block)))
          (declare (ignore exprp))
          (if gen (list :genfunc name params body) (list :func name params body)))))))

;;; ---- expressions (Pratt) ----
(defun assignable-target-p (node op)
  "Is NODE a valid AssignmentTarget for assignment operator OP?
   Simple (=): identifiers, member accesses, and (for plain =) destructuring
   patterns. Compound ops require a simple reference."
  (case (car node)
    (:ident t)
    (:member t)
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
          ;; assignment (right-assoc), lowest
          ((and (eq tt :punct) (member tv *assignops* :test #'string=) (>= 1 (1- min-bp)))
           (unless (assignable-target-p left tv)
             (js-throw (make-native-error "SyntaxError" "Invalid left-hand side in assignment")))
           (adv) (setf left (list :assign tv left (parse-expr 1))))
          ;; conditional ?:
          ((and (punct? "?") (>= 2 min-bp))
           (adv) (let ((then (parse-expr 1))) (eat ":")
                   (setf left (list :cond left then (parse-expr 2)))))
          ;; instanceof / in (keyword operators, relational precedence)
          ((and (eq tt :ident) (member tv '("instanceof" "in") :test #'string=) (>= 9 min-bp))
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
      ((kw? "typeof") (adv) (list :unary "typeof" (parse-unary)))
      ((kw? "void") (adv) (list :unary "void" (parse-unary)))
      ((kw? "delete") (adv) (list :delete (parse-unary)))
      ((kw? "new") (adv) (let* ((callee (parse-member (parse-primary) nil)) ; member, but NOT the call
                                (newexpr (list :new callee (if (punct? "(") (parse-args) '()))))
                           (parse-member newexpr)))    ; trailing .m() / [k] / () after new
      ((or (punct? "++") (punct? "--")) (let ((op tv)) (adv) (list :update op t (parse-unary))))
      (t (parse-postfix)))))

(defun parse-postfix ()
  (let ((e (parse-member (parse-primary))))
    (if (or (punct? "++") (punct? "--")) (prog1 (list :update (cur-val) nil e) (adv)) e)))

(defun parse-member (e &optional (allow-call t))   ; . [] () ?. chains + tagged templates
  (loop
    (cond ((punct? ".") (adv) (setf e (list :member e (list :str (cur-val)) nil)) (adv))
          ((punct? "?.")
           (adv)
           (cond ((punct? "(") (setf e (list :ocall e (parse-args))))    ; ?.( args )
                 ((punct? "[") (adv) (let ((k (parse-expr 1))) (eat "]")
                                       (setf e (list :omember e k t))))  ; ?.[ expr ]
                 (t (setf e (list :omember e (list :str (cur-val)) nil)) (adv)))) ; ?.ident
          ((punct? "[") (adv) (let ((k (parse-expr 1))) (eat "]") (setf e (list :member e k t))))
          ((and allow-call (punct? "(")) (setf e (list :call e (parse-args))))
          ((eq (cur-type) :template)                                     ; tagged template
           (setf e (list :tagged-template e (parse-template-node))))
          (t (return e)))))

(defun parse-args ()
  (eat "(") (let ((args '()))
              (loop until (punct? ")") do
                (if (punct? "...")
                    (progn (adv) (push (list :spread (parse-expr 2)) args))
                    (push (parse-expr 2) args))
                (unless (punct? ")") (eat ",")))
              (eat ")") (nreverse args)))

(defun parse-array-literal ()
  "Array literal with holes ([1,,3] -> nil element) and spread ([...a])."
  (eat "[")
  (let ((elems '()))
    (loop until (punct? "]") do
      (cond
        ((punct? ",") (push nil elems) (adv))         ; elision
        ((punct? "...") (adv) (push (list :spread (parse-expr 2)) elems)
                        (unless (punct? "]") (eat ",")))
        (t (push (parse-expr 2) elems)
           (unless (punct? "]") (eat ",")))))
    (eat "]")
    (list :array (nreverse elems))))

(defun parse-primary ()
  (let ((tt (cur-type)) (tv (cur-val)))
    (cond
      ((eq tt :num) (adv) (list :num tv))
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
      ((kw? "function") (parse-function t))
      ((kw? "class") (parse-class t))
      ((punct? "(") (parse-paren-or-arrow))
      ((punct? "[") (parse-array-literal))
      ((punct? "{") (parse-object-literal))
      ((eq tt :ident)
       (adv) (if (punct? "=>")                  ; id => body  (arrow)
                 (progn (adv) (list :arrow (list tv) (parse-arrow-body)))
                 (list :ident tv)))
      (t (js-throw (format nil "Unexpected token ~a ~s" tt tv))))))

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
  (let ((start *pos*))
    (or (ignore-errors
          (eat "(")
          (let ((params (parse-param-list)))
            (eat ")")
            (when (punct? "=>")
              (adv) (list :arrow params (parse-arrow-body)))))
        (progn
          (setf *pos* start)
          (eat "(")
          (let ((items '()))
            (loop until (punct? ")") do (push (parse-expr 2) items) (unless (punct? ")") (eat ",")))
            (eat ")")
            (setf items (nreverse items))
            (or (car (last items)) (js-throw (make-native-error "SyntaxError" "empty ()"))))))))

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
    ((eq (cur-type) :ident) (list :lit (prog1 (cur-val) (adv))))
    (t (js-throw (make-native-error "SyntaxError" "Unexpected token in object literal")))))

(defun parse-method-tail (name-string &optional gen)
  "Parse `(params){body}` as a function expression AST for a method/accessor.
   When GEN, the body is a generator body (yield is a keyword)."
  (eat "(")
  (let ((params (parse-param-list)))
    (eat ")")
    (let* ((*in-generator* gen) (body (parse-block)))
      (if gen (list :genfunc name-string params body)
          (list :func name-string params body)))))

(defun parse-object-literal ()
  (eat "{")
  (let ((props '()))
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
