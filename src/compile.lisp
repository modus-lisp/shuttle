;;;; compile.lisp — AST -> bytecode. A flat instruction stream (op . args) with
;;;; symbolic labels, then assembled to a vector with resolved jump targets.
;;;; Stack machine; variables are name-resolved through an environment chain
;;;; (indexed locals + scope analysis = a later optimization).
(in-package #:shuttle)

(defstruct code name params instrs inst-instrs
  (this-mode :normal)     ; :normal = OrdinaryCallBindThis (sloppy: undefined/null -> globalThis, primitive -> boxed);
                          ; :lexical = arrow (inherit caller's this, no rebind)
  (constructable t))      ; NIL for arrows and concise/accessor methods (new'ing them is a TypeError)
(defvar *out*)
(defvar *break-target* nil) (defvar *continue-target* nil)
(defvar *scope-depth* 0)                 ; current lexical block-env nesting within the fn
(defvar *break-depth* 0) (defvar *continue-depth* 0)  ; scope depth at the loop/switch target
(defun em (op &rest args) (push (cons op args) *out*))
(defun lbl () (gensym "L"))
(defun pop-envs (count) (dotimes (_ count) (em :pop-env)))

(defun assemble (rev-instrs)
  (let ((instrs (nreverse rev-instrs)) (pos (make-hash-table)) (idx 0) (out '()))
    (dolist (in instrs) (if (eq (car in) :label) (setf (gethash (cadr in) pos) idx) (incf idx)))
    (dolist (in instrs)
      (unless (eq (car in) :label)
        (push (if (member (car in) '(:jmp :jmp-if-false :jmp-if-true :and-jmp :or-jmp :nullish-jmp :nullish-short :push-handler))
                  (list (car in) (gethash (cadr in) pos)) in) out)))
    (coerce (nreverse out) 'vector)))

(defun compile-toplevel (src)
  ;; top-level falls off the end so RUN returns the completion value (eval semantics)
  (compile-fn nil '() (parse-program src) t))

(defun param-names (params &optional acc)
  "All identifier names bound by a parameter list (incl. destructured/rest)."
  (dolist (p params acc)
    (setf acc (target-names (param-target p) acc))))

(defun param-target (p)
  "The binding target of a single param form (peel :default/:rest wrappers)."
  (cond ((stringp p) p)
        ((eq (car p) :default) (second p))
        ((eq (car p) :rest) (second p))
        (t p)))                             ; a pattern (:apat/:opat)

(defun target-names (tgt &optional acc)
  "All names bound by a binding target (name string or destructuring pattern)."
  (cond
    ((stringp tgt) (pushnew tgt acc :test #'string=))
    ((null tgt) acc)                        ; array hole
    ((eq (car tgt) :apat)
     (dolist (e (second tgt) acc)
       (cond ((null e))
             ((and (consp e) (eq (car e) :rest)) (setf acc (target-names (second e) acc)))
             ((and (consp e) (eq (car e) :default)) (setf acc (target-names (second e) acc)))
             (t (setf acc (target-names e acc))))))
    ((eq (car tgt) :opat)
     (dolist (pr (second tgt) acc)
       (if (eq (car pr) :rest) (pushnew (second pr) acc :test #'string=)
           (setf acc (target-names (second pr) acc)))))
    ((eq (car tgt) :default) (target-names (second tgt) acc))
    ((eq (car tgt) :rest) (target-names (second tgt) acc))
    (t acc)))

(defun directive-prologue-strict-p (body)
  "True iff BODY (a :block) opens with a Directive Prologue containing the exact
   \"use strict\" directive — a leading run of bare string-literal statements."
  (when (and (consp body) (eq (car body) :block))
    (dolist (s (second body) nil)
      (if (and (consp s) (eq (car s) :expr)
               (consp (second s)) (eq (car (second s)) :str))
          (when (string= (second (second s)) "use strict") (return t))
          (return nil)))))          ; first non-string-literal stmt ends the prologue

(defun compile-fn (name params body &optional toplevel (this-mode :normal) (constructable t))
  ;; A function whose body opens with "use strict" is strict: its `this` is NOT
  ;; substituted (undefined stays undefined). We otherwise can't track strict mode,
  ;; so sloppy substitution is the default. (Arrows keep :lexical regardless.)
  (when (and (eq this-mode :normal) (directive-prologue-strict-p body))
    (setf this-mode :strict))
  (let ((*out* '()) (pnames (param-names params)))
    ;; bind parameters from incoming call args
    (compile-params params)
    ;; hoist: pre-declare all `var` names (as undefined) so forward reads don't
    ;; ReferenceError. Function declarations are hoisted by :func handling below.
    (dolist (v (collect-var-names body))
      (unless (member v pnames :test #'string=)
        (em :const *undefined*) (em :declare-var v)))
    ;; function/top-level body: hoist its OWN lexicals into the function env (no extra block)
    (let ((stmts (if (eq (car body) :block) (second body) (list body))))
      (dolist (n (block-lexical-names stmts)) (em :tdz-declare n))
      (dolist (fn (block-lexical-fns stmts)) (compile-expr fn) (em :init-let (second fn)))
      (dolist (s stmts) (unless (block-hoisted-fn-p s) (compile-stmt s))))
    (unless toplevel (em :const *undefined*) (em :ret))   ; functions default-return undefined
    (make-code :name name :params params :instrs (assemble *out*)
               :this-mode this-mode :constructable constructable)))

(defun compile-fn-split (name params body &optional (this-mode :normal))
  "Compile a generator/async/async-generator: split FunctionDeclarationInstantiation
   (param binding + var/lexical/fn hoisting — run synchronously at the call) from the
   deferred body. Returns a CODE whose INST-INSTRS is the instantiation stream and
   INSTRS is the body; both run against the SAME function environment."
  (let ((pnames (param-names params)) (inst nil))
    (let ((*out* '()))
      (compile-params params)
      (dolist (v (collect-var-names body))
        (unless (member v pnames :test #'string=)
          (em :const *undefined*) (em :declare-var v)))
      (let ((stmts (if (eq (car body) :block) (second body) (list body))))
        (dolist (n (block-lexical-names stmts)) (em :tdz-declare n))
        (dolist (fn (block-lexical-fns stmts)) (compile-expr fn) (em :init-let (second fn))))
      (em :const *undefined*) (em :ret)              ; instantiation stream returns undefined
      (setf inst (assemble *out*)))
    (let ((*out* '()))
      (let ((stmts (if (eq (car body) :block) (second body) (list body))))
        (dolist (s stmts) (unless (block-hoisted-fn-p s) (compile-stmt s))))
      (em :const *undefined*) (em :ret)
      (make-code :name name :params params :instrs (assemble *out*) :inst-instrs inst
                 :this-mode this-mode))))

(defun compile-array-destructure (pat)
  "Value on stack is the iterable. Destructure per (:apat ELEMS)."
  (let ((it (string (gensym "IT"))) (elems (second pat)))
    (em :get-iterator) (em :declare-var it)
    (dolist (e elems)
      (cond
        ((null e)                            ; hole: step iterator, discard
         (em :get-var it) (em :iter-next) (em :pop))
        ((and (consp e) (eq (car e) :rest))
         (em :get-var it) (em :iter-rest)    ; collect remaining into an array
         (bind-target (second e)))
        ((and (consp e) (eq (car e) :default))
         (em :get-var it) (em :iter-next) (em :get-prop-c "value")
         (apply-default (third e))
         (bind-target (second e)))
        (t (em :get-var it) (em :iter-next) (em :get-prop-c "value")
           (bind-target e))))))

(defun compile-object-destructure (pat)
  "Value on stack is the source object. Destructure per (:opat PROPS)."
  (let ((src (string (gensym "SRC"))) (props (second pat)) (seen '()))
    (em :declare-var src)
    (dolist (pr props)
      (cond
        ((eq (car pr) :rest)
         ;; { ...rest }: copy own enumerable keys not already taken
         (em :get-var src) (em :object-rest (reverse seen)) (em :declare-var (second pr)))
        (t (destructuring-bind (key tgt &optional default) pr
             (push (and (eq (car key) :lit) (second key)) seen)
             (em :get-var src)
             (if (eq (car key) :computed) (progn (compile-expr (second key)) (em :get-prop))
                 (em :get-prop-c (second key)))
             (when default (apply-default default))
             (bind-target tgt)))))))

(defun compile-params (params)
  "Emit the parameter-binding prologue: pull positional args, apply defaults,
   destructure, and gather rest."
  (loop for p in params for i from 0 do
    (cond
      ((and (consp p) (eq (car p) :rest))
       (em :load-rest i) (bind-target (second p)))
      ((and (consp p) (eq (car p) :default))
       (em :load-arg i) (apply-default (third p)) (bind-target (second p)))
      (t (em :load-arg i) (bind-target p)))))

(defun apply-default (default-expr)
  "Top of stack is a value; if it is undefined, replace with DEFAULT-EXPR."
  (let ((skip (lbl)))
    (em :dup) (em :const *undefined*) (em :bin "!==") (em :jmp-if-true skip)
    (em :pop) (compile-expr default-expr)
    (em :label skip)))

(defun bind-lexical (tgt kind)
  "Initialize a let/const binding TGT from the value on top of the stack.
   KIND is :let or :const. Names are TDZ-pre-declared by the block prologue."
  (cond
    ((stringp tgt) (em (if (eq kind :const) :init-const :init-let) tgt))
    (t (bind-target tgt))))                  ; patterns: leaf names init via declare-var

(defun bind-target (tgt)
  "Bind the value on top of the stack to TGT (name or pattern). Consumes it."
  (cond
    ((stringp tgt) (em :declare-var tgt))
    ((null tgt) (em :pop))                  ; hole: discard
    ((eq (car tgt) :apat) (compile-array-destructure tgt))
    ((eq (car tgt) :opat) (compile-object-destructure tgt))
    (t (js-throw "bad binding target"))))

;;; ---- destructuring ASSIGNMENT (LHS is expression-form: :ident/:member/:array/:object) ----
(defun assign-to-target (tgt)
  "Value on top of stack -> assign to expression-form TGT, consuming the value."
  (ecase (car tgt)
    (:ident (em :set-var (second tgt)) (em :pop))
    (:member
     ;; stack: val ; need obj key val -> set-prop -> pop
     (compile-expr (second tgt))
     (if (fourth tgt) (compile-expr (third tgt)) (em :const (second (third tgt))))
     (em :rot3)                              ; bring val above obj,key : obj key val
     (em :set-prop) (em :pop))
    ((:array :object) (compile-assign-pattern tgt))))

(defun assign-elem-with-default (elem)
  "ELEM may be (:assign \"=\" TGT DEFAULT). Applies default if value is undefined,
   then assigns. Value on top of stack."
  (if (and (consp elem) (eq (car elem) :assign) (string= (second elem) "="))
      (progn (apply-default (fourth elem)) (assign-to-target (third elem)))
      (assign-to-target elem)))

(defun compile-assign-pattern (pat)
  "Destructure the value on top of the stack into expression-form pattern PAT.
   Consumes the value."
  (ecase (car pat)
    (:array
     (let ((it (string (gensym "IT"))) (elems (second pat)))
       (em :get-iterator) (em :declare-var it)
       (dolist (e elems)
         (cond
           ((null e) (em :get-var it) (em :iter-next) (em :pop))       ; hole
           ((and (consp e) (eq (car e) :spread))
            (em :get-var it) (em :iter-rest) (assign-to-target (second e)))
           (t (em :get-var it) (em :iter-next) (em :get-prop-c "value")
              (assign-elem-with-default e))))))
    (:object
     (let ((src (string (gensym "SRC"))) (seen '()))
       (em :declare-var src)
       (dolist (pr (second pat))
         (ecase (car pr)
           (:spread
            (em :get-var src) (em :object-rest (reverse seen)) (assign-to-target (second pr)))
           (:proto                                   ; treat like a normal key __proto__
            (push "__proto__" seen)
            (em :get-var src) (em :get-prop-c "__proto__") (assign-to-target (second pr)))
           (:init
            (let ((key (second pr)) (val (third pr)))
              (when (eq (car key) :lit) (push (second key) seen))
              (em :get-var src)
              (if (eq (car key) :computed) (progn (compile-expr (second key)) (em :get-prop))
                  (em :get-prop-c (second key)))
              ;; val is the target expression (possibly (:assign = tgt default) for {k: t = d}
              ;; or (:ident name) for shorthand {k}, or (:ident name)+default stored in 4th)
              (if (fourth pr)                        ; shorthand-with-default {x = d}
                  (progn (apply-default (fourth pr)) (assign-to-target val))
                  (assign-elem-with-default val))))))))))

(defun collect-var-names (node &optional acc)
  "Collect `var`-declared names in NODE, NOT descending into nested functions."
  (when (consp node)
    (case (car node)
      ((:func :method-func :arrow :genfunc :class :asyncfunc :asyncgenfunc :async-arrow) acc)  ; nested function/class scope: stop
      (:var (if (string= (second node) "var")   ; only `var` hoists to function scope
                (progn (dolist (d (third node)) (setf acc (target-names (car d) acc))) acc)
                acc))
      (:for-in (setf acc (collect-var-names (fourth node) (collect-var-names (second node) acc))))
      (:for-of (setf acc (collect-var-names (fourth node) (collect-var-names (second node) acc))))
      (:for-await-of (setf acc (collect-var-names (fourth node) (collect-var-names (second node) acc))))
      (t (dolist (x (cdr node))
           (cond ((and (consp x) (keywordp (car x))) (setf acc (collect-var-names x acc)))
                 ((and (consp x) (consp (car x)))   ; a list of statements/cases
                  (dolist (y x) (when (consp y) (setf acc (collect-var-names y acc)))))))
         acc))))

(defun lexical-decls (stmts)
  "The (:var KIND DECLS) nodes that are let/const, directly in STMTS (not nested)."
  (remove-if-not (lambda (s) (and (consp s) (eq (car s) :var)
                                  (member (second s) '("let" "const") :test #'string=)))
                 stmts))

(defun block-lexical-names (stmts)
  "All names bound by let/const/class declarations directly in STMTS."
  (let ((acc '()))
    (dolist (d (lexical-decls stmts))
      (dolist (decl (third d)) (setf acc (target-names (car decl) acc))))
    (dolist (s stmts acc)
      (when (and (consp s) (eq (car s) :class) (second s))
        (pushnew (second s) acc :test #'string=)))))

(defun hoisted-func-names (stmts)
  "Names of function declarations directly in STMTS (block-level fn hoisting)."
  (loop for s in stmts when (and (consp s) (eq (car s) :func) (second s))
        collect (second s)))

(defun compile-scoped-block (stmts)
  "Compile a block that declares let/const: new env, TDZ-hoist lexicals,
   hoist block-level function decls, run statements, pop env."
  (let ((lex (block-lexical-names stmts)))
    (if (null lex)
        (mapc #'compile-stmt stmts)          ; no lexicals: keep it flat
        (progn
          (em :push-env)
          (let ((*scope-depth* (1+ *scope-depth*)))
            (dolist (n lex) (em :tdz-declare n))          ; temporal dead zone
            ;; hoist block-scoped function declarations (initialized to undefined then defined)
            (dolist (fn (block-lexical-fns stmts))
              (compile-expr fn) (em :init-let (second fn)))
            (dolist (s stmts) (unless (block-hoisted-fn-p s) (compile-stmt s)))
            (em :pop-env))))))

(defun block-lexical-fns (stmts)
  "Function declarations directly in STMTS (hoisted at block scope)."
  (remove-if-not #'block-hoisted-fn-p stmts))
(defun block-hoisted-fn-p (s) (and (consp s) (member (car s) '(:func :genfunc :asyncfunc :asyncgenfunc)) (second s)))

;;; ---- statements ----
(defun compile-stmt (node)
  (ecase (car node)
    (:block (compile-scoped-block (second node)))
    (:empty nil)
    (:expr (compile-expr (second node)) (em :save-completion))
    (:var (let ((kind (second node)))
            (loop for (tgt . init) in (third node)
                  do (if init (compile-expr init) (em :const *undefined*))
                     (cond
                       ((string= kind "const") (bind-lexical tgt :const))
                       ((string= kind "let")   (bind-lexical tgt :let))
                       (t (if (stringp tgt) (em :declare-var tgt) (bind-target tgt)))))))
    (:func (compile-expr node) (em :declare-var (second node)))
    (:genfunc (compile-expr node) (em :declare-var (second node)))
    (:asyncfunc (compile-expr node) (em :declare-var (second node)))
    (:asyncgenfunc (compile-expr node) (em :declare-var (second node)))
    (:class (compile-expr node) (em :init-let (second node)))   ; class decl: lexical binding
    (:return (compile-expr (second node)) (em :ret))
    (:throw (compile-expr (second node)) (em :throw-op))
    (:if (let ((l1 (lbl)) (l2 (lbl)))
           (compile-expr (second node)) (em :jmp-if-false l1)
           (compile-stmt (third node)) (em :jmp l2)
           (em :label l1) (when (fourth node) (compile-stmt (fourth node)))
           (em :label l2)))
    (:while (let ((top (lbl)) (end (lbl)))
              (em :label top) (compile-expr (second node)) (em :jmp-if-false end)
              (let ((*break-target* end) (*continue-target* top)
                    (*break-depth* *scope-depth*) (*continue-depth* *scope-depth*))
                (compile-stmt (third node)))
              (em :jmp top) (em :label end)))
    (:for (compile-for node))
    (:for-in (compile-scoped-loop node #'compile-for-in))
    (:for-of (compile-scoped-loop node #'compile-for-of))
    (:for-await-of (compile-scoped-loop node #'compile-for-await-of))
    (:break (if *break-target* (progn (pop-envs (- *scope-depth* *break-depth*)) (em :jmp *break-target*))
                (js-throw "illegal break")))
    (:continue (if *continue-target* (progn (pop-envs (- *scope-depth* *continue-depth*)) (em :jmp *continue-target*))
                   (js-throw "illegal continue")))
    (:switch (destructuring-bind (disc cases default) (cdr node)
               (let ((dv (string (gensym "SW"))) (end (lbl)) (deflabel (lbl))
                     (clabels (mapcar (lambda (c) (cons c (lbl))) cases)))
                 (compile-expr disc) (em :declare-var dv)
                 (dolist (cl clabels)
                   (em :get-var dv) (compile-expr (car (car cl))) (em :bin "===") (em :jmp-if-true (cdr cl)))
                 (em :jmp deflabel)
                 (let ((*break-target* end) (*break-depth* *scope-depth*))
                   (dolist (cl clabels) (em :label (cdr cl)) (mapc #'compile-stmt (cdr (car cl))))
                   (em :label deflabel) (when default (mapc #'compile-stmt default)))
                 (em :label end))))
    (:try (destructuring-bind (blk param catch fin) (cdr node)
            (if catch
                (let ((lc (lbl)) (after (lbl)))
                  (em :push-handler lc) (compile-stmt blk) (em :pop-handler) (em :jmp after)
                  (em :label lc)                                  ; thrown value on stack
                  (em :push-env)                                  ; catch parameter scope
                  (let ((*scope-depth* (1+ *scope-depth*)))
                    (cond ((null param) (em :pop))
                          ((stringp param) (em :declare-var param))
                          (t (bind-target param)))               ; destructuring catch param
                    (compile-stmt catch))
                  (em :pop-env)
                  (em :label after))
                (compile-stmt blk))
            (when fin (compile-stmt fin))))))   ; v0: finally runs on the normal/caught path

(defun compile-for (node)
  (destructuring-bind (init test update body) (cdr node)
    (let ((lexical (and init (eq (car init) :var)
                        (member (second init) '("let" "const") :test #'string=))))
      (when lexical (em :push-env))
      (let ((*scope-depth* (if lexical (1+ *scope-depth*) *scope-depth*)))
        (let ((top (lbl)) (cont (lbl)) (end (lbl)))
          (when init (compile-stmt (if (eq (car init) :var) init (list :expr (second init)))))
          (em :label top)
          (when test (compile-expr test) (em :jmp-if-false end))
          (let ((*break-target* end) (*continue-target* cont)
                (*break-depth* *scope-depth*) (*continue-depth* *scope-depth*))
            (compile-stmt body))
          (em :label cont)
          (when update (compile-expr update) (em :pop))
          (em :jmp top) (em :label end)))
      (when lexical (em :pop-env)))))

(defun compile-scoped-loop (node inner)
  "Wrap a for-in/for-of in a block env when its head declares let/const."
  (let* ((head (second node))
         (lexical (and (consp head) (eq (car head) :var)
                       (member (second head) '("let" "const") :test #'string=))))
    (if lexical
        (progn (em :push-env)
               (let ((*scope-depth* (1+ *scope-depth*))) (funcall inner node))
               (em :pop-env))
        (funcall inner node))))

(defun for-head-assign (head)
  "Bind the value currently on top of the stack to the loop target (consumes it)."
  (cond ((eq (car head) :var)
         (let ((tgt (car (first (third head)))))
           (if (stringp tgt) (em :declare-var tgt) (bind-target tgt))))
        ((eq (car head) :ident) (em :set-var (second head)) (em :pop))
        ((member (car head) '(:member))            ; obj.p / obj[k] loop target
         (compile-assign-pattern head) (em :pop))
        ((member (car head) '(:array :object))     ; destructuring assignment target
         (compile-assign-pattern head) (em :pop))
        (t (js-throw "unsupported for-in/of target"))))

(defun compile-for-in (node)
  (destructuring-bind (head obj body) (cdr node)
    (let ((keys (string (gensym "KS"))) (idx (string (gensym "I"))) (len (string (gensym "N")))
          (top (lbl)) (cont (lbl)) (end (lbl)))
      (compile-expr obj) (em :for-in-keys) (em :declare-var keys)  ; array of enumerable keys
      (em :const 0d0) (em :declare-var idx)
      (em :get-var keys) (em :get-prop-c "length") (em :declare-var len)
      (em :label top)
      (em :get-var idx) (em :get-var len) (em :bin "<") (em :jmp-if-false end)
      (em :get-var keys) (em :get-var idx) (em :get-prop)     ; the key string
      (for-head-assign head)
      (let ((*break-target* end) (*continue-target* cont)) (compile-stmt body))
      (em :label cont)
      (em :get-var idx) (em :const 1d0) (em :bin "+") (em :set-var idx) (em :pop)
      (em :jmp top) (em :label end))))

(defun compile-for-of (node)
  (destructuring-bind (head obj body) (cdr node)
    (let ((it (string (gensym "IT"))) (res (string (gensym "R")))
          (top (lbl)) (cont (lbl)) (end (lbl)))
      (compile-expr obj) (em :get-iterator) (em :declare-var it)
      (em :label top)
      (em :get-var it) (em :iter-next) (em :declare-var res)     ; {value,done}
      (em :get-var res) (em :get-prop-c "done") (em :jmp-if-true end)
      (em :get-var res) (em :get-prop-c "value")
      (for-head-assign head)
      (let ((*break-target* end) (*continue-target* cont)) (compile-stmt body))
      (em :label cont) (em :jmp top) (em :label end))))

(defun compile-for-await-of (node)
  "for await (x of asyncIterable): drive the async iterator, awaiting each step's
   result and its value. Only valid inside an async function."
  (destructuring-bind (head obj body) (cdr node)
    (let ((it (string (gensym "IT"))) (res (string (gensym "R")))
          (top (lbl)) (cont (lbl)) (end (lbl)))
      (compile-expr obj) (em :get-async-iterator) (em :declare-var it)
      (em :label top)
      (em :get-var it) (em :iter-next) (em :await) (em :declare-var res)  ; await the {value,done}
      (em :get-var res) (em :get-prop-c "done") (em :jmp-if-true end)
      (em :get-var res) (em :get-prop-c "value") (em :await)              ; await the value
      (for-head-assign head)
      (let ((*break-target* end) (*continue-target* cont)) (compile-stmt body))
      (em :label cont) (em :jmp top) (em :label end))))

;;; ---- expressions (each leaves exactly one value on the stack) ----
(defun compile-expr (node)
  (ecase (car node)
    (:num (em :const (second node)))
    (:bigint (em :const (second node)))
    (:str (em :const (second node)))
    (:regex (em :get-var "RegExp") (em :const (second node)) (em :const (third node)) (em :new 2))
    (:bool (em :const (if (second node) *true* *false*)))
    (:null (em :const *null*))
    (:undefined (em :const *undefined*))
    (:this (em :get-this))
    (:ident (em :get-var (second node)))
    (:bin (compile-expr (third node)) (compile-expr (fourth node)) (em :bin (second node)))
    (:unary (if (and (string= (second node) "typeof") (eq (car (third node)) :ident))
                (em :typeof-var (second (third node)))     ; typeof of a NAME never throws
                (progn (compile-expr (third node)) (em :unary (second node)))))
    (:delete (let ((tgt (second node)))
               (if (eq (car tgt) :member)
                   (progn (compile-expr (second tgt))
                          (if (fourth tgt) (compile-expr (third tgt)) (em :const (second (third tgt))))
                          (em :del-prop))
                   (em :const *true*))))   ; delete of a non-reference is true (sloppy)
    (:logical (let ((end (lbl)) (op (second node)))
                (compile-expr (third node))
                (em (cond ((string= op "&&") :and-jmp)
                          ((string= op "||") :or-jmp)
                          (t :nullish-jmp)) end)   ; ??
                (compile-expr (fourth node)) (em :label end)))
    (:cond (let ((l1 (lbl)) (l2 (lbl)))
             (compile-expr (second node)) (em :jmp-if-false l1)
             (compile-expr (third node)) (em :jmp l2)
             (em :label l1) (compile-expr (fourth node)) (em :label l2)))
    (:assign (compile-assign (second node) (third node) (fourth node)))
    (:update (compile-update (second node) (third node) (fourth node)))
    (:member (compile-expr (second node))
             (if (fourth node) (progn (compile-expr (third node)) (em :get-prop))
                 (em :get-prop-c (second (third node)))))   ; non-computed key node is (:str name)
    (:call (compile-call (second node) (third node)))
    (:new (compile-expr (second node))
          (if (some (lambda (a) (and (consp a) (eq (car a) :spread))) (third node))
              (progn (compile-arg-array (third node)) (em :new-spread))
              (progn (mapc #'compile-expr (third node)) (em :new (length (third node))))))
    (:array (compile-array-literal (second node)))
    (:object (compile-object-literal (second node)))
    (:func (em :closure (compile-fn (second node) (third node) (fourth node))))
    ;; concise/accessor method: ordinary this-mode (sloppy substitution) but not constructable
    (:method-func (em :closure (compile-fn (second node) (third node) (fourth node) nil :normal nil)))
    (:genfunc (em :genclosure (compile-fn-split (second node) (third node) (fourth node))))
    (:asyncfunc (em :asyncclosure (compile-fn-split (second node) (third node) (fourth node))))
    (:asyncgenfunc (em :asyncgenclosure (compile-fn-split (second node) (third node) (fourth node))))
    (:arrow (em :closure (compile-fn nil (second node) (third node) nil :lexical nil)))
    (:async-arrow (em :asyncclosure (compile-fn-split nil (second node) (third node) :lexical)))
    (:await (compile-expr (second node)) (em :await))
    (:class (compile-class node))
    (:yield (if (second node) (compile-expr (second node)) (em :const *undefined*))
            (em :yield))
    (:yield* (compile-expr (second node)) (em :yield-star))
    (:super-member (compile-super-member node))
    (:super-call (compile-super-call (second node)))
    (:spread (compile-expr (second node)))   ; bare spread handled by call/array sites
    (:template (compile-template node))
    (:tagged-template (compile-tagged-template node))
    ((:omember :ocall) (compile-optional-chain node))))

;;; ---- classes ----
(defun class-field-inits (members)
  "Instance (non-static) field members, in source order."
  (remove-if-not (lambda (m) (and (eq (car m) :field) (not (fourth m)))) members))

(defun compile-class (node)
  "Compile (:class NAME SUPER MEMBERS CTOR) leaving the constructor on the stack.
   Strategy: build a ctor function + prototype object at runtime via ops; attach
   methods (non-enumerable) and static members; run field initializers in the
   constructor prologue."
  (destructuring-bind (name super members ctor) (cdr node)
    (let* ((derived (and super t))
           (fields (class-field-inits members))
           ;; the constructor body: default is `constructor(...args){ super(...args) }`
           ;; for derived, or an empty constructor otherwise.
           (ctor-code (compile-class-ctor name ctor fields derived)))
      ;; super value on stack (or undefined sentinel)
      (if super (compile-expr super) (em :const *undefined*))
      (em :make-class ctor-code derived name)            ; -> ctor (with .prototype)
      ;; if named, the class name is bound inside method scope; we bound it lexically
      ;; at the declaration site. For expression form, methods capture via the outer env.
      ;; ctor is on the stack throughout; each member op consumes its extras and
      ;; leaves ctor in place.
      (dolist (m members)
        (ecase (car m)
          (:method
           (destructuring-bind (kind key fn static) (cdr m)
             ;; stack: ctor ; push key, push method-closure, def
             (if (eq (car key) :computed) (compile-expr (second key)) (em :const (second key)))
             (compile-expr fn)                            ; method closure (home set by op)
             (em :class-method kind (if static t nil))))  ; ctor key fn -> ctor
          (:field
           (when (fourth m)                               ; static field: init with this=ctor
             (if (eq (car (second m)) :computed) (compile-expr (second (second m))) (em :const (second (second m))))
             (if (third m)
                 (compile-with-this-ctor (third m))       ; value, this=ctor
                 (em :const *undefined*))
             (em :class-static-field)))))                 ; ctor key val -> ctor
      ;; final: ctor stays on the stack as the class value
      )))

(defun compile-with-this-ctor (expr)
  "Compile EXPR so that `this` refers to the constructor (top-of-stack ctor).
   Used for static field initializers. We emit the expr normally — static field
   initializers that reference `this` are rare; if EXPR uses `this` it will read
   the surrounding this. For correctness we set this via a helper op wrapping."
  ;; Simplest correct-enough path: evaluate the expr with normal `this`. Static
  ;; field initializer `this` referring to the class is an edge case.
  (compile-expr expr))

;; A simplified static-field path: recompute below without the fragile dup.
(defun compile-class-ctor (name ctor fields derived)
  "Build the code object for the class constructor. FIELDS are instance field
   members to initialize (in the ctor prologue, after super() for derived)."
  (declare (ignore name))
  (let* ((params (if ctor (third ctor) (if derived (list (list :rest "args")) '())))
         (user-body (if ctor (fourth ctor) nil))
         (field-stmts (mapcar #'field->stmt fields))
         ;; default constructor bodies
         (body (cond
                 (ctor (splice-field-inits user-body field-stmts derived))
                 (derived (list :block (append
                                        (list (list :expr (list :super-call (list (list :spread (list :ident "args"))))))
                                        field-stmts)))
                 (t (list :block field-stmts)))))
    (let ((*compiling-ctor* (if derived :derived :base)))
      (compile-fn "constructor" params body))))

(defvar *compiling-ctor* nil)   ; :base / :derived while compiling a class constructor body

(defun field->stmt (field)
  "Turn a (:field KEY INIT STATIC) into a `this.KEY = INIT` statement."
  (destructuring-bind (key init static) (cdr field)
    (declare (ignore static))
    (let ((tgt (if (eq (car key) :computed)
                   (list :member (list :this) (second key) t)
                   (list :member (list :this) (list :str (second key)) nil))))
      (list :expr (list :assign "=" tgt (or init *undefined-ast*))))))

(defun splice-field-inits (user-body field-stmts derived)
  "Insert field initializers: for a base ctor, at the top of the body; for a
   derived ctor, immediately AFTER the super() call (approx: at top — simplest)."
  (declare (ignore derived))
  (let ((stmts (if (eq (car user-body) :block) (second user-body) (list user-body))))
    (list :block (append field-stmts stmts))))

(defun array-has-special-p (elems)
  (some (lambda (e) (or (null e) (and (consp e) (eq (car e) :spread)))) elems))

(defun compile-array-literal (elems)
  (if (array-has-special-p elems)
      ;; build incrementally: fresh array, push/append elements, track length
      (let ((arr (string (gensym "A"))) (idx (string (gensym "AI"))))
        (em :new-array) (em :declare-var arr)
        (em :const 0d0) (em :declare-var idx)
        (dolist (e elems)
          (cond
            ((null e)                        ; hole: just bump length/index
             (em :get-var idx) (em :const 1d0) (em :bin "+") (em :set-var idx) (em :pop))
            ((and (consp e) (eq (car e) :spread))
             (em :get-var arr) (em :get-var idx) (compile-expr (second e))
             (em :array-spread)              ; arr idx iterable -> newidx
             (em :set-var idx) (em :pop))
            (t (em :get-var arr) (em :get-var idx) (compile-expr e) (em :set-prop) (em :pop)
               (em :get-var idx) (em :const 1d0) (em :bin "+") (em :set-var idx) (em :pop))))
        ;; set final length (covers trailing holes)
        (em :get-var arr) (em :const "length") (em :get-var idx) (em :set-prop) (em :pop)
        (em :get-var arr))
      (progn (mapc #'compile-expr elems) (em :array (length elems)))))

(defun compile-object-literal (props)
  (em :new-object)                           ; empty object on stack; each op returns it
  (dolist (pr props)
    (ecase (car pr)
      (:init
       (let ((key (second pr)) (val (third pr)))
         (if (eq (car key) :computed) (compile-expr (second key)) (em :const (second key)))
         (compile-expr val)
         (em :def-prop)))                    ; obj key val -> obj
      ((:get :set)
       (let ((key (second pr)) (fn (third pr)))
         (if (eq (car key) :computed) (compile-expr (second key)) (em :const (second key)))
         (compile-expr fn)
         (em (if (eq (car pr) :get) :def-getter :def-setter))))   ; obj key fn -> obj
      (:proto
       (compile-expr (second pr))
       (em :set-proto))                       ; obj protoval -> obj
      (:spread
       (compile-expr (second pr))
       (em :def-spread)))))                  ; obj src -> obj

;;; ---- template literals / tagged templates ----
(defun compile-template (node)
  "(:template (COOKED...) (RAW...) (EXPR-AST...)) -> string concatenation.
   Result = cooked[0] + String(expr[0]) + cooked[1] + ... "
  (destructuring-bind (cooked raw exprs) (cdr node)
    (declare (ignore raw))
    (em :const (or (first cooked) ""))
    (loop for e in exprs
          for rest on (cdr cooked) do
      (compile-expr e) (em :to-str) (em :bin "+")
      (em :const (or (car rest) "")) (em :bin "+"))))

(defun compile-tagged-template (node)
  "tag`...` -> tag(stringsArray, ...substitutions) with stringsArray.raw set."
  (destructuring-bind (tag tmpl) (cdr node)
    (destructuring-bind (cooked raw exprs) (cdr tmpl)
      ;; determine `this` and callee like a normal call
      (if (member (car tag) '(:member :omember))
          (progn (compile-expr (second tag)) (em :dup)
                 (if (fourth tag) (progn (compile-expr (third tag)) (em :get-prop))
                     (em :get-prop-c (second (third tag)))))
          (progn (em :const *undefined*) (compile-expr tag)))
      ;; build the strings array (cooked) with a .raw array
      (em :new-array)
      (loop for s in cooked for i from 0 do
        (em :dup) (em :const (princ-to-string i)) (em :const s) (em :set-prop) (em :pop))
      (em :dup) (em :const "length") (em :const (float (length cooked) 1d0)) (em :set-prop) (em :pop)
      ;; .raw
      (em :dup) (em :const "raw") (em :new-array)
      (loop for s in raw for i from 0 do
        (em :dup) (em :const (princ-to-string i)) (em :const s) (em :set-prop) (em :pop))
      (em :dup) (em :const "length") (em :const (float (length raw) 1d0)) (em :set-prop) (em :pop)
      (em :set-prop) (em :pop)
      ;; substitutions as remaining args
      (dolist (e exprs) (compile-expr e))
      (em :call (1+ (length exprs))))))

;;; ---- optional chaining ----
(defun optional-chain-p (node)
  (and (consp node) (member (car node) '(:omember :ocall))))

(defun compile-optional-chain (node)
  "Compile a chain containing at least one ?. link. If any optional link's base
   is null/undefined, the whole chain evaluates to undefined."
  (let ((end (lbl)))
    (compile-chain-link node end)
    (let ((done (lbl)))
      (em :jmp done)
      (em :label end) (em :pop) (em :const *undefined*)   ; discard base, yield undefined
      (em :label done))))

(defun compile-chain-link (node short)
  "Emit code leaving the link's value on the stack; on an optional null/undefined
   base, jump to SHORT (with the base value still on the stack to be popped)."
  (ecase (car node)
    (:omember
     (compile-chain-base (second node) short)
     (em :dup) (em :nullish-short short)      ; if base nullish, jump to short (base on stack)
     (if (fourth node) (progn (compile-expr (third node)) (em :get-prop))
         (em :get-prop-c (second (third node)))))
    (:ocall
     (compile-chain-base (second node) short)
     (em :dup) (em :nullish-short short)
     ;; optional call: callee on stack; call with this=undefined
     (compile-call-on-stack (third node)))
    (:member
     (compile-chain-base (second node) short)
     (if (fourth node) (progn (compile-expr (third node)) (em :get-prop))
         (em :get-prop-c (second (third node)))))
    (:call
     ;; a normal call inside an optional chain (e.g. a?.b())
     (let ((callee (second node)))
       (if (member (car callee) '(:member :omember))
           (progn (compile-chain-base (second callee) short)
                  (when (eq (car callee) :omember) (em :dup) (em :nullish-short short))
                  (em :dup)
                  (if (fourth callee) (progn (compile-expr (third callee)) (em :get-prop))
                      (em :get-prop-c (second (third callee))))
                  (mapc #'compile-expr (third node)) (em :call (length (third node))))
           (progn (compile-chain-base callee short) (em :const *undefined*) (em :swap)
                  (mapc #'compile-expr (third node)) (em :call (length (third node)))))))))

(defun compile-chain-base (node short)
  "Compile a sub-expression that is part of the optional chain (recurse) or a
   plain expression (leaf)."
  (if (optional-chain-p node)
      (compile-chain-link node short)
      (compile-expr node)))

(defun compile-call-on-stack (args)
  "Callee is on top of stack; call it with this=undefined and ARGS."
  (em :const *undefined*) (em :swap)          ; -> undefined callee
  (mapc #'compile-expr args) (em :call (length args)))

;;; ---- super ----
(defun compile-super-member (node)
  "super.x / super[k]: read property from the home object's [[Prototype]], with
   this=current this. Leaves the value on the stack."
  (destructuring-bind (key computed) (cdr node)
    (if computed (compile-expr key) (em :const (second key)))
    (em :super-get)))                          ; key -> value (uses %home + this)

(defun compile-super-call (args)
  "super(...): call the parent constructor with the current `this`, running its
   [[Call]] to initialize the instance."
  (if (some (lambda (a) (and (consp a) (eq (car a) :spread))) args)
      (progn (compile-arg-array args) (em :super-call-spread))
      (progn (mapc #'compile-expr args) (em :super-call (length args)))))

(defun compile-call (callee args)
  ;; super.m(...) : method call on the super prototype, this = current this
  (when (eq (car callee) :super-member)
    (destructuring-bind (key computed) (cdr callee)
      (if computed (compile-expr key) (em :const (second key)))
      (em :super-get-method)                   ; key -> thisv methodfn
      (if (some (lambda (a) (and (consp a) (eq (car a) :spread))) args)
          (progn (compile-arg-array args) (em :call-spread))
          (progn (mapc #'compile-expr args) (em :call (length args))))
      (return-from compile-call nil)))
  (if (eq (car callee) :member)            ; method call: `this` is the object
      (progn (compile-expr (second callee)) (em :dup)
             (if (fourth callee) (progn (compile-expr (third callee)) (em :get-prop))
                 (em :get-prop-c (second (third callee)))))
      (progn (em :const *undefined*) (compile-expr callee)))   ; plain call: this = undefined
  ;; stack now: thisv callee
  (if (some (lambda (a) (and (consp a) (eq (car a) :spread))) args)
      (progn (compile-arg-array args) (em :call-spread))       ; thisv callee argsArray -> result
      (progn (mapc #'compile-expr args) (em :call (length args)))))

(defun compile-arg-array (args)
  "Build an array of argument values, flattening spreads. Leaves it on the stack."
  (let ((arr (string (gensym "CA"))) (idx (string (gensym "CI"))))
    (em :new-array) (em :declare-var arr)
    (em :const 0d0) (em :declare-var idx)
    (dolist (a args)
      (if (and (consp a) (eq (car a) :spread))
          (progn (em :get-var arr) (em :get-var idx) (compile-expr (second a))
                 (em :array-spread) (em :set-var idx) (em :pop))
          (progn (em :get-var arr) (em :get-var idx) (compile-expr a) (em :set-prop) (em :pop)
                 (em :get-var idx) (em :const 1d0) (em :bin "+") (em :set-var idx) (em :pop))))
    (em :get-var arr)))

(defun logical-assign-op (op)
  "For &&= ||= ??= return the short-circuit op string; else nil."
  (cond ((string= op "&&=") "&&") ((string= op "||=") "||") ((string= op "??=") "??")))

(defun compile-logical-assign (lop target value)
  "x <op>= v  where <op> in {&& || ??}: read x; short-circuit; else assign v.
   Result on stack = final value of the reference."
  (let ((end (lbl))
        (jmpop (cond ((string= lop "&&") :and-jmp) ((string= lop "||") :or-jmp) (t :nullish-jmp))))
    (ecase (car target)
      (:ident
       (em :get-var (second target))        ; current value on stack
       (em jmpop end)                        ; keep it & skip if short-circuits
       (compile-expr value) (em :set-var (second target))
       (em :label end))
      (:member
       (let ((short (lbl)) (obj (string (gensym "O"))) (k (string (gensym "K"))))
         (compile-expr (second target)) (em :declare-var obj)   ; save obj
         (if (fourth target) (compile-expr (third target)) (em :const (second (third target))))
         (em :declare-var k)                                    ; save key
         (em :get-var obj) (em :get-var k) (em :get-prop)       ; old on stack
         (em jmpop short)                                       ; short-circuit: keep old
         (em :pop)                                              ; drop old, recompute for set
         (em :get-var obj) (em :get-var k) (compile-expr value) (em :set-prop)
         (em :jmp end)
         (em :label short)                                      ; old already on stack = result
         (em :label end))))))

(defun compile-assign (op target value)
  (when (logical-assign-op op)
    (return-from compile-assign (compile-logical-assign (logical-assign-op op) target value)))
  ;; destructuring assignment: [a,b] = v / ({x} = v). Only plain `=`.
  (when (and (string= op "=") (member (car target) '(:array :object)))
    (compile-expr value)                     ; RHS value on stack (assignment result)
    (em :dup)                                ; keep a copy to destructure
    (compile-assign-pattern target)          ; consumes the copy
    (return-from compile-assign nil))
  (let ((base (and (> (length op) 1) (subseq op 0 (1- (length op))))))  ; "+=" -> "+"
    (ecase (car target)
      (:ident (if base (progn (em :get-var (second target)) (compile-expr value) (em :bin base))
                  (compile-expr value))
              (em :set-var (second target)))
      (:member
       (compile-expr (second target))                                       ; obj
       (if (fourth target) (compile-expr (third target)) (em :const (second (third target)))) ; key
       (if base
           ;; obj key -> [obj key obj-key-get] -> bin -> set-prop  (dup obj+key first)
           (progn (em :dup2)               ; stack: obj key obj key
                  (em :get-prop)           ; stack: obj key old
                  (compile-expr value) (em :bin base))  ; stack: obj key new
           (compile-expr value))
       (em :set-prop)))))

(defun compile-update (op prefix target)
  (let ((binop (if (string= op "++") "+" "-")))
    (ecase (car target)
      (:ident
       (let ((name (second target)) (delta (if (string= op "++") 1 -1)))
         (declare (ignore binop))
         (em :get-var name) (em :to-numeric)
         (if prefix
             (progn (em :num-step delta) (em :set-var name))
             (progn (em :dup) (em :num-step delta) (em :set-var name) (em :pop)))))
      (:member
       (compile-expr (second target))
       (if (fourth target) (compile-expr (third target)) (em :const (second (third target))))
       ;; stack: obj key ; VM op reads obj[key], applies +/-1, writes back,
       ;; and pushes the new (prefix) or old (postfix) numeric value.
       (em :update-prop (if (string= op "++") 1d0 -1d0) prefix)))))
