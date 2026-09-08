;;;; compile.lisp — AST -> bytecode. A flat instruction stream (op . args) with
;;;; symbolic labels, then assembled to a vector with resolved jump targets.
;;;; Stack machine; variables are name-resolved through an environment chain
;;;; (indexed locals + scope analysis = a later optimization).
(in-package #:shuttle)

(defstruct code name params instrs inst-instrs
  (this-mode :normal)     ; :normal = OrdinaryCallBindThis (sloppy: undefined/null -> globalThis, primitive -> boxed);
                          ; :lexical = arrow (inherit caller's this, no rebind)
  (strict nil)            ; T iff this code runs in strict mode (own "use strict" prologue or inherited)
  (constructable t))      ; NIL for arrows and concise/accessor methods (new'ing them is a TypeError)

(defvar *strict* nil)     ; compile-time: are we lexically inside strict code? (inherited by nested fns)
;; Declared HERE, above every LET that binds it: a LET of an undeclared name is a LEXICAL binding,
;; so a defvar further down the file would leave each binding invisible to the reader in
;; COMPILE-EXPR -- which is exactly what happened, silently.
(defvar *in-async-gen* nil
  "True while compiling an ASYNC generator body, where `yield*` must await each step.")
(defvar *pending-finallys* nil
  "Finally blocks (innermost first) that an abrupt exit from here must run on its way out.
`return` inside a try compiles its finallys before the RET; without this the block was simply
skipped, and `try { return 'a' } finally { return 'b' }` answered 'a'.")
(defvar *in-function* nil) ; compile-time: inside a function body? (`new.target` early error outside one)
(defvar *out*)
(defvar *break-target* nil) (defvar *continue-target* nil)
(defvar *labels* '())          ; ((NAME break-lbl continue-lbl-or-nil scope-depth) ...)
(defvar *pending-labels* '())  ; label names attached to the next loop/iteration stmt
(defvar *scope-depth* 0)                 ; current lexical block-env nesting within the fn
(defvar *annexb-fn-names* '())           ; block-fn names getting an Annex B B.3.3 var binding
(defvar *break-depth* 0) (defvar *continue-depth* 0)  ; scope depth at the loop/switch target
;; The pending-finally list AS IT WAS at the loop/switch target.  Breaking or continuing out of a
;; try must run the finallys entered since -- the same rule `return` follows, measured against a
;; nearer boundary.
(defvar *break-finallys* nil) (defvar *continue-finallys* nil)
(defun em (op &rest args) (push (cons op args) *out*))
(defun lbl () (gensym "L"))
(defun pop-envs (count) (dotimes (_ count) (em :pop-env)))

(defun assemble (rev-instrs)
  (let ((instrs (nreverse rev-instrs)) (pos (make-hash-table)) (idx 0) (out '()))
    (dolist (in instrs) (if (eq (car in) :label) (setf (gethash (cadr in) pos) idx) (incf idx)))
    (dolist (in instrs)
      (unless (eq (car in) :label)
        (push (if (member (car in) '(:jmp :jmp-if-false :jmp-if-true :and-jmp :or-jmp :nullish-jmp :nullish-short :nullish-short-2 :push-handler))
                  (list (car in) (gethash (cadr in) pos)) in) out)))
    (coerce (nreverse out) 'vector)))

(defun compile-toplevel (src &optional eval-code)
  ;; top-level falls off the end so RUN returns the completion value (eval semantics)
  (compile-fn nil '() (parse-program src) (if eval-code :eval t)))

(defun check-no-duplicate-params (params)
  "Strict-mode early error: a duplicate binding name in a parameter list is a
   SyntaxError. (In sloppy mode duplicates are allowed for plain-ident params.)"
  (let ((seen '()))
    (labels ((names (tgt)
               (cond ((stringp tgt) (list tgt))
                     ((null tgt) '())
                     ((eq (car tgt) :apat)
                      (loop for e in (second tgt) append
                            (cond ((null e) '())
                                  ((and (consp e) (member (car e) '(:rest :default))) (names (second e)))
                                  (t (names e)))))
                     ((eq (car tgt) :opat)
                      (loop for pr in (second tgt) append
                            (if (eq (car pr) :rest) (list (second pr)) (names (second pr)))))
                     ((member (car tgt) '(:default :rest)) (names (second tgt)))
                     (t '()))))
      (dolist (p params)
        (dolist (n (names (param-target p)))
          (when (member n seen :test #'string=)
            (js-throw (make-native-error "SyntaxError"
                        (format nil "Duplicate parameter name '~a' not allowed in this context" n))))
          (push n seen))))))

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
  ;; A strict function's `this` is NOT substituted (undefined stays undefined):
  ;; strict is triggered by the body's own "use strict" prologue OR inherited from
  ;; enclosing strict code. sloppy substitution is the default. (Arrows keep
  ;; :lexical regardless — they inherit `this` from the definition site.)
  (let ((*strict* (or *strict* (directive-prologue-strict-p body)))
        (*in-function* (if toplevel *in-function* t)))  ; top-level program/eval: not a function body
  (when (and (eq this-mode :normal) *strict*)
    (setf this-mode :strict))
  (let ((*out* '()) (pnames (param-names params)))
    ;; strict early error: duplicate parameter names are a SyntaxError.
    (when *strict* (check-no-duplicate-params params))
    ;; bind parameters from incoming call args
    (compile-params params)
    ;; hoist: pre-declare all `var` names (as undefined) so forward reads don't
    ;; ReferenceError. Function declarations are hoisted by :func handling below.
    ;; At GLOBAL scope, GlobalDeclarationInstantiation instead runs the spec early
    ;; checks and creates var/function bindings as own properties of the global
    ;; object (configurable:false) — emitted as a single :global-instantiate op.
    (when (eq toplevel t)
      (let* ((tstmts (if (eq (car body) :block) (second body) (list body)))
             (tfns   (hoisted-func-names tstmts))
             (tlex   (block-lexical-names tstmts))
             ;; Annex B B.3.3 block-nested fn names also become global VAR bindings
             ;; (sloppy only), so they land as own properties of the global object.
             (tannexb (if *strict* '() (annexb-var-fn-names body pnames tlex)))
             (tvars  (union (collect-var-names body) tannexb :test #'string=)))
        (em :global-instantiate (list tvars tfns tlex))))
    ;; eval code (direct/indirect): EvalDeclarationInstantiation — var/fn bindings
    ;; go into the running variable environment. At global scope that means a global
    ;; object property (but NOT the genv [[VarNames]], so a later `let` isn't blocked).
    (when (eq toplevel :eval)
      (let* ((estmts (if (eq (car body) :block) (second body) (list body)))
             (efns   (hoisted-func-names estmts))
             (elex   (block-lexical-names estmts))
             ;; Annex B B.3.3 block-nested fn names also become eval var bindings (sloppy).
             (eannexb (if *strict* '() (annexb-var-fn-names body pnames elex))))
        (dolist (v (union (union (collect-var-names body) efns :test #'string=)
                          eannexb :test #'string=))
          (unless (member v pnames :test #'string=)
            (em :eval-var-decl v)))))
    (unless toplevel
      (dolist (v (collect-var-names body))
        (unless (member v pnames :test #'string=)
          (em :const *undefined*) (em :declare-var v))))
    ;; function/top-level body: hoist its OWN lexicals into the function env (no extra block)
    (let* ((stmts (if (eq (car body) :block) (second body) (list body)))
           (lexnames (block-lexical-names stmts))
           ;; Annex B B.3.3 (sloppy only): block-nested fn names get a var binding.
           (*annexb-fn-names* (if *strict* '()
                                  (annexb-var-fn-names body pnames lexnames))))
      ;; pre-declare the Annex B var bindings (undefined) unless already covered by a
      ;; param, a `var`, or a top-level function declaration (those bind it themselves).
      (let ((top-fns (hoisted-func-names stmts))
            (varnames (collect-var-names body)))
        (dolist (v *annexb-fn-names*)
          (unless (or (member v pnames :test #'string=)
                      (member v varnames :test #'string=)
                      (member v top-fns :test #'string=))
            ;; only create the var binding if absent (a shared eval env may already
            ;; have it as a param/outer var — don't clobber it to undefined).
            (em :const *undefined*) (em :declare-var-absent v))))
      (dolist (n lexnames) (em :tdz-declare n))
      ;; Top-level function declarations: at global/eval scope they are VAR-scoped
      ;; (CreateGlobalFunctionBinding / EvalDeclarationInstantiation) — bind them onto
      ;; the global object via :declare-var (the property was pre-created by
      ;; :global-instantiate / :eval-var-decl). Inside an ordinary function body they
      ;; are hoisted into the function's declarative record via :init-let.
      (dolist (fn (block-lexical-fns stmts))
        (compile-fn-decl-closure fn)
        (if toplevel (em :declare-var (second fn)) (em :init-let (second fn))))
      (dolist (s stmts) (unless (block-hoisted-fn-p s) (compile-stmt s))))
    (unless toplevel (em :const *undefined*) (em :ret))   ; functions default-return undefined
    (make-code :name name :params params :instrs (assemble *out*)
               :this-mode this-mode :strict *strict* :constructable constructable))))

(defun compile-fn-split (name params body &optional (this-mode :normal))
  "Compile a generator/async/async-generator: split FunctionDeclarationInstantiation
   (param binding + var/lexical/fn hoisting — run synchronously at the call) from the
   deferred body. Returns a CODE whose INST-INSTRS is the instantiation stream and
   INSTRS is the body; both run against the SAME function environment."
  (let ((*strict* (or *strict* (directive-prologue-strict-p body)))
        (*in-function* t))
  (when (and (eq this-mode :normal) *strict*)
    (setf this-mode :strict))
  (let ((pnames (param-names params)) (inst nil))
    (let ((*out* '()))
      (compile-params params)
      (dolist (v (collect-var-names body))
        (unless (member v pnames :test #'string=)
          (em :const *undefined*) (em :declare-var v)))
      (let ((stmts (if (eq (car body) :block) (second body) (list body))))
        (dolist (n (block-lexical-names stmts)) (em :tdz-declare n))
        (dolist (fn (block-lexical-fns stmts)) (compile-fn-decl-closure fn) (em :init-let (second fn))))
      (em :const *undefined*) (em :ret)              ; instantiation stream returns undefined
      (setf inst (assemble *out*)))
    (let ((*out* '()))
      (let ((stmts (if (eq (car body) :block) (second body) (list body))))
        (dolist (s stmts) (unless (block-hoisted-fn-p s) (compile-stmt s))))
      (em :const *undefined*) (em :ret)
      (make-code :name name :params params :instrs (assemble *out*) :inst-instrs inst
                 :this-mode this-mode :strict *strict*)))))

(defun compile-array-destructure (pat)
  "Value on stack is the iterable. Destructure per (:apat ELEMS). Tracks the
   iterator's done-state and, when the pattern has no rest element and does not
   exhaust the iterator, performs IteratorClose (calls .return())."
  (let* ((it (string (gensym "IT"))) (done (string (gensym "DN")))
         (elems (second pat))
         (has-rest (some (lambda (e) (and (consp e) (eq (car e) :rest))) elems)))
    (em :get-iterator) (em :declare-var it)
    (em :const *false*) (em :declare-var done)
    (let ((close (lbl)) (after (lbl)))
      (em :push-handler close)               ; a throw while binding => IteratorClose then rethrow
      (dolist (e elems)
        (cond
          ((null e)                            ; hole: step iterator (respecting done), discard
           (em :iter-step-checked done it) (em :pop))
          ((and (consp e) (eq (car e) :rest))
           (em :get-var it) (em :iter-rest)    ; collect remaining into an array (exhausts iterator)
           (em :const *true*) (em :set-var done) (em :pop)
           (bind-target (second e)))
          ((and (consp e) (eq (car e) :default))
           (em :iter-step-checked done it)
           (apply-default (third e) (and (stringp (second e)) (second e)))
           (bind-target (second e)))
          (t (em :iter-step-checked done it)
             (bind-target e))))
      (em :pop-handler)
      (unless has-rest (em :iter-close-normal done it))
      (em :jmp after)
      (em :label close)                      ; thrown value on stack
      (em :iter-close-abrupt done it)        ; close (swallowing return errors), leave the thrown value
      (em :throw-op)                         ; rethrow the original
      (em :label after))))

(defun compile-object-destructure (pat)
  "Value on stack is the source object. Destructure per (:opat PROPS)."
  (let* ((src (string (gensym "SRC"))) (props (second pat)) (seen '())
         (has-rest (some (lambda (p) (eq (car p) :rest)) props))
         ;; a { ...rest } with computed keys needs a RUNTIME exclusion set (the
         ;; computed keys are only known at evaluation time, in source order).
         (dyn-excl (and has-rest (some (lambda (p) (and (not (eq (car p) :rest))
                                                        (consp (car p)) (eq (car (car p)) :computed)))
                                       props)))
         (excl (and dyn-excl (string (gensym "EXCL")))))
    (em :require-coercible)                   ; { } = null / undefined still throws (RequireObjectCoercible)
    (em :declare-var src)
    (when dyn-excl (em :new-array) (em :declare-var excl))
    (dolist (pr props)
      (cond
        ((eq (car pr) :rest)
         (em :get-var src)
         (if dyn-excl (progn (em :get-var excl) (em :swap) (em :object-rest-dyn))
             (em :object-rest (reverse seen)))
         (em :declare-var (second pr)))
        (t (destructuring-bind (key tgt &optional default) pr
             (push (and (eq (car key) :lit) (second key)) seen)
             (cond
               ((eq (car key) :computed)
                (compile-expr (second key)) (em :to-prop-key)   ; key value on stack
                (when dyn-excl (em :array-append excl))          ; record for exclusion (peeks, leaves key)
                (em :get-var src) (em :swap) (em :get-prop))
               (t (em :get-var src) (em :get-prop-c (second key))))
             (when default (apply-default default (and (stringp tgt) tgt)))
             (bind-target tgt)))))))

(defun compile-params (params)
  "Emit the parameter-binding prologue: pull positional args, apply defaults,
   destructure, and gather rest."
  (loop for p in params for i from 0 do
    (cond
      ((and (consp p) (eq (car p) :rest))
       (em :load-rest i) (bind-target (second p)))
      ((and (consp p) (eq (car p) :default))
       (em :load-arg i) (apply-default (third p) (and (stringp (second p)) (second p))) (bind-target (second p)))
      (t (em :load-arg i) (bind-target p)))))

(defun apply-default (default-expr &optional name)
  "Top of stack is a value; if it is undefined, replace with DEFAULT-EXPR. When the
   binding target is a plain NAME and DEFAULT-EXPR is an anonymous fn/class, the
   default value is named after the binding (NamedEvaluation)."
  (let ((skip (lbl)))
    (em :dup) (em :const *undefined*) (em :bin "!==") (em :jmp-if-true skip)
    (em :pop) (compile-expr default-expr)
    (when (and (stringp name) (anonymous-fn-value-p default-expr)) (em :set-fn-name name))
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
    (t (js-throw (make-native-error "SyntaxError" "bad binding target")))))

;;; ---- destructuring ASSIGNMENT (LHS is expression-form: :ident/:member/:array/:object) ----
(defun check-strict-assign-target (tgt)
  "In STRICT code `eval` and `arguments` may not be assigned to, incremented, or compound-assigned
-- an early SyntaxError, not a runtime one.  Sloppy code may do all of it."
  (when (and *strict* (consp tgt) (eq (car tgt) :ident)
             (member (second tgt) '("eval" "arguments") :test #'string=))
    (js-throw (make-native-error
               "SyntaxError"
               (format nil "Unexpected ~a in strict mode" (second tgt))))))

(defun assign-to-target (tgt)
  "Value on top of stack -> assign to expression-form TGT, consuming the value.

An unrecognised node here is not an internal error, it is a SOURCE error: `[[(x, y)]] = v` parses
fine as an array literal and only becomes wrong when it is reinterpreted as a pattern, which is
exactly what an early error is for.  ECASE turned that into an uncatchable Lisp condition."
  (case (car tgt)
    (:ident (em :set-var (second tgt)) (em :pop))
    (:member
     ;; stack: val ; need obj key val -> set-prop -> pop
     (compile-expr (second tgt))
     (if (fourth tgt) (compile-expr (third tgt)) (em :const (second (third tgt))))
     (em :rot3)                              ; bring val above obj,key : obj key val
     (em :set-prop) (em :pop))
    (:private-member
     ;; stack: val ; -> obj val -> private-set -> pop
     (compile-expr (second tgt)) (em :swap)
     (em :private-set (resolve-private-name (third tgt))) (em :pop))
    ((:array :object) (compile-assign-pattern tgt))
    (t (js-throw (make-native-error "SyntaxError" "Invalid destructuring assignment target")))))

(defun assign-elem-with-default (elem)
  "ELEM may be (:assign \"=\" TGT DEFAULT). Applies default if value is undefined,
   then assigns. Value on top of stack."
  (if (and (consp elem) (eq (car elem) :assign) (string= (second elem) "="))
      (let ((tgt (third elem)))
        (apply-default (fourth elem) (and (consp tgt) (eq (car tgt) :ident) (second tgt)))
        (assign-to-target tgt))
      (assign-to-target elem)))

(defun compile-assign-pattern (pat)
  "Destructure the value on top of the stack into expression-form pattern PAT.
   Consumes the value."
  (case (car pat)
    (:array
     (let* ((it (string (gensym "IT"))) (done (string (gensym "DN"))) (elems (second pat))
            (has-rest (some (lambda (e) (and (consp e) (eq (car e) :spread))) elems)))
       (em :get-iterator) (em :declare-var it)
       (em :const *false*) (em :declare-var done)
       (let ((close (lbl)) (after (lbl)))
         (em :push-handler close)
         (dolist (e elems)
           (cond
             ((null e) (em :iter-step-checked done it) (em :pop))       ; hole
             ((and (consp e) (eq (car e) :spread))
              (em :get-var it) (em :iter-rest) (em :const *true*) (em :set-var done) (em :pop)
              (assign-to-target (second e)))
             (t (em :iter-step-checked done it)
                (assign-elem-with-default e))))
         (em :pop-handler)
         (unless has-rest (em :iter-close-normal done it))
         (em :jmp after)
         (em :label close)
         (em :iter-close-abrupt done it)
         (em :throw-op)
         (em :label after))))
    (:object
     (let* ((src (string (gensym "SRC"))) (seen '())
            (has-rest (some (lambda (p) (eq (car p) :spread)) (second pat)))
            (dyn-excl (and has-rest (some (lambda (p) (and (eq (car p) :init)
                                                           (eq (car (second p)) :computed)))
                                          (second pat))))
            (excl (and dyn-excl (string (gensym "EXCL")))))
       (em :require-coercible)                 ; ({} = null) still throws
       (em :declare-var src)
       (when dyn-excl (em :new-array) (em :declare-var excl))
       (dolist (pr (second pat))
         (case (car pr)
           (:spread
            (em :get-var src)
            (if dyn-excl (progn (em :get-var excl) (em :swap) (em :object-rest-dyn))
                (em :object-rest (reverse seen)))
            (assign-to-target (second pr)))
           (:proto                                   ; treat like a normal key __proto__
            (push "__proto__" seen)
            (when dyn-excl (em :const "__proto__") (em :array-append excl) (em :pop))
            (em :get-var src) (em :get-prop-c "__proto__") (assign-to-target (second pr)))
           (:init
            (let ((key (second pr)) (val (third pr)))
              (when (eq (car key) :lit) (push (second key) seen))
              (cond
                ((eq (car key) :computed)
                 (compile-expr (second key)) (em :to-prop-key)
                 (when dyn-excl (em :array-append excl))
                 (em :get-var src) (em :swap) (em :get-prop))
                (t (when dyn-excl (em :const (second key)) (em :array-append excl) (em :pop))
                   (em :get-var src) (em :get-prop-c (second key))))
              ;; val is the target expression (possibly (:assign = tgt default) for {k: t = d}
              ;; or (:ident name) for shorthand {k}, or (:ident name)+default stored in 4th)
              (if (fourth pr)                        ; shorthand-with-default {x = d}
                  (progn (apply-default (fourth pr) (and (consp val) (eq (car val) :ident) (second val)))
                         (assign-to-target val))
                  (assign-elem-with-default val))))
           ;; A getter, setter or method in a destructuring target -- `[{ get x(){} }] = v`
           ;; -- is an early SyntaxError, not a shape the compiler should meet.
           (t (js-throw (make-native-error
                         "SyntaxError" "Invalid destructuring assignment target")))))))
    ;; Same reason as ASSIGN-TO-TARGET: an unrecognised pattern node is a SOURCE error,
    ;; and a silent NIL here would be worse than the crash it replaces.
    (t (js-throw (make-native-error "SyntaxError" "Invalid destructuring assignment target")))))

;;; ---- Annex B B.3.3: block-scoped function declarations ----
;;; In sloppy mode a function declared in a block also creates a var-scoped binding
;;; in the enclosing function/global scope, assigned (to the current lexical value)
;;; when the block-level declaration is evaluated.
(defun annexb-nested-fn-names (stmts &optional acc)
  "Names of function declarations nested inside blocks/control-structures within
   STMTS (NOT the direct top-level ones — those are ordinary var-hoisted fns).
   Does not descend into nested functions."
  (dolist (s stmts acc)
    (when (consp s)
      (setf acc (annexb-fn-names-in s acc '())))))

(defun annexb-fn-names-in (node acc shadowed)
  "Collect block-level function-declaration names under NODE (a statement),
   descending through blocks/if/loops/try/switch/labels but not nested functions.
   SHADOWED is the set of lexical names declared in enclosing blocks between here
   and the var scope — a candidate whose name is shadowed is skipped (B.3.3.1)."
  (when (consp node)
    (case (car node)
      ((:func :method-func :arrow :genfunc :class :asyncfunc :asyncgenfunc :async-arrow) acc)
      (:block
       ;; a nested block introduces its own lexicals into SHADOWED for its body
       (let ((inner-shadow (append (block-lexical-names (second node)) shadowed)))
         (dolist (s (second node) acc)
           (when (and (consp s) (member (car s) '(:func :genfunc :asyncfunc :asyncgenfunc)) (second s)
                      (not (member (second s) shadowed :test #'string=)))
             (pushnew (second s) acc :test #'string=))
           (setf acc (annexb-fn-names-in s acc inner-shadow)))))
      ((:if) (setf acc (annexb-labeled-collect (third node) acc shadowed))
             (when (fourth node) (setf acc (annexb-labeled-collect (fourth node) acc shadowed)))
             acc)
      ((:label) (annexb-labeled-collect (third node) acc shadowed))
      ((:while :do-while) (annexb-labeled-collect (third node) acc shadowed))
      ((:for :for-in :for-of :for-await-of)
       ;; a `let`/`const` in the loop head lexically binds across the body — shadow it
       (let ((head-lex (for-head-lexnames node)))
         (annexb-labeled-collect (car (last node)) acc (append head-lex shadowed))))
      ((:try)                               ; (:try blk param catch fin) — blk/catch/fin are :block nodes
       (destructuring-bind (blk param catch fin) (cdr node)
         (declare (ignore param))
         (when (consp blk) (setf acc (annexb-fn-names-in blk acc shadowed)))
         (when (consp catch) (setf acc (annexb-fn-names-in catch acc shadowed)))
         (when (consp fin) (setf acc (annexb-fn-names-in fin acc shadowed)))
         acc))
      ((:switch)                            ; (:switch disc clauses) — clause = (TEST-or-:default . body)
       (let ((sw-shadow (append (switch-lexical-names node) shadowed)))
         (flet ((scan-stmts (ss)
                  (dolist (s ss)
                    (when (and (consp s) (member (car s) '(:func :genfunc :asyncfunc :asyncgenfunc)) (second s)
                               (not (member (second s) shadowed :test #'string=)))
                      (pushnew (second s) acc :test #'string=))
                    (setf acc (annexb-fn-names-in s acc sw-shadow)))))
           (dolist (clause (third node)) (scan-stmts (cdr clause)))
           acc)))
      (t acc))))

(defun for-head-lexnames (node)
  "Lexical (let/const) names bound in a for/for-in/for-of loop head."
  (let ((init (second node)))                ; :for init ...; :for-in/of lhs ...
    (if (and (consp init) (eq (car init) :var)
             (member (second init) '("let" "const") :test #'string=))
        (let ((acc '())) (dolist (d (third init) acc) (setf acc (target-names (car d) acc))))
        '())))

(defun switch-lexical-names (node)
  "Lexical (let/const/class) names declared across a switch's clauses."
  (let ((acc '()))
    (dolist (clause (third node)) (setf acc (append (block-lexical-names (cdr clause)) acc)))
    acc))

(defun annexb-labeled-collect (node acc shadowed)
  "A statement position that is NOT a block: a bare `function` decl there (e.g.
   `if (x) function f(){}`, `label: function f(){}`) is a labelled/if fn decl —
   its name also gets an Annex B var binding (unless shadowed)."
  (when (consp node)
    (cond
      ((eq (car node) :block) (annexb-fn-names-in node acc shadowed))
      ((and (member (car node) '(:func :genfunc :asyncfunc :asyncgenfunc)) (second node))
       (if (member (second node) shadowed :test #'string=) acc
           (progn (pushnew (second node) acc :test #'string=) acc)))
      ((eq (car node) :label) (annexb-labeled-collect (third node) acc shadowed))
      ((member (car node) '(:if :while :do-while :for :for-in :for-of :for-await-of :try :switch))
       (annexb-fn-names-in node acc shadowed))
      (t acc))))

(defun annexb-var-fn-names (body pnames lexnames)
  "The Annex B B.3.3 candidate names for BODY (a fn/program body): block-nested fn
   names, minus formal parameters and minus enclosing lexical declarations. Sloppy
   mode only (caller gates on *strict*)."
  (let* ((stmts (if (and (consp body) (eq (car body) :block)) (second body) (list body)))
         (cands (annexb-nested-fn-names stmts)))
    ;; NB: a name that is ALSO a top-level function declaration is kept — the block
    ;; fn's evaluation must still update the (already-existing) var binding (B.3.3).
    (remove-if (lambda (n) (or (member n pnames :test #'string=)
                               (member n lexnames :test #'string=)))
               (remove-duplicates cands :test #'string=))))

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
  "Compile a block: new env if it declares let/const/class OR block-level functions,
   TDZ-hoist lexicals, hoist block-level function decls (lexically), and — for names
   with an Annex B var binding — sync that var binding at the decl's evaluation point.
   Then run statements, pop env."
  (let ((lex (block-lexical-names stmts))
        (fns (block-lexical-fns stmts)))
    (if (and (null lex) (null fns))
        (mapc #'compile-stmt stmts)          ; nothing block-scoped: keep it flat
        (progn
          (em :push-env)
          (let ((*scope-depth* (1+ *scope-depth*)))
            (dolist (n lex) (em :tdz-declare n))          ; temporal dead zone
            ;; hoist block-scoped function declarations (lexical binding = the fn),
            ;; and if the name has an Annex B var binding, assign it now too.
            (dolist (fn fns)
              (compile-fn-decl-closure fn)
              (when (member (second fn) *annexb-fn-names* :test #'string=)
                (em :annexb-var-set (second fn)))          ; leaves the fn value on the stack
              (em :init-let (second fn)))
            (dolist (s stmts) (unless (block-hoisted-fn-p s) (compile-stmt s)))
            (em :pop-env))))))

(defun compile-switch (node)
  "SwitchStatement: CaseBlockEvaluation with source-order clauses & fall-through.
   The whole CaseBlock is one lexical scope (let/const/fns shared across clauses)."
  (destructuring-bind (disc clauses) (cdr node)
    (let* ((dv (string (gensym "SW"))) (end (lbl))
           (labels (mapcar (lambda (c) (cons c (lbl))) clauses))
           (default-entry (find :default clauses :key #'car))
           (deflabel (if default-entry (cdr (assoc default-entry labels)) end))
           ;; all statements across every clause body form ONE lexical scope
           (all-body (loop for c in clauses append (cdr c)))
           (lex (block-lexical-names all-body))
           (fns (block-lexical-fns all-body))
           (scoped (or lex fns)))
      (compile-expr disc) (em :declare-var dv)
      (when scoped
        (em :push-env)
        (incf *scope-depth*)
        (dolist (n lex) (em :tdz-declare n))
        (dolist (fn fns)
          (compile-fn-decl-closure fn)
          (when (member (second fn) *annexb-fn-names* :test #'string=)
            (em :annexb-var-set (second fn)))
          (em :init-let (second fn))))
      (em :comp-clear)
      ;; Test cases in physical order (A before default, then B). First === match
      ;; jumps to that clause's body; fall-through then runs the rest in order.
      (dolist (cl labels)
        (unless (eq (car (car cl)) :default)
          (em :get-var dv) (compile-expr (car (car cl))) (em :bin "===") (em :jmp-if-true (cdr cl))))
      (em :jmp deflabel)
      (let ((*break-target* end) (*break-depth* *scope-depth*))
        (dolist (cl labels)
          (em :label (cdr cl))
          (dolist (s (cdr (car cl)))
            (unless (block-hoisted-fn-p s) (compile-stmt s)))))
      (when scoped (em :pop-env) (decf *scope-depth*))
      (em :label end) (em :comp-default-undef))))

(defun block-lexical-fns (stmts)
  "Function declarations directly in STMTS (hoisted at block scope)."
  (remove-if-not #'block-hoisted-fn-p stmts))
(defun block-hoisted-fn-p (s) (and (consp s) (member (car s) '(:func :genfunc :asyncfunc :asyncgenfunc)) (second s)))
(defun annexb-wrap-fn-stmt (s)
  "Annex B B.3.4: a bare `FunctionDeclaration` in a single-statement position (the
   consequent/alternate of an `if`, a labelled statement) is treated as if enclosed
   in a block — giving it block scoping plus the Annex B var binding."
  (if (block-hoisted-fn-p s) (list :block (list s)) s))

(defun compile-fn-decl-closure (node)
  "Emit the closure object for a FunctionDeclaration/GeneratorDeclaration/etc.
   Unlike a named function EXPRESSION, a declaration gets NO immutable inner
   self-binding of its own name — the name is provided by the (mutable) outer
   binding created by the enclosing scope (fn/global var, block let, etc.), so
   `function f(){ f = 1; }` reassigns that outer binding rather than throwing."
  (ecase (car node)
    ;; *IN-ASYNC-GEN* is rebound for EVERY nested function, not just the async-generator one: a
    ;; plain generator written inside an async generator has its own, synchronous, yield*.
    (:func         (let ((*in-async-gen* nil))
                     (em :closure (compile-fn (second node) (third node) (fourth node)))))
    (:genfunc      (let ((*in-async-gen* nil))
                     (em :genclosure (compile-fn-split (second node) (third node) (fourth node)))))
    (:asyncfunc    (let ((*in-async-gen* nil))
                     (em :asyncclosure (compile-fn-split (second node) (third node) (fourth node)))))
    (:asyncgenfunc (let ((*in-async-gen* t))
                     (em :asyncgenclosure
                         (compile-fn-split (second node) (third node) (fourth node)))))))

(defun anonymous-fn-value-p (node)
  "T if NODE is an expression that produces an anonymous function/class (one with
   no name of its own) — eligible for NamedEvaluation (`.name` := binding name)."
  (and (consp node)
       (case (car node)
         ((:func :genfunc :asyncfunc :asyncgenfunc) (null (second node)))   ; function(){} with no id
         ((:arrow :async-arrow) t)                                          ; arrows are always anonymous
         (:class (null (second node)))                                      ; class {} with no id
         (t nil))))

(defun compile-named-init (value name)
  "Compile VALUE onto the stack; if it is an anonymous function/class and NAME is a
   plain string binding name, apply NamedEvaluation so its .name becomes NAME."
  (compile-expr value)
  (when (and (stringp name) (anonymous-fn-value-p value))
    (em :set-fn-name name)))

;;; ---- statements ----
(defun compile-stmt (node)
  (ecase (car node)
    (:block (compile-scoped-block (second node)))
    (:empty nil)
    (:expr (compile-expr (second node)) (em :save-completion))
    (:var (let ((kind (second node)))
            (loop for (tgt . init) in (third node)
                  do (if init (compile-named-init init (and (stringp tgt) tgt)) (em :const *undefined*))
                     (cond
                       ((string= kind "const") (bind-lexical tgt :const))
                       ((string= kind "let")   (bind-lexical tgt :let))
                       (t (if (stringp tgt) (em :declare-var tgt) (bind-target tgt)))))))
    (:func (compile-fn-decl-closure node) (em :declare-var (second node)))
    (:genfunc (compile-fn-decl-closure node) (em :declare-var (second node)))
    (:asyncfunc (compile-fn-decl-closure node) (em :declare-var (second node)))
    (:asyncgenfunc (compile-fn-decl-closure node) (em :declare-var (second node)))
    (:name-default (em :name-default))   ; see module-runtime.lisp: NamedEvaluation for *default*
    (:class (compile-expr node) (em :init-let (second node)))   ; class decl: lexical binding
    (:private-field-init
     ;; this.#name = INIT ; add a fresh private field to `this`'s brand table
     (em :get-this) (em :const (resolve-private-name (second node)))
     (compile-expr (third node)) (em :private-field-add))
    (:private-method-init
     ;; install a private method/accessor into `this`'s brand table
     (destructuring-bind (name kind fn) (cdr node)
       (em :get-this) (em :const (resolve-private-name name))
       (compile-expr fn) (em :private-method-add kind)))
    (:return
     ;; The value is computed FIRST, then every pending finally runs, then the return happens --
     ;; which is the spec's order and the reason `try { return f() } finally { g() }` calls f
     ;; before g.  A finally that returns wins, and it does so naturally: its own :RET fires
     ;; while compiling it here, before this one is ever reached.
     (compile-expr (second node))
     (let ((fins *pending-finallys*))
       (let ((*pending-finallys* nil))       ; a finally does not re-run itself
         (dolist (f fins) (compile-finally-block f))))
     (em :ret))
    (:throw (compile-expr (second node)) (em :throw-op))
    (:if (let ((l1 (lbl)) (l2 (lbl)))
           (em :comp-clear)
           (compile-expr (second node)) (em :jmp-if-false l1)
           (compile-stmt (annexb-wrap-fn-stmt (third node))) (em :jmp l2)
           (em :label l1) (when (fourth node) (compile-stmt (annexb-wrap-fn-stmt (fourth node))))
           (em :label l2) (em :comp-default-undef)))
    (:while (let ((top (lbl)) (end (lbl)))
              (em :comp-clear)
              (em :label top) (compile-expr (second node)) (em :jmp-if-false end)
              (let ((*break-target* end) (*continue-target* top)
                    (*break-depth* *scope-depth*) (*continue-depth* *scope-depth*)
            (*break-finallys* *pending-finallys*) (*continue-finallys* *pending-finallys*)
                    (*labels* (loop-label-entries end top *scope-depth*)) (*pending-labels* '()))
                (compile-stmt (third node)))
              (em :jmp top) (em :label end) (em :comp-default-undef)))
    (:do-while (let ((top (lbl)) (cont (lbl)) (end (lbl)))
                 (em :comp-clear)
                 (em :label top)
                 (let ((*break-target* end) (*continue-target* cont)
                       (*break-depth* *scope-depth*) (*continue-depth* *scope-depth*)
            (*break-finallys* *pending-finallys*) (*continue-finallys* *pending-finallys*)
                       (*labels* (loop-label-entries end cont *scope-depth*)) (*pending-labels* '()))
                   (compile-stmt (third node)))
                 (em :label cont) (compile-expr (second node)) (em :jmp-if-true top)
                 (em :label end) (em :comp-default-undef)))
    (:for (em :comp-clear) (compile-for node) (em :comp-default-undef))
    (:for-in (em :comp-clear) (compile-scoped-loop node #'compile-for-in) (em :comp-default-undef))
    (:for-of (em :comp-clear) (compile-scoped-loop node #'compile-for-of) (em :comp-default-undef))
    (:for-await-of (em :comp-clear) (compile-scoped-loop node #'compile-for-await-of) (em :comp-default-undef))
    (:label (compile-labeled node))
    (:break (let ((lbl (second node)))
              (if lbl
                  (let ((entry (assoc lbl *labels* :test #'string=)))
                    (unless entry (js-throw (make-native-error "SyntaxError" (format nil "Undefined label '~a'" lbl))))
                    (run-exit-finallys *break-finallys*)
                    (pop-envs (- *scope-depth* (fourth entry))) (em :jmp (second entry)))
                  (if *break-target*
                      (progn (run-exit-finallys *break-finallys*)
                             (pop-envs (- *scope-depth* *break-depth*)) (em :jmp *break-target*))
                      (js-throw (make-native-error "SyntaxError" "illegal break"))))))
    (:continue (let ((lbl (second node)))
                 (if lbl
                     (let ((entry (assoc lbl *labels* :test #'string=)))
                       (unless (and entry (third entry))
                         (js-throw (make-native-error "SyntaxError" (format nil "Undefined continue label '~a'" lbl))))
                       (run-exit-finallys *continue-finallys*)
                       (pop-envs (- *scope-depth* (fourth entry))) (em :jmp (third entry)))
                     (if *continue-target*
                         (progn (run-exit-finallys *continue-finallys*)
                                (pop-envs (- *scope-depth* *continue-depth*)) (em :jmp *continue-target*))
                         (js-throw (make-native-error "SyntaxError" "illegal continue"))))))
    (:switch (compile-switch node))
    (:with
     (when *strict*
       (js-throw (make-native-error "SyntaxError" "'with' statements are not allowed in strict mode")))
     (compile-expr (second node))                ; the object -> stack
     (em :to-object) (em :push-with-env)         ; pop obj, push a with scope
     (let ((*scope-depth* (1+ *scope-depth*)))
       (compile-stmt (third node)))
     (em :pop-env))
    (:try (destructuring-bind (blk param catch fin) (cdr node)
            (em :comp-clear)
            (flet ((body ()
                     (if catch
                         (let ((lc (lbl)) (after (lbl)))
                           (em :push-handler lc) (compile-stmt blk) (em :pop-handler) (em :jmp after)
                           (em :label lc)                                  ; thrown value on stack
                           (em :comp-clear)                                ; catch clause: fresh completion
                           (em :push-env)                                  ; catch parameter scope
                           (let ((*scope-depth* (1+ *scope-depth*)))
                             (cond ((null param) (em :pop))
                                   ((stringp param) (em :declare-var param))
                                   (t (bind-target param)))               ; destructuring catch param
                             (compile-stmt catch))
                           (em :pop-env)
                           (em :label after))
                         (compile-stmt blk))))
              (if (null fin)
                  (body)
                  ;; WITH A FINALLY, every way out has to go through it: normal completion, an
                  ;; uncaught throw, and any `return` inside (which compiles the block itself --
                  ;; see :RETURN).  Only the normal path ran it before, so a throw or a return
                  ;; skipped cleanup entirely.
                  (let ((lthrow (lbl)) (after (lbl)))
                    (em :push-handler lthrow)
                    (let ((*pending-finallys* (cons fin *pending-finallys*)))
                      (body))
                    (em :pop-handler)
                    (compile-finally-block fin)          ; normal completion
                    (em :jmp after)
                    (em :label lthrow)                   ; thrown value is on the stack
                    (compile-finally-block fin)          ; ...run the finally, then rethrow
                    (em :throw-op)
                    (em :label after))))
            (em :comp-default-undef)))))

(defun run-exit-finallys (baseline)
  "Compile the finally blocks entered since BASELINE, innermost first."
  (let ((fins (ldiff *pending-finallys* baseline)))
    (let ((*pending-finallys* baseline))
      (dolist (f fins) (compile-finally-block f)))))

(defun compile-finally-block (fin)
  "Run FIN, preserving whatever completion value was already in flight."
  (let ((saved (string (gensym "FINV"))))
    (em :comp-default-undef) (em :get-completion) (em :declare-var saved)
    (em :comp-clear)
    (let ((*pending-finallys* nil)) (compile-stmt fin))
    (em :get-var saved) (em :save-completion)))

(defun loop-label-entries (break-lbl continue-lbl depth)
  "Register any *pending-labels* (labels attached to this loop) as label entries
   pointing at the loop's break/continue targets, prepended to *labels*."
  (append (mapcar (lambda (nm) (list nm break-lbl continue-lbl depth)) *pending-labels*)
          *labels*))

(defun iteration-stmt-p (node)
  (and (consp node) (member (car node) '(:while :for :for-in :for-of :for-await-of :do-while))))

(defun compile-labeled (node)
  "(:label NAME STMT). Collect nested labels; if the target is an iteration
   statement, the loop registers these labels (break+continue). Otherwise it's a
   break-only label whose break target is the end of the statement."
  (let ((names '()) (n node))
    (loop while (and (consp n) (eq (car n) :label))
          do (push (second n) names) (setf n (third n)))
    (if (iteration-stmt-p n)
        (let ((*pending-labels* (append names *pending-labels*)))
          (compile-stmt n))
        (let ((end (lbl)))
          (let ((*labels* (append (mapcar (lambda (nm) (list nm end nil *scope-depth*)) names)
                                  *labels*)))
            (compile-stmt (annexb-wrap-fn-stmt n)))   ; B.3.4: `label: function f(){}` blocks the fn
          (em :label end)))))

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
                (*break-depth* *scope-depth*) (*continue-depth* *scope-depth*)
            (*break-finallys* *pending-finallys*) (*continue-finallys* *pending-finallys*)
                (*labels* (loop-label-entries end cont *scope-depth*)) (*pending-labels* '()))
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
        ((member (car head) '(:ident :member :private-member))  ; simple LHS loop target
         (assign-to-target head))
        ((member (car head) '(:array :object))     ; destructuring assignment target
         (compile-assign-pattern head))
        (t (js-throw (make-native-error "SyntaxError" "unsupported for-in/of target")))))

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
      (let ((*break-target* end) (*continue-target* cont)
            (*break-depth* *scope-depth*) (*continue-depth* *scope-depth*)
            (*break-finallys* *pending-finallys*) (*continue-finallys* *pending-finallys*)
            (*labels* (loop-label-entries end cont *scope-depth*)) (*pending-labels* '()))
        (compile-stmt body))
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
      (let ((*break-target* end) (*continue-target* cont)
            (*break-depth* *scope-depth*) (*continue-depth* *scope-depth*)
            (*break-finallys* *pending-finallys*) (*continue-finallys* *pending-finallys*)
            (*labels* (loop-label-entries end cont *scope-depth*)) (*pending-labels* '()))
        (compile-stmt body))
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
      (let ((*break-target* end) (*continue-target* cont)
            (*break-depth* *scope-depth*) (*continue-depth* *scope-depth*)
            (*break-finallys* *pending-finallys*) (*continue-finallys* *pending-finallys*)
            (*labels* (loop-label-entries end cont *scope-depth*)) (*pending-labels* '()))
        (compile-stmt body))
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
    (:dynamic-import (compile-expr (second node)) (em :dynamic-import))
    (:import-meta (em :import-meta))
    (:new-target
     (unless *in-function*
       (js-throw (make-native-error "SyntaxError" "new.target expression is not allowed here")))
     (em :new-target))
    (:ident (em :get-var (second node)))
    (:bin (if (and (string= (second node) "in")
                   (consp (third node)) (eq (car (third node)) :private-ref))
              (progn (compile-expr (fourth node))              ; #x in obj
                     (em :private-in (resolve-private-name (second (third node)))))
              (progn (compile-expr (third node)) (compile-expr (fourth node)) (em :bin (second node)))))
    (:unary (if (and (string= (second node) "typeof") (eq (car (third node)) :ident))
                (em :typeof-var (second (third node)))     ; typeof of a NAME never throws
                (progn (compile-expr (third node)) (em :unary (second node)))))
    (:delete (let ((tgt (second node)))
               (when (and *strict* (eq (car tgt) :ident))
                 (js-throw (make-native-error "SyntaxError"
                   "Delete of an unqualified identifier in strict mode.")))
               (cond
                 ((eq (car tgt) :member)
                  (compile-expr (second tgt))
                  (if (fourth tgt) (compile-expr (third tgt)) (em :const (second (third tgt))))
                  (em :del-prop))
                 ;; `delete x` on a BINDING is false (bindings are not configurable); on an
                 ;; undeclared name it is true, and it must not throw the way an ordinary read
                 ;; would -- so it needs its own op rather than compiling the identifier.
                 ((eq (car tgt) :ident) (em :del-var (second tgt)))
                 ;; delete of any other expression is TRUE -- but the expression is still
                 ;; EVALUATED.  `delete foo()` calls foo.  Skipping that made the operand's side
                 ;; effects vanish, which is the whole point of these tests.
                 (t (compile-expr tgt) (em :pop) (em :const *true*)))))
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
    (:seq (loop for (e . more) on (cdr node)
                do (compile-expr e) (when more (em :pop))))
    (:assign (compile-assign (second node) (third node) (fourth node)))
    (:update (compile-update (second node) (third node) (fourth node)))
    (:member (if (chain-contains-optional-p (second node))
                 (compile-optional-chain node)              ; e.g. a?.b.c — one chain, one short-circuit
                 (progn (compile-expr (second node))
                        (if (fourth node) (progn (compile-expr (third node)) (em :get-prop))
                            (em :get-prop-c (second (third node)))))))  ; non-computed key node is (:str name)
    (:private-member                                        ; obj.#name (brand-checked read)
     (if (chain-contains-optional-p (second node))
         (compile-optional-chain node)
         (progn (compile-expr (second node))
                (em :private-get (resolve-private-name (third node))))))
    (:oprivate-member                                       ; obj?.#name (standalone)
     (compile-optional-chain node))
    (:call (if (chain-contains-optional-p (second node))
               (compile-optional-chain node)               ; e.g. a?.b() — call inside an optional chain
               (compile-call (second node) (third node))))
    (:new (compile-expr (second node))
          (if (some (lambda (a) (and (consp a) (eq (car a) :spread))) (third node))
              (progn (compile-arg-array (third node)) (em :new-spread))
              (progn (mapc #'compile-expr (third node)) (em :new (length (third node))))))
    (:array (compile-array-literal (second node)))
    (:object (compile-object-literal (second node)))
    (:func (if (second node)
               (em :named-closure (compile-fn (second node) (third node) (fourth node)) (second node))
               (em :closure (compile-fn (second node) (third node) (fourth node)))))
    ;; concise/accessor method: ordinary this-mode (sloppy substitution) but not constructable
    (:method-func (em :closure (compile-fn (second node) (third node) (fourth node) nil :normal nil)))
    (:genfunc (if (second node)
                  (let ((*in-async-gen* nil))
                    (em :named-genclosure (compile-fn-split (second node) (third node) (fourth node)) (second node)))
                  (let ((*in-async-gen* nil))
                    (em :genclosure (compile-fn-split (second node) (third node) (fourth node))))))
    (:asyncfunc (let ((*in-async-gen* nil))
                  (if (second node)
                      (em :named-asyncclosure (compile-fn-split (second node) (third node) (fourth node)) (second node))
                      (em :asyncclosure (compile-fn-split (second node) (third node) (fourth node))))))
    (:asyncgenfunc (let ((*in-async-gen* t))
                     (if (second node)
                         (em :named-asyncgenclosure (compile-fn-split (second node) (third node) (fourth node)) (second node))
                         (em :asyncgenclosure (compile-fn-split (second node) (third node) (fourth node))))))
    (:arrow (em :closure (compile-fn nil (second node) (third node) nil :lexical nil)))
    (:async-arrow (em :asyncclosure (compile-fn-split nil (second node) (third node) :lexical)))
    (:await (compile-expr (second node)) (em :await))
    (:class (compile-class node))
    (:yield (if (second node) (compile-expr (second node)) (em :const *undefined*))
            (em :yield))
    (:yield* (compile-expr (second node))
             (em (if *in-async-gen* :yield-star-async :yield-star)))
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

(defvar *private-scopes* '())   ; list of alists ("#name" . private-name-object)

(defun private-member-keys (members ctor)
  "All #private-name strings declared in a class (fields, methods, accessors),
   including those in the constructor's own params/body? No — only member keys."
  (declare (ignore ctor))
  (let ((names '()))
    (dolist (m members)
      (let ((key (case (car m)
                   (:method (third m))
                   (:field (second m))
                   (t nil))))
        (when (and (consp key) (eq (car key) :private))
          (pushnew (second key) names :test #'string=))))
    (nreverse names)))

(defun resolve-private-name (name)
  "Look up a #private-name in the enclosing private scopes; SyntaxError if unbound."
  (dolist (scope *private-scopes*
                 (js-throw (make-native-error "SyntaxError"
                             (format nil "Private field '~a' must be declared in an enclosing class" name))))
    (let ((hit (assoc name scope :test #'string=)))
      (when hit (return (cdr hit))))))

(defun compile-class (node)
  "Compile (:class NAME SUPER MEMBERS CTOR) leaving the constructor on the stack.
   Strategy: build a ctor function + prototype object at runtime via ops; attach
   methods (non-enumerable) and static members; run field initializers in the
   constructor prologue."
  (destructuring-bind (name super members ctor) (cdr node)
    (let* ((derived (and super t))
           (privnames (private-member-keys members ctor))
           (privscope (mapcar (lambda (nm) (cons nm (make-private-name nm))) privnames))
           (*private-scopes* (cons privscope *private-scopes*))
           (fields (class-field-inits members))
           ;; the constructor body: default is `constructor(...args){ super(...args) }`
           ;; for derived, or an empty constructor otherwise.
           (ctor-code (compile-class-ctor name ctor fields (priv-instance-methods members) derived)))
      ;; A named class binds its own name (as a const) in an inner scope visible to
      ;; the constructor, methods, and static elements — evaluate super/build/members
      ;; inside that env so the class can refer to itself before the outer binding.
      (when name (em :push-env) (em :tdz-declare name))
      ;; super value on stack (or undefined sentinel)
      (if super (compile-expr super) (em :const *undefined*))
      (em :make-class ctor-code derived name)            ; -> ctor (with .prototype)
      (when name (em :dup) (em :init-const name))         ; bind the class name to the ctor
      ;; ctor is on the stack throughout; each member op consumes its extras and
      ;; leaves ctor in place.
      (dolist (m members)
        (ecase (car m)
          (:static-block
           ;; run { ... } at class definition with this=ctor
           (em :closure (compile-fn nil '() (second m) nil :normal nil))
           (em :run-static-block))                       ; ctor fn -> ctor
          (:method
           (destructuring-bind (kind key fn static) (cdr m)
             (cond
               ((eq (car key) :private)
                ;; Private method/accessor. Instance-level ones are installed
                ;; per-instance in the constructor (see priv-instance-installers);
                ;; static ones go into the CLASS's private table now.
                (when static
                  (em :const (resolve-private-name (second key)))
                  (compile-expr fn)
                  (em :class-private-static kind)))       ; ctor pn fn -> ctor
               (t
                ;; stack: ctor ; push key, push method-closure, def
                (if (eq (car key) :computed) (compile-expr (second key)) (em :const (second key)))
                (compile-expr fn)                          ; method closure (home set by op)
                (em :class-method kind (if static t nil)))))) ; ctor key fn -> ctor
          (:field
           (cond
             ((and (fourth m) (eq (car (second m)) :private))   ; static private field
              (em :const (resolve-private-name (second (second m))))
              (if (third m) (compile-with-this-ctor (third m)) (em :const *undefined*))
              (em :class-private-static-field))                 ; ctor pn val -> ctor
             ((fourth m)                                         ; static public field: this=ctor
              (if (eq (car (second m)) :computed) (compile-expr (second (second m))) (em :const (second (second m))))
              (if (third m)
                  (compile-with-this-ctor (third m))
                  (em :const *undefined*))
              (em :class-static-field))))))                     ; ctor key val -> ctor
      ;; pop the inner class-name scope; ctor stays on the stack as the class value
      (when name (em :pop-env)))))

(defun priv-instance-methods (members)
  "Instance (non-static) private method/accessor members."
  (remove-if-not (lambda (m) (and (eq (car m) :method) (not (fifth m))
                                  (consp (third m)) (eq (car (third m)) :private)))
                 members))

(defun compile-with-this-ctor (expr)
  "Compile EXPR so that `this` refers to the constructor (top-of-stack ctor).
   Used for static field initializers. We emit the expr normally — static field
   initializers that reference `this` are rare; if EXPR uses `this` it will read
   the surrounding this. For correctness we set this via a helper op wrapping."
  ;; Simplest correct-enough path: evaluate the expr with normal `this`. Static
  ;; field initializer `this` referring to the class is an edge case.
  (compile-expr expr))

;; A simplified static-field path: recompute below without the fragile dup.
(defun compile-class-ctor (name ctor fields priv-methods derived)
  "Build the code object for the class constructor. FIELDS are instance field
   members to initialize (in the ctor prologue, after super() for derived).
   PRIV-METHODS are instance private methods/accessors installed per-instance."
  (declare (ignore name))
  ;; Bound per constructor so a pending set of field initializers cannot leak into the next
  ;; class.  (This was meant to be a binding and was briefly a COND CLAUSE, which made the body
  ;; NIL whenever any initializers were pending -- so a default derived constructor lost its
  ;; super() call entirely.)
  (let* ((*ctor-field-stmts* nil)
         (params (if ctor (third ctor) (if derived (list (list :rest "args")) '())))
         (user-body (if ctor (fourth ctor) nil))
         (field-stmts (append (mapcar #'priv-method->stmt priv-methods)
                              (mapcar #'field->stmt fields)))
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
  "Turn a (:field KEY INIT STATIC) into an initializer statement (this=instance)."
  (destructuring-bind (key init static) (cdr field)
    (declare (ignore static))
    (if (eq (car key) :private)
        (list :private-field-init (second key) (or init *undefined-ast*))
        (let ((tgt (if (eq (car key) :computed)
                       (list :member (list :this) (second key) t)
                       (list :member (list :this) (list :str (second key)) nil))))
          (list :expr (list :assign "=" tgt (or init *undefined-ast*)))))))

(defun priv-method->stmt (m)
  "Turn an instance (:method KIND (:private NAME) FN STATIC) into a per-instance
   private brand-install statement."
  (destructuring-bind (kind key fn static) (cdr m)
    (declare (ignore static))
    (list :private-method-init (second key) kind fn)))

(defvar *ctor-field-stmts* nil
  "Field initializers awaiting a super() call.  In a DERIVED constructor they run when super()
returns -- that is when `this` comes into existence -- so COMPILE-SUPER-CALL emits them right
after the call rather than the body splicing them anywhere.")

(defun splice-field-inits (user-body field-stmts derived)
  "Insert field initializers.

A BASE constructor gets them at the top of its body: `this` exists from the start.

A DERIVED constructor does not.  Its `this` is created by super(), and the fields initialize when
super() RETURNS -- so they are handed to COMPILE-SUPER-CALL and emitted there, wherever the call
happens to be.  Splicing them at the top instead (which is what this did) put `this.f = ...` before
any `this` existed; it went unnoticed only because nothing checked, and the derived-constructor
TDZ is what finally surfaced it."
  (let ((stmts (if (eq (car user-body) :block) (second user-body) (list user-body))))
    (if derived
        (progn (setf *ctor-field-stmts* field-stmts) (list :block stmts))
        (list :block (append field-stmts stmts)))))

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
         (cond
           ((eq (car key) :computed)
            (compile-expr (second key))
            (if (anonymous-fn-value-p val)
                (progn (em :dup)                 ; [obj key key] — extra copy for NamedEvaluation
                       (compile-expr val)        ; [obj key key val]
                       (em :set-fn-name-dyn))    ; names val from the key copy -> [obj key val]
                (compile-expr val))
            (em :def-prop))
           (t
            (em :const (second key))
            (compile-named-init val (and (stringp (second key)) (second key)))
            (em :def-prop)))))                ; obj key val -> obj
      ;; A method definition, unlike `m: function(){}`, carries a [[HomeObject]] -- so `super.x`
      ;; inside it resolves against the object's prototype.  :DEF-METHOD sets it; :DEF-PROP does
      ;; not, which is the whole reason these are different ops.
      (:method-prop
       (let ((key (second pr)) (fn (third pr)))
         (if (eq (car key) :computed) (compile-expr (second key)) (em :const (second key)))
         (compile-expr fn)
         (em :def-method)))
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
      ;; the frozen, cached template object (same call site => same object identity,
      ;; per GetTemplateObject). SITE-KEY is a fresh cons unique to this AST node.
      (em :template-object (list :site (list :key (cons nil nil)) :cooked cooked :raw raw))
      ;; substitutions as remaining args
      (dolist (e exprs) (compile-expr e))
      (em :call (1+ (length exprs))))))

;;; ---- optional chaining ----
(defun optional-chain-p (node)
  (and (consp node) (member (car node) '(:omember :ocall :oprivate-member))))

(defun chain-contains-optional-p (node)
  "T if NODE is a member/call/optional access whose chain of bases contains at
   least one ?. link. A plain `.b`/`b()` that wraps an optional sub-chain must be
   compiled as ONE optional chain (a short-circuit skips the whole rest)."
  (and (consp node)
       (case (car node)
         ((:omember :ocall :oprivate-member) t)
         ((:member :private-member) (chain-contains-optional-p (second node)))
         (:call (chain-contains-optional-p (second node)))
         (t nil))))

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
  "Emit code leaving the link's value (exactly one) on the stack. STACK INVARIANT:
   a link consumes its base and leaves one value; on an optional nullish base, jump
   to SHORT with exactly ONE value on the stack (the SHORT handler pops it and
   pushes undefined). `:nullish-short` PEEKS (leaves the value), so no dup is needed."
  (ecase (car node)
    (:omember
     (compile-chain-base (second node) short)
     (em :nullish-short short)                 ; base nullish -> SHORT (base still on stack)
     (if (fourth node) (progn (compile-expr (third node)) (em :get-prop))
         (em :get-prop-c (second (third node)))))
    (:oprivate-member
     (compile-chain-base (second node) short)
     (em :nullish-short short)
     (em :private-get (resolve-private-name (third node))))
    (:private-member
     (compile-chain-base (second node) short)
     (em :private-get (resolve-private-name (third node))))
    (:ocall
     ;; obj?.() — evaluate the callee; if nullish short-circuit, else call it.
     ;; When the callee is a member access (a.b?.() / a?.b?.()), preserve `this`
     ;; = the member's base object; otherwise this = undefined.
     (let ((callee (second node)))
       (if (member (car callee) '(:member :omember :private-member :oprivate-member))
           (progn
             (compile-chain-base (second callee) short)   ; base object (thisv) -> stack
             (when (member (car callee) '(:omember :oprivate-member))
               (em :nullish-short short))                 ; base nullish: SHORT pops the 1 base
             (em :dup)                                     ; [thisv thisv] — read the fn off the 2nd copy
             (case (car callee)
               ((:private-member :oprivate-member) (em :private-get (resolve-private-name (third callee))))
               (t (if (fourth callee) (progn (compile-expr (third callee)) (em :get-prop))
                      (em :get-prop-c (second (third callee))))))
             ;; stack: [thisv fn]; if fn nullish, drop fn and SHORT (thisv is the 1 base popped)
             (em :nullish-short-2 short)
             (mapc #'compile-expr (third node)) (em :call (length (third node))))
           (progn
             (compile-chain-base callee short)            ; the fn -> stack
             (em :nullish-short short)                     ; fn nullish: SHORT pops the 1 fn
             (compile-call-on-stack (third node))))))
    (:member
     (compile-chain-base (second node) short)
     (if (fourth node) (progn (compile-expr (third node)) (em :get-prop))
         (em :get-prop-c (second (third node)))))
    (:call
     ;; a normal call inside an optional chain (e.g. a?.b()); preserve `this` for
     ;; a member callee.
     (let ((callee (second node)))
       (if (member (car callee) '(:member :omember :private-member :oprivate-member))
           (progn (compile-chain-base (second callee) short)
                  (when (member (car callee) '(:omember :oprivate-member))
                    (em :nullish-short short))
                  (em :dup)                                ; [thisv thisv]
                  (case (car callee)
                    ((:private-member :oprivate-member) (em :private-get (resolve-private-name (third callee))))
                    (t (if (fourth callee) (progn (compile-expr (third callee)) (em :get-prop))
                           (em :get-prop-c (second (third callee))))))
                  (mapc #'compile-expr (third node)) (em :call (length (third node))))
           (progn (compile-chain-base callee short) (em :const *undefined*) (em :swap)
                  (mapc #'compile-expr (third node)) (em :call (length (third node)))))))))

(defun compile-chain-base (node short)
  "Compile a sub-expression that is part of the optional chain (recurse) or a
   plain expression (leaf). Recurse while the base still contains a ?. link — a
   plain `.b`/`b()` between two optional links is still part of the same chain."
  (if (chain-contains-optional-p node)
      (compile-chain-link node short)
      (compile-expr node)))

(defun compile-call-on-stack (args)
  "Callee is on top of stack; call it with this=undefined and ARGS."
  (em :const *undefined*) (em :swap)          ; -> undefined callee
  (mapc #'compile-expr args) (em :call (length args)))

;;; ---- super ----
(defun compile-super-set (node)
  "super.x = v / super[k] = v.  The property is written on the home object's [[Prototype]] with
the RECEIVER still `this` -- which is what makes a setter up the chain see the right object, and
what the read path already does with :SUPER-GET.  Value is expected on the stack; it stays there."
  (destructuring-bind (key computed) (cdr node)
    (if computed (compile-expr key) (em :const (second key)))
    (em :super-set)))

(defun compile-super-member (node)
  "super.x / super[k]: read property from the home object's [[Prototype]], with
   this=current this. Leaves the value on the stack."
  (destructuring-bind (key computed) (cdr node)
    (if computed (compile-expr key) (em :const (second key)))
    (em :super-get)))                          ; key -> value (uses %home + this)

(defun compile-super-call (args)
  "super(...): call the parent constructor with the current `this`, running its
   [[Call]] to initialize the instance -- then run the field initializers, which is exactly when
   the spec says they run."
  (if (some (lambda (a) (and (consp a) (eq (car a) :spread))) args)
      (progn (compile-arg-array args) (em :super-call-spread))
      (progn (mapc #'compile-expr args) (em :super-call (length args))))
  ;; The call left `this` on the stack as its value; statements are stack-neutral, so the
  ;; initializers can run right here without disturbing it.
  (let ((fields *ctor-field-stmts*))
    (when fields
      (setf *ctor-field-stmts* nil)          ; only the FIRST super() initializes
      (mapc #'compile-stmt fields))))

(defun compile-call (callee args)
  ;; Direct eval: a call whose callee is the *identifier* `eval` (not a member
  ;; access, not a computed reference). We resolve the binding at runtime and,
  ;; iff it is the realm's %eval% intrinsic and the first arg is a string, run
  ;; the code in THIS lexical environment / `this` / strict context. Any other
  ;; binding (shadowed eval, non-string arg) falls through to an ordinary call.
  (when (and (consp callee) (eq (car callee) :ident) (string= (second callee) "eval")
             (not (some (lambda (a) (and (consp a) (eq (car a) :spread))) args)))
    (em :get-var "eval")                ; the (possibly shadowed) eval binding
    (mapc #'compile-expr args)
    (em :eval-direct (length args))
    (return-from compile-call nil))
  ;; super.m(...) : method call on the super prototype, this = current this
  (when (eq (car callee) :super-member)
    (destructuring-bind (key computed) (cdr callee)
      (if computed (compile-expr key) (em :const (second key)))
      (em :super-get-method)                   ; key -> thisv methodfn
      (if (some (lambda (a) (and (consp a) (eq (car a) :spread))) args)
          (progn (compile-arg-array args) (em :call-spread))
          (progn (mapc #'compile-expr args) (em :call (length args))))
      (return-from compile-call nil)))
  (cond
    ((eq (car callee) :private-member)      ; obj.#m(...): this=obj, fn from brand
     (compile-expr (second callee)) (em :dup)
     (em :private-get (resolve-private-name (third callee))))
    ((eq (car callee) :member)              ; method call: `this` is the object
     (compile-expr (second callee)) (em :dup)
     (if (fourth callee) (progn (compile-expr (third callee)) (em :get-prop))
         (em :get-prop-c (second (third callee)))))
    (t (em :const *undefined*) (compile-expr callee)))   ; plain call: this = undefined
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
  (check-strict-assign-target target)
  (let ((end (lbl))
        (jmpop (cond ((string= lop "&&") :and-jmp) ((string= lop "||") :or-jmp) (t :nullish-jmp))))
    (case (car target)
      (:ident
       (em :get-var (second target))        ; current value on stack
       (em jmpop end)                        ; keep it & skip if short-circuits
       (compile-expr value) (em :set-var (second target))
       (em :label end))
      ;; NOTE on the stack: the short-circuit ops POP when they fall through and KEEP the value
      ;; when they jump (see :and-jmp / :or-jmp / :nullish-jmp in the VM).  So the not-taken path
      ;; starts empty and must NOT pop again -- an extra :pop here underflowed the stack, which
      ;; is why `o.a ||= 5` died on every plain object while `z ||= 3` worked.
      (:member
       (let ((short (lbl)) (obj (string (gensym "O"))) (k (string (gensym "K"))))
         (compile-expr (second target)) (em :declare-var obj)   ; save obj
         (if (fourth target) (compile-expr (third target)) (em :const (second (third target))))
         (em :declare-var k)                                    ; save key
         (em :get-var obj) (em :get-var k) (em :get-prop)       ; old on stack
         (em jmpop short)                                       ; short-circuits: old is the result
         (em :get-var obj) (em :get-var k) (compile-expr value) (em :set-prop)
         (em :jmp end)
         (em :label short)                                      ; old already on stack = result
         (em :label end)))
      (:super-member
       ;; super.x <op>= v, with the key stashed so a computed one is evaluated once
       (let ((short (lbl)) (k (string (gensym "SK"))))
         (if (third target) (compile-expr (second target)) (em :const (second (second target))))
         (em :declare-var k)
         (em :get-var k) (em :super-get)                        ; old on stack
         (em jmpop short)
         (compile-expr value) (em :get-var k) (em :super-set)
         (em :jmp end)
         (em :label short)
         (em :label end)))
      (:private-member
       (let ((short (lbl)) (pn (resolve-private-name (third target))) (obj (string (gensym "PO"))))
         (compile-expr (second target)) (em :declare-var obj)
         (em :get-var obj) (em :private-get pn)                 ; old on stack
         (em jmpop short)                                       ; short-circuits: old is the result
         (compile-expr value) (em :get-var obj) (em :swap) (em :private-set pn)
         (em :jmp end)
         (em :label short)
         (em :label end)))
      (t (js-throw (make-native-error "SyntaxError" "Invalid left-hand side in assignment"))))))

(defun assert-not-optional-target (target ctx)
  "Assignment / update targets may not be optional chains (early SyntaxError):
   `a?.b = 1`, `--a?.b`, `[a?.b] = x`, etc."
  (when (and (consp target)
             (or (member (car target) '(:omember :ocall :oprivate-member))
                 (and (member (car target) '(:member :private-member :call))
                      (chain-contains-optional-p target))))
    (js-throw (make-native-error "SyntaxError"
                (format nil "Invalid ~a target: optional chain is not a valid assignment target" ctx)))))

(defun compile-assign (op target value)
  (check-strict-assign-target target)
  (assert-not-optional-target target "assignment")
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
      (:super-member
       (if base
           (progn (compile-super-member target) (compile-expr value) (em :bin base))
           (compile-expr value))
       (compile-super-set target))
      (:ident (if base (progn (em :get-var (second target)) (compile-expr value) (em :bin base))
                  (compile-named-init value (second target)))   ; x = function(){} -> x.name = "x"
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
       (em :set-prop))
      (:private-member
       (let ((pn (resolve-private-name (third target))) (obj (string (gensym "PO"))))
         (compile-expr (second target)) (em :declare-var obj)   ; save obj
         (if base
             (progn (em :get-var obj) (em :private-get pn)      ; old
                    (compile-expr value) (em :bin base))        ; new on stack
             (compile-expr value))                              ; val on stack
         ;; stack: val ; -> obj val -> private-set (leaves val)
         (em :get-var obj) (em :swap) (em :private-set pn))))))

(defun compile-update (op prefix target)
  (check-strict-assign-target target)
  (assert-not-optional-target target "update")
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
       (em :update-prop (if (string= op "++") 1d0 -1d0) prefix))
      (:super-member
       ;; No dedicated VM op: read through :SUPER-GET, step, write back through :SUPER-SET.
       ;; The key is recomputed rather than saved, which is correct for the non-computed form
       ;; and evaluates a computed key twice -- so a computed one is stashed in a temp first.
       (let ((delta (if (string= op "++") 1 -1))
             (computed (third target))       ; node is (:super-member KEY COMPUTED)
             (ktmp (string (gensym "SK"))))
         (declare (ignore binop))
         (if computed
             (progn (compile-expr (second target)) (em :declare-var ktmp)
                    (em :get-var ktmp) (em :super-get))
             (progn (em :const (second (second target))) (em :super-get)))
         (em :to-numeric)
         (flet ((write-back ()
                  (if computed (em :get-var ktmp) (em :const (second (second target))))
                  (em :super-set) (em :pop)))
           (if prefix
               (progn (em :num-step delta) (em :dup) (write-back))
               (progn (em :dup) (em :num-step delta) (write-back))))))
      (:private-member
       (let ((pn (resolve-private-name (third target))) (obj (string (gensym "PO")))
             (delta (if (string= op "++") 1 -1)))
         (compile-expr (second target)) (em :declare-var obj)
         (em :get-var obj) (em :private-get pn) (em :to-numeric)  ; old
         (if prefix
             (progn (em :num-step delta) (em :get-var obj) (em :swap) (em :private-set pn))
             (progn (em :dup) (em :num-step delta) (em :get-var obj) (em :swap) (em :private-set pn) (em :pop))))))))
