;;;; vm.lisp — the stack VM, environments, operator semantics, and the
;;;; function/closure machinery. JS functions and host (CL-backed) functions
;;;; both present as objects with [[Call]] — the seam weft calls across.
(in-package #:shuttle)

(defstruct (realm (:constructor %make-realm))
  object-proto function-proto array-proto
  string-proto number-proto boolean-proto symbol-proto
  symbol-registry                       ; string -> js-symbol (Symbol.for/keyFor)
  intrinsics                            ; plist: keyword -> js object (constructors etc.)
  global global-env)
(defvar *current-realm*)
(defun %obj-proto () (realm-object-proto *current-realm*))
(defun %fn-proto () (realm-function-proto *current-realm*))
(defun %arr-proto () (realm-array-proto *current-realm*))
(defun %intrinsic (key) (getf (realm-intrinsics *current-realm*) key))

;;; ---- ToObject: box a primitive into its wrapper object ----
(defun box-primitive (v)
  (let ((r *current-realm*))
    (cond
      ((stringp v)
       (let ((o (make-object :proto (realm-string-proto r) :class "String")))
         (setf (js-object-primitive o) v)
         ;; String exotic: character indices are own enumerable, non-writable,
         ;; non-configurable data properties.
         (dotimes (i (length v))
           (put o (princ-to-string i) (string (char v i))
                :enumerable t :writable nil :configurable nil))
         (put o "length" (float (length v) 1d0) :enumerable nil :writable nil :configurable nil)
         o))
      ((floatp v)
       (let ((o (make-object :proto (realm-number-proto r) :class "Number")))
         (setf (js-object-primitive o) v) o))
      ((or (eq v *true*) (eq v *false*))
       (let ((o (make-object :proto (realm-boolean-proto r) :class "Boolean")))
         (setf (js-object-primitive o) v) o))
      ((js-symbol-p v)
       (let ((o (make-object :proto (realm-symbol-proto r) :class "Symbol")))
         (setf (js-object-primitive o) v) o))
      ((js-bigint-p v)
       (let ((o (make-object :proto (or (getf (realm-intrinsics r) :bigint-proto) (%obj-proto))
                             :class "BigInt")))
         (setf (js-object-primitive o) v) o))
      (t (js-throw "Cannot box value")))))

;;; ---- environments ----
;;; A binding value of the TDZ sentinel means "declared but not yet initialized"
;;; (let/const temporal dead zone). CONSTS holds names that may not be reassigned.
(defvar *tdz* '#:tdz)                    ; unique uninitialized marker
(defvar *current-module* nil)            ; set in module-runtime.lisp; see :dynamic-import

;;; ---- indirect bindings: what makes an imported name LIVE ---------------------------------
;;;
;;; `import { n } from './m.js'` does not copy n.  The importer's environment holds a pointer to
;;; the exporter's binding, and ENV-GET dereferences it on every read -- so a reassignment over
;;; there is visible over here, which is the whole difference between a module and a copy.
;;; DEREF-INDIRECT lives in module-runtime.lisp; this is only the shape and the test.
;;;
;;; DEFSTRUCT rather than DEFCLASS because this sits on the variable-access path: every ENV-GET in
;;; the system now type-tests the value it just fetched, and that test has to be cheap.

(defstruct (indirect-binding (:conc-name ib-))
  module        ; the SOURCE-TEXT-MODULE that owns the real binding
  name)         ; its name over there, which need not be the name over here

(defparameter *indirect-depth-limit* 64
  "A re-export chain longer than this is a cycle the resolver failed to catch; refuse rather than
recurse forever.")


(defvar *empty-completion* '#:empty)     ; the [[value]]:empty completion sentinel (eval completion-value tracking)
;; global-obj: when non-nil, this env is THE global Environment Record. Its VARS
;; hash-table is the *declarative* record (holds only let/const/class + built-in
;; declarative bindings); var/function bindings live as own properties of the
;; global object (globalThis) so `var x` and `globalThis.x` alias, per spec
;; (8.1.1.4 Global Environment Records).
;; var-names: the global env's [[VarNames]] — names introduced by global `var`/
;; function declarations (distinct from arbitrary own properties of globalThis).
;; Used by GlobalDeclarationInstantiation's HasVarDeclaration / HasRestrictedGlobalProperty.
(defstruct env vars parent consts with-obj block global-obj nfe module
  (var-names (make-hash-table :test 'equal)))
(defun new-env (parent) (make-env :vars (make-hash-table :test 'equal) :parent parent))
(defun new-global-env (obj) (make-env :vars (make-hash-table :test 'equal) :parent nil :global-obj obj))
;; --- global-object var-binding helpers (spec CreateGlobalVarBinding etc.) ---
(defun global-var-defined-p (obj name)
  "Does the global object have an own property NAME (a global var/fn binding, or a
   host-defined global property)?"
  (and (js-object-p obj) (js-get-own-property obj name) t))
(defun create-global-var-binding (obj name val &optional (overwrite t))
  "Define/set NAME as an own property of the global object. New bindings are
   configurable:false (global var/fn semantics); if the property already exists we
   only overwrite its value (var re-decl / fn re-decl over a var)."
  (let ((d (js-get-own-property obj name)))
    (cond ((null d)
           (put obj name val :enumerable t :writable t :configurable nil))
          (overwrite
           (js-set obj name val obj)))
    val))
(defun new-block-env (parent) (make-env :vars (make-hash-table :test 'equal) :parent parent :block t))
(defun env-var-scope-has (env name)
  "Is NAME already bound in the nearest var scope (skipping block envs, stopping at
   the first non-block env — the function/global scope)? Used by Annex B B.3.3 to
   avoid clobbering an existing param/var when creating a block-fn's var binding."
  (loop for e = env then (env-parent e) while e
        do (when (nth-value 1 (gethash name (env-vars e))) (return-from env-var-scope-has t))
           (unless (env-block e)
             ;; the var scope is the global environment: its var bindings are
             ;; own properties of the global object, not the declarative record.
             (when (env-global-obj e)
               (return-from env-var-scope-has (global-var-defined-p (env-global-obj e) name)))
             (return-from env-var-scope-has nil)))
  nil)
(defun env-var-set (env name val)
  "Assign an existing var-scoped binding of NAME, skipping block-scoped lexical
   envs (Annex B B.3.3: the block function's var binding lives in the nearest
   function/global scope, not the shadowing block lexical)."
  (loop for e = env then (env-parent e) while e
        do (unless (env-block e)
             (when (nth-value 1 (gethash name (env-vars e)))
               (setf (gethash name (env-vars e)) val) (return-from env-var-set val))
             (when (and (env-global-obj e) (global-var-defined-p (env-global-obj e) name))
               (js-set (env-global-obj e) name val (env-global-obj e))
               (return-from env-var-set val))))
  ;; no var binding found (shouldn't happen if pre-declared) — set on root
  (let ((root (env-root env)))
    (if (env-global-obj root)
        (js-set (env-global-obj root) name val (env-global-obj root))
        (setf (gethash name (env-vars root)) val)))
  val)
(defun new-with-env (parent obj) (make-env :vars (make-hash-table :test 'equal) :parent parent :with-obj obj))
(defun env-root (e) (loop while (env-parent e) do (setf e (env-parent e))) e)
(defun with-binds-p (obj name)
  "Does the `with` object OBJ provide a binding for NAME? (HasProperty, minus any
   name listed truthy in @@unscopables.)"
  (and (js-object-p obj)
       (js-truthy* (js-has obj name))
       (let* ((usym (well-known-symbol "unscopables"))
              (unsc (and usym (js-get obj usym))))
         (not (and (js-object-p unsc) (js-truthy (js-get unsc name)))))))
(defun env-get (env name)
  "Return (values VALUE BOUND-P). BOUND-P nil means the name is not declared."
  (loop for e = env then (env-parent e) while e
        do (when (and (env-with-obj e) (with-binds-p (env-with-obj e) name))
             (return-from env-get (values (js-get (env-with-obj e) name) t)))
           ;; declarative record (let/const/class + built-in declarative bindings)
           (multiple-value-bind (v p) (gethash name (env-vars e))
             (when p (return-from env-get
                       (values (if (indirect-binding-p v) (deref-indirect v 0) v) t))))
           ;; global env: fall back to the global object (var/fn + host globals)
           (when (and (env-global-obj e) (global-var-defined-p (env-global-obj e) name))
             (return-from env-get (values (js-get (env-global-obj e) name) t))))
  (values *undefined* nil))
(defun env-get-checked (env name)
  "Read a binding, throwing ReferenceError if not declared, or if still in TDZ."
  (multiple-value-bind (v p) (env-get env name)
    ;; lazily provide our minimal Promise global on first reference (a richer
    ;; builtins/promise.lisp would define it eagerly and win over this).
    (when (and (not p) (string= name "Promise") (boundp '*current-realm*) *current-realm*)
      (ensure-promise-global)
      (multiple-value-setq (v p) (env-get env name)))
    (cond ((not p) (js-throw (make-native-error "ReferenceError" (format nil "~a is not defined" name))))
          ((eq v *tdz*) (js-throw (make-native-error "ReferenceError"
                          (format nil "Cannot access '~a' before initialization" name))))
          (t v))))
(defun env-typeof (env name)
  (multiple-value-bind (v p) (env-get env name)
    (when (and (not p) (string= name "Promise") (boundp '*current-realm*) *current-realm*)
      (ensure-promise-global)
      (multiple-value-setq (v p) (env-get env name)))
    (cond ((not p) "undefined")
          ((eq v *tdz*) (js-throw (make-native-error "ReferenceError"
                          (format nil "Cannot access '~a' before initialization" name))))
          (t (js-typeof v)))))
(defun env-set (env name val &optional strict)
  (loop for e = env then (env-parent e) while e
        do (when (and (env-with-obj e) (with-binds-p (env-with-obj e) name))
             (js-set (env-with-obj e) name val) (return-from env-set val))
           (when (nth-value 1 (gethash name (env-vars e)))
             ;; An imported binding is immutable in the importing module: the exporter owns it.
             (when (indirect-binding-p (gethash name (env-vars e)))
               (js-throw (make-native-error
                          "TypeError" (format nil "Assignment to constant variable."))))
             ;; Named-function-expression self-binding: an immutable binding. Strict
             ;; assignment -> TypeError; sloppy -> silent no-op (per SetMutableBinding).
             (when (and (env-nfe e) (member name (env-nfe e) :test #'string=))
               (when strict
                 (js-throw (make-native-error "TypeError"
                             (format nil "Cannot assign to read only property '~a'" name))))
               (return-from env-set val))
             (when (and (env-consts e) (member name (env-consts e) :test #'string=))
               (js-throw (make-native-error "TypeError" (format nil "Assignment to constant variable."))))
             (setf (gethash name (env-vars e)) val) (return-from env-set val))
           ;; global env: an own property of the global object is a resolvable binding
           (when (and (env-global-obj e) (global-var-defined-p (env-global-obj e) name))
             (let ((ok (js-set (env-global-obj e) name val (env-global-obj e))))
               (when (and strict (not (js-truthy* ok)))       ; strict: failed [[Set]] -> TypeError
                 (js-throw (make-native-error "TypeError"
                             (format nil "Cannot assign to read-only property '~a' of the global object" name)))))
             (return-from env-set val)))
  ;; unresolvable reference: strict -> ReferenceError; sloppy -> create an implicit global
  (when strict
    (js-throw (make-native-error "ReferenceError" (format nil "~a is not defined" name))))
  (let ((root (env-root env)))                                          ; sloppy implicit global
    (if (env-global-obj root)
        (js-set (env-global-obj root) name val (env-global-obj root))   ; -> writable/enumerable/configurable global property
        (setf (gethash name (env-vars root)) val)))
  val)
(defun env-declare (env name val)
  ;; On the global environment, a var/function binding that already exists as an
  ;; own property of the global object (pre-created by GlobalDeclarationInstantiation,
  ;; or a host global) is updated there — so function-declaration values and var
  ;; re-decls flow onto globalThis. Otherwise (compiler temps, block/fn scopes) the
  ;; binding lives in the declarative record.
  (if (and (env-global-obj env) (global-var-defined-p (env-global-obj env) name))
      (js-set (env-global-obj env) name val (env-global-obj env))
      (setf (gethash name (env-vars env)) val)))
(defun env-declare-const (env name val) (setf (gethash name (env-vars env)) val)
  (pushnew name (env-consts env) :test #'string=))
;; Lexical (let/const/class/TDZ) bindings ALWAYS live in the declarative record,
;; even at global scope where they shadow (but don't touch) a same-named global
;; object property. env-declare is only for var/function bindings.
(defun env-declare-lexical (env name val) (setf (gethash name (env-vars env)) val))

;;; ---- GlobalDeclarationInstantiation (ECMA-262 §16.1.7) ----
;;; Find the global environment record on the env chain (env-root, if it's global).
(defun global-env-of (env)
  "The global environment reachable from ENV -- or NIL if a MODULE environment is in the way.

A module's outer environment IS the global one, so an unguarded walk to the root finds it and
GlobalDeclarationInstantiation then puts the module's `var`s and function declarations onto
globalThis.  Modules do not do that: their var scope is their own, which is most of what makes a
module not a script."
  (loop for e = env then (env-parent e) while e
        do (when (env-module e) (return nil))
           (when (env-global-obj e) (return e))))
(defun genv-has-lexical (genv name)
  "HasLexicalDeclaration: NAME in the declarative record."
  (nth-value 1 (gethash name (env-vars genv))))
(defun genv-has-var (genv name)
  "HasVarDeclaration: NAME is in [[VarNames]] (a prior global var/fn decl)."
  (nth-value 1 (gethash name (env-var-names genv))))
(defun genv-restricted-global-p (genv name)
  "HasRestrictedGlobalProperty: an existing own property of the global object that
   is non-configurable (a `var`/fn already put it there configurable:false, or the
   host defined it non-configurable — either way a `let` collides)."
  (let ((d (js-get-own-property (env-global-obj genv) name)))
    (and d (not (prop-configurable d)))))
(defun genv-can-declare-global-var (genv name)
  (let ((obj (env-global-obj genv)))
    (or (global-var-defined-p obj name) (js-extensible-p obj))))
(defun genv-can-declare-global-function (genv name)
  (let* ((obj (env-global-obj genv)) (d (js-get-own-property obj name)))
    (cond ((null d) (js-extensible-p obj))
          ((prop-configurable d) t)
          ;; existing writable+enumerable data property is redefinable
          ((and (not (prop-accessor d)) (prop-writable d) (prop-enumerable d)) t)
          (t nil))))
(defun create-global-function-binding (genv name val)
  "CreateGlobalFunctionBinding: define NAME as a data property of the global object.
   If it already exists and is configurable, redefine fully (writable/enumerable,
   configurable:false); else just set its value."
  (let* ((obj (env-global-obj genv)) (d (js-get-own-property obj name)))
    (if (or (null d) (prop-configurable d))
        (ordinary-define-own-property obj name
          (list :value val :writable t :enumerable t :configurable nil))
        (js-set obj name val obj))
    (setf (gethash name (env-var-names genv)) t)
    val))
(defun env-var-scope (env)
  "The nearest var scope: skip block envs, stop at the first non-block env (a
   function or the global environment record)."
  (loop for e = env then (env-parent e) while e
        do (unless (env-block e) (return-from env-var-scope e)))
  (env-root env))
(defun eval-var-decl (env name)
  "EvalDeclarationInstantiation for one var/fn NAME. When the eval's variable
   environment is the GLOBAL environment the binding becomes a *deletable*
   (configurable:true) own property of the global object, NOT recorded in
   [[VarNames]] (so a later global `let` isn't blocked). Otherwise (eval sharing a
   function's var scope) it's an ordinary absent-safe var binding in that scope.
   Never clobbers an existing binding."
  (let ((vscope (env-var-scope env)))
    (if (env-global-obj vscope)
        (let ((obj (env-global-obj vscope)))
          (unless (global-var-defined-p obj name)
            (put obj name *undefined* :enumerable t :writable t :configurable t)))
        (unless (env-var-scope-has env name)
          (env-declare vscope name *undefined*)))))
(defun global-declaration-instantiation (env decls)
  "Run the spec early checks + create global var/function bindings on the global
   object. DECLS = (var-names function-names lexical-names). SyntaxError on a
   lex/var collision or restricted-global collision; TypeError if a name is not
   definable (non-extensible global object)."
  (destructuring-bind (var-names fn-names lex-names) decls
    (let ((genv (global-env-of env)))
      (unless genv (return-from global-declaration-instantiation))   ; direct-eval etc. share a non-global env
      ;; 1. lexical-declaration early errors (SyntaxError) — run BEFORE any binding
      ;;    is created, so a failure leaves the global env untouched.
      (dolist (n lex-names)
        (when (or (genv-has-var genv n) (genv-has-lexical genv n) (genv-restricted-global-p genv n))
          (js-throw (make-native-error "SyntaxError"
                      (format nil "Identifier '~a' has already been declared" n)))))
      ;; 2. var/function-declaration collides with a lexical declaration -> SyntaxError
      (dolist (n (union var-names fn-names :test #'string=))
        (when (genv-has-lexical genv n)
          (js-throw (make-native-error "SyntaxError"
                      (format nil "Identifier '~a' has already been declared" n)))))
      ;; 3. CanDeclareGlobalFunction / CanDeclareGlobalVar -> TypeError if not definable
      (dolist (n fn-names)
        (unless (genv-can-declare-global-function genv n)
          (js-throw (make-native-error "TypeError"
                      (format nil "Cannot declare global function '~a'" n)))))
      (dolist (n var-names)
        (unless (member n fn-names :test #'string=)
          (unless (genv-can-declare-global-var genv n)
            (js-throw (make-native-error "TypeError"
                        (format nil "Cannot declare global variable '~a'" n))))))
      ;; 4. create global VAR bindings (undefined). Function-declaration bindings are
      ;;    created/assigned by the body's :func -> :declare-var (env-declare finds the
      ;;    pre-created property, or create-global-function-binding via the fn set).
      ;;    Pre-create fn property slots too so :declare-var writes onto globalThis.
      (dolist (n fn-names)
        (create-global-function-binding genv n *undefined*))
      (dolist (n var-names)
        (unless (member n fn-names :test #'string=)
          (unless (global-var-defined-p (env-global-obj genv) n)
            (create-global-var-binding (env-global-obj genv) n *undefined*))
          (setf (gethash n (env-var-names genv)) t))))))

;;; ---- object builders ----
(defun make-array-object (elems)
  (let ((o (make-object :proto (%arr-proto) :class "Array")))
    (loop for e in elems for i from 0 do (put o (princ-to-string i) e))
    ;; Array "length" is writable but non-enumerable and non-configurable.
    (put o "length" (float (length elems) 1d0)
         :enumerable nil :writable t :configurable nil)
    o))
(defun %frozen-string-array (strings)
  "A frozen array of STRINGS: each element non-writable/non-configurable, length
   non-writable/non-configurable, and the array itself non-extensible."
  (let ((o (make-object :proto (%arr-proto) :class "Array")))
    (loop for s in strings for i from 0
          do (put o (princ-to-string i) (or s *undefined*) :writable nil :configurable nil :enumerable t))
    (put o "length" (float (length strings) 1d0) :enumerable nil :writable nil :configurable nil)
    (setf (js-object-extensible o) nil)
    o))

(defun get-template-object (spec)
  "GetTemplateObject: the frozen strings array (with frozen .raw) for a tagged
   template call site. Cached per site-key on the current realm so the SAME site
   yields the SAME object across evaluations (SPEC 13.2.8.4)."
  (destructuring-bind (&key site cooked raw) spec
    (let* ((key (getf site :key))
           (cache (or (getf (realm-intrinsics *current-realm*) :template-cache)
                      (setf (getf (realm-intrinsics *current-realm*) :template-cache)
                            (make-hash-table :test 'eq)))))
      (or (gethash key cache)
          (let ((obj (%frozen-string-array cooked))
                (rawarr (%frozen-string-array raw)))
            (put obj "raw" rawarr :writable nil :configurable nil :enumerable nil)
            (setf (js-object-extensible obj) nil)
            (setf (gethash key cache) obj))))))

(defun make-plain-object (pairs)
  (let ((o (make-object :proto (%obj-proto))))
    (loop for (k . v) in pairs do (put o (if (stringp k) k (to-string k)) v)) o))

(defun array-object-to-list (arr)
  "Read a dense array object's indexed elements 0..length-1 into a CL list."
  (let ((n (truncate (to-number (js-get arr "length")))))
    (loop for i from 0 below n collect (js-get arr (princ-to-string i)))))

(defun object-rest-copy (src taken)
  "Copy own enumerable string keys of SRC into a fresh object, excluding TAKEN."
  (let ((o (make-object :proto (%obj-proto))) (src (to-object src)))
    (when (js-object-p src)
      (dolist (k (js-own-keys src))
        (when (and (stringp k) (not (member k taken :test #'string=)))
          (let ((d (js-get-own-property src k)))
            (when (and d (prop-enumerable d))
              (put o k (js-get src k)))))))
    o))

(defun object-rest-copy-keys (src taken)
  "CopyDataProperties: copy own enumerable keys (string AND symbol) of SRC into a
   fresh object, excluding those in TAKEN (each already a property key: string or
   symbol). TAKEN entries that are numbers/etc. are coerced to property keys."
  (let ((o (make-object :proto (%obj-proto))) (src (to-object src))
        (excluded (mapcar #'prop-key taken)))
    (when (js-object-p src)
      (dolist (k (js-own-keys src))
        (unless (member k excluded :test (lambda (a b)
                                           (if (and (js-symbol-p a) (js-symbol-p b)) (eq a b)
                                               (and (stringp a) (stringp b) (string= a b)))))
          (let ((d (js-get-own-property src k)))
            (when (and d (prop-enumerable d))
              (put o k (js-get src k)))))))
    o))

(defun for-in-key-array (o)
  "Array of enumerable string keys of O and its prototype chain (deduped)."
  (if (js-object-p o)
      (let ((seen (make-hash-table :test 'equal)) (out '()))
        (loop for cur = o then (js-object-proto cur)
              while (js-object-p cur)
              do (dolist (k (js-own-keys cur))
                   (when (and (stringp k) (not (gethash k seen)))
                     (setf (gethash k seen) t)
                     (let ((d (js-get-own-property cur k)))
                       (when (and d (prop-enumerable d)) (push k out))))))
        (make-array-object (nreverse out)))
      (make-array-object '())))

;;; ---- iterator protocol (for-of, spread, Array.from) ----
(defvar *symbol-iterator* nil)          ; @@iterator well-known symbol (set at realm build)
(defun get-iterator (obj)
  (let ((o (to-object obj)))
    (let ((itf (and *symbol-iterator* (js-get o *symbol-iterator*))))
      (unless (js-callable-p itf)
        (js-throw (make-native-error "TypeError" (format nil "~a is not iterable" (ignore-errors (to-string obj))))))
      (let ((it (js-call itf o '())))
        (unless (js-object-p it) (js-throw (make-native-error "TypeError" "iterator is not an object")))
        it))))
(defun iterator-step (it)
  "Call it.next(); return the result record ({value,done})."
  (let ((next (js-get it "next")))
    (unless (js-callable-p next) (js-throw (make-native-error "TypeError" "iterator.next is not a function")))
    (let ((r (js-call next it '())))
      (unless (js-object-p r) (js-throw (make-native-error "TypeError" "iterator result is not an object")))
      r)))
(defun iterator-close (it)
  "IteratorClose: call it.return() if present, ignoring a thrown result (we are
   already unwinding an abrupt completion)."
  (when (js-object-p it)
    (let ((ret (ignore-errors (js-get it "return"))))
      (when (js-callable-p ret)
        (ignore-errors (js-call ret it '()))))))
(defun iterator-close-normal (it)
  "IteratorClose on a NORMAL completion: call it.return(); if it is not callable,
   fine; if it returns a non-object, TypeError; a thrown return() propagates."
  (when (js-object-p it)
    (let ((ret (js-get it "return")))
      (when (and ret (not (eq ret *undefined*)) (not (eq ret *null*)))
        (unless (js-callable-p ret)
          (js-throw (make-native-error "TypeError" "iterator return is not a function")))
        (let ((r (js-call ret it '())))
          (unless (js-object-p r)
            (js-throw (make-native-error "TypeError" "iterator return result is not an object"))))))))

(defun make-arguments-object (args)
  "A minimal (unmapped) arguments object: indexed elements + length + @@iterator."
  (let ((o (make-object :proto (%obj-proto) :class "Arguments")))
    (loop for a in args for i from 0 do (put o (princ-to-string i) a))
    (put o "length" (float (length args) 1d0) :enumerable nil)
    (when *symbol-iterator*
      (let ((av (realm-array-proto *current-realm*)))
        (put o *symbol-iterator* (js-get av *symbol-iterator*) :enumerable nil)))
    o))

(defun fn-home (fn) (getf (js-object-internal fn) :home))
(defun (setf fn-home) (v fn) (setf (getf (js-object-internal fn) :home) v))
(defun fn-super-ctor (fn) (getf (js-object-internal fn) :super-ctor))
(defun (setf fn-super-ctor) (v fn) (setf (getf (js-object-internal fn) :super-ctor) v))

(defun ordinary-bind-this (this)
  "OrdinaryCallBindThis for a NON-strict ordinary (:normal this-mode) function:
   undefined/null -> the realm global object; a primitive -> ToObject (boxed);
   an object passes through. (We don't track strict mode; sloppy is the default,
   matching the majority of non-strict test262 tests.)"
  (cond ((js-null-or-undef this)
         (if (boundp '*current-realm*) (realm-global (symbol-value '*current-realm*)) this))
        ((js-object-p this) this)
        (t (to-object this))))          ; box a primitive receiver

(defun make-js-function (code env &key kind lexical-this)
  "KIND: nil = ordinary function; :method = has [[HomeObject]] (super),
   :generator = a generator function; :class-base / :class-derived = a class ctor.
   LEXICAL-THIS: for an arrow (:lexical this-mode), the `this` captured at the
   arrow's DEFINITION site — the arrow ignores its caller's `this` and uses it."
  (let ((fn (make-object :proto (%fn-proto) :class "Function"))
        ;; arrows (:lexical) have no [[NewTarget]] of their own — new.target inside an
        ;; arrow resolves to the enclosing function's, captured here at definition.
        (lexical-nt (and (eq (code-this-mode code) :lexical) *new-target*)))
    ;; THE ACTIVE MODULE, captured at DEFINITION.  `import()` and `import.meta` inside a function
    ;; must resolve against the module the function was written in -- and by the time an async
    ;; continuation runs, every dynamic binding that knew is long unwound.  So the function
    ;; carries it, which is what the spec means by "the active script or module".
    (when *current-module*
      (setf (getf (js-object-internal fn) :module) *current-module*))
    (put fn "length" (float (fn-declared-length (code-params code)) 1d0) :enumerable nil :writable nil)
    (put fn "name" (or (code-name code) "") :enumerable nil :writable nil :configurable t)
    (setf (js-object-call fn)
          ;; OrdinaryCallBindThis: :normal (ordinary/method) functions substitute
          ;; undefined/null -> globalThis and box a primitive receiver; :lexical
          ;; (arrow) functions use the this captured at their definition site.
          (macrolet ((bind (this) `(case (code-this-mode code)
                                     (:lexical lexical-this)          ; arrow: captured this
                                     (:strict ,this)                  ; strict: no substitution (undefined stays)
                                     (t (ordinary-bind-this ,this))))) ; sloppy: undefined/null -> global, primitive -> boxed
            (case kind
              (:generator (lambda (this args) (make-generator-object code env (bind this) args fn)))
              (:async (lambda (this args)
                        (let ((this (bind this)))
                          (handler-case (make-async-function-object code env this args fn)
                            (shuttle-error (e)
                              ;; a synchronous throw before the first await -> rejected promise
                              (let ((p (make-promise)))
                                (promise-settle p :rejected (shuttle-error-value e)) p))))))
              (:async-generator (lambda (this args) (make-async-generator-object code env (bind this) args fn)))
              (t (lambda (this args)
                   (let ((fenv (new-env env))
                         (*new-target* (if (eq (code-this-mode code) :lexical) lexical-nt *new-target*)))
                     (env-declare fenv "arguments" (make-arguments-object args))
                     (run code fenv (bind this) args fn)))))))
    ;; class constructors: only callable via `new`; the [[Construct]] initializes
    ;; the instance (derived ctors require super() to run the base first).
    (cond
      ((member kind '(:class-base :class-derived))
       ;; the real runner: super() and new both call this to run the ctor body.
       (setf (getf (js-object-internal fn) :ctor-run)
             (lambda (this args) (let ((fenv (new-env env)))
                                   (env-declare fenv "arguments" (make-arguments-object args))
                                   (run code fenv this args fn))))
       (setf (js-object-construct fn)
             (lambda (args new-target)
               (let* ((pp (js-get (or new-target fn) "prototype"))
                      (obj (make-object :proto (if (js-object-p pp) pp (%obj-proto)))))
                 (let ((r (funcall (getf (js-object-internal fn) :ctor-run) obj args)))
                   (if (js-object-p r) r obj)))))
       ;; class ctors are not plain-callable: throw on [[Call]]
       (setf (js-object-call fn)
             (lambda (this args) (declare (ignore this args))
               (js-throw (make-native-error "TypeError"
                          (format nil "Class constructor ~a cannot be invoked without 'new'"
                                  (or (code-name code) "")))))))
      ((member kind '(:async :async-generator)) nil)   ; async fns are not constructable
      ;; arrows and concise/accessor methods are not constructable: `new (()=>{})`
      ;; and `new ({m(){}}.m)` throw TypeError (no [[Construct]] / no .prototype).
      ((not (code-constructable code)) nil)
      (t
       (setf (js-object-construct fn)
             (lambda (args new-target)
               ;; OrdinaryCreateFromConstructor: the new object's [[Prototype]] is
               ;; newTarget.prototype (Reflect.construct's 3rd arg), else fn's.
               (let* ((pp (js-get (or new-target fn) "prototype"))
                      (obj (make-object :proto (if (js-object-p pp) pp (%obj-proto)))))
                 (let ((r (funcall (js-object-call fn) obj args))) (if (js-object-p r) r obj)))))))
    ;; a fresh .prototype so `new` works and methods can be attached.
    ;; async (non-generator) functions and non-constructable fns (arrows/methods) don't get one.
    (unless (or (member kind '(:method :async)) (not (code-constructable code)))
      (let ((proto (make-object :proto (case kind
                                         (:generator (generator-prototype))
                                         (:async-generator (async-generator-prototype))
                                         (t (%obj-proto))))))
        (unless (member kind '(:generator :async-generator)) (put proto "constructor" fn :enumerable nil))
        (put fn "prototype" proto :enumerable nil :configurable nil
             :writable (not (member kind '(:generator :async-generator))))))
    fn))

(defun fn-declared-length (params)
  "The .length of a function: count leading params before the first default/rest."
  (let ((n 0))
    (dolist (p params n)
      (when (and (consp p) (member (car p) '(:default :rest))) (return n))
      (incf n))))

;;; ---- generators (thread-backed coroutines) ----
;;; A generator runs its body on a dedicated worker thread. At each `yield` the
;;; worker blocks on RESUME-SEM and the consumer thread proceeds; `.next(v)` hands
;;; V back and unblocks the worker. This gives true VM-frame suspend/resume without
;;; CPS-transforming the bytecode. Threads are cheap here (short-lived, gated).
(defstruct genstate
  thread
  (to-gen-sem (sb-thread:make-semaphore))     ; consumer -> generator (resume)
  (to-consumer-sem (sb-thread:make-semaphore)) ; generator -> consumer (yielded/done)
  sent                                        ; value passed into .next(v) / throw / return
  mode                                        ; :next :throw :return  (how to resume)
  yielded                                     ; value handed out at a yield
  (done nil)
  (started nil)
  (executing nil)                             ; t while resumed (re-entrant next/return/throw -> TypeError)
  error)                                      ; a shuttle-error to propagate to the consumer

(defvar *current-generator* nil)              ; the genstate the running thread belongs to
(defvar *generators-created* 0)               ; counter to periodically reclaim leaked threads
(defvar *live-generators* '())                ; suspended (non-done) genstates, newest first
(defparameter *max-live-generators* 300)      ; hard cap on concurrent worker threads

(defun terminate-generator (gs)
  "Force an abandoned suspended generator's worker to unwind and exit."
  (unless (genstate-done gs)
    (setf (genstate-done gs) t (genstate-mode gs) :terminate)
    (ignore-errors (sb-thread:signal-semaphore (genstate-to-gen-sem gs)))
    (let ((th (genstate-thread gs)))
      (when (and th (sb-thread:thread-alive-p th))
        (ignore-errors (sb-thread:join-thread th :timeout 1))))))

(defun terminate-all-generators ()
  "Force every live (suspended) generator's worker thread to unwind and exit.
   Called by the test harness between tests so abandoned generators — each
   holding a realm + a 2MB thread stack — can't accumulate into heap exhaustion."
  (when *live-generators*
    (dolist (gs *live-generators*) (ignore-errors (terminate-generator gs)))
    (setf *live-generators* '())))

(defun reap-generators ()
  "Drop finished generators from the registry; if still over the cap, forcibly
   terminate the oldest suspended workers (assumed abandoned by a prior test)."
  (setf *live-generators* (delete-if #'genstate-done *live-generators*))
  (when (> (length *live-generators*) *max-live-generators*)
    ;; oldest are at the tail; terminate down to half the cap
    (let* ((keep (floor *max-live-generators* 2))
           (rev (reverse *live-generators*))
           (kill (nthcdr keep rev)))
      (dolist (gs kill) (terminate-generator gs))
      (setf *live-generators* (delete-if #'genstate-done *live-generators*)))))

(define-condition generator-terminate (error) ())  ; unwinds an abandoned generator's thread

(defun gen-yield (value)
  "Called from inside a generator's worker thread at a `yield`. Hands VALUE to the
   consumer, blocks until resumed, and returns the sent value (or throws)."
  (let ((gs *current-generator*))
    (setf (genstate-yielded gs) value)
    (sb-thread:signal-semaphore (genstate-to-consumer-sem gs))
    (sb-thread:wait-on-semaphore (genstate-to-gen-sem gs))
    (case (genstate-mode gs)
      (:throw  (js-throw (genstate-sent gs)))
      (:return (throw 'generator-return (genstate-sent gs)))
      (:terminate (error 'generator-terminate))    ; abandoned: unwind the worker
      (t (genstate-sent gs)))))

(defvar *generator-proto-cache* nil)   ; alist (realm . %GeneratorPrototype%)
(defun generator-prototype ()
  "The shared %GeneratorPrototype% for the current realm (next/return/throw/@@it)."
  (let ((cell (assoc *current-realm* *generator-proto-cache*)))
    (if cell (cdr cell)
        (let ((gp (make-object :proto (or *iterator-prototype* (%obj-proto)))))
          (flet ((native (name fn) (let ((f (make-object :proto (%fn-proto) :class "Function")))
                                     (setf (js-object-call f) fn)
                                     (put f "name" name :enumerable nil :writable nil)
                                     (put gp name f :enumerable nil))))
            (native "next"   (lambda (this args) (generator-resume this :next (if args (car args) *undefined*))))
            (native "return" (lambda (this args) (generator-resume this :return (if args (car args) *undefined*))))
            (native "throw"  (lambda (this args) (generator-resume this :throw (if args (car args) *undefined*)))))
          (when *symbol-iterator*
            (let ((f (make-object :proto (%fn-proto) :class "Function")))
              (setf (js-object-call f) (lambda (this args) (declare (ignore args)) this))
              (put f "name" "[Symbol.iterator]" :enumerable nil :writable nil)
              (put gp *symbol-iterator* f :enumerable nil)))
          (push (cons *current-realm* gp) *generator-proto-cache*)
          gp))))

(defun instantiate-fn-env (code env this args fn)
  "Build the function environment for a split generator/async CODE and run its
   instantiation stream (param binding + hoisting) SYNCHRONOUSLY in the current
   thread. Returns the prepared environment. Errors here propagate to the CALLER."
  (let ((fenv (new-env env)))
    (env-declare fenv "arguments" (make-arguments-object args))
    (when (code-inst-instrs code)
      (%run (make-code :name (code-name code) :params (code-params code)
                       :instrs (code-inst-instrs code))
            fenv this args fn))
    fenv))

(defun make-generator-object (code env this args fn)
  "Create a generator object whose worker thread will run CODE. The object exposes
   next/return/throw and @@iterator (returns itself)."
  ;; keep leaked (abandoned, suspended) generator threads bounded (see reap).
  (incf *generators-created*)
  (when (zerop (mod *generators-created* 64)) (reap-generators))
  ;; FunctionDeclarationInstantiation runs SYNCHRONOUSLY here (before the generator
  ;; object exists): a throw in a default param / destructuring surfaces to the caller.
  (let ((fenv (instantiate-fn-env code env this args fn)))
   (let* ((gs (make-genstate))
         (gproto (let ((pp (js-get fn "prototype"))) (if (js-object-p pp) pp (generator-prototype))))
         (gobj (make-object :proto gproto :class "Generator"))
         (realm *current-realm*))
    (setf (getf (js-object-internal gobj) :genstate) gs)
    ;; the worker: waits for the first resume, then runs the body.
    (setf (genstate-thread gs)
          (sb-thread:make-thread
           (lambda ()
             (block worker
               (let ((*current-realm* realm) (*current-generator* gs)
                     (*steps* 0) (*run-depth* 1))
                 (sb-thread:wait-on-semaphore (genstate-to-gen-sem gs))
                 (handler-case
                     (progn
                       (when (eq (genstate-mode gs) :terminate) (return-from worker))
                       (let ((rv (catch 'generator-return
                                   (case (genstate-mode gs)
                                     (:throw (js-throw (genstate-sent gs)))
                                     (:return (genstate-sent gs))
                                     (t (run code fenv this args fn))))))
                         (setf (genstate-yielded gs) rv (genstate-done gs) t)))
                   (generator-terminate () (return-from worker))   ; abandoned: silent exit
                   (shuttle-error (e) (setf (genstate-error gs) e (genstate-done gs) t))
                   ;; ANY other serious condition (timeout, stack, host bug): mark done
                   ;; and surface as a JS error to the consumer — never let it quit the
                   ;; whole process (--disable-debugger would kill everything).
                   (serious-condition (e)
                     (setf (genstate-error gs)
                           (make-condition 'shuttle-error
                                           :value (make-native-error "Error"
                                                    (format nil "generator error: ~a" e)))
                           (genstate-done gs) t)))
                 (sb-thread:signal-semaphore (genstate-to-consumer-sem gs)))))
           :name "shuttle-generator"))
    (push gs *live-generators*)
    gobj)))

(defun generator-resume (gobj mode value)
  "Resume GOBJ's generator with MODE (:next/:throw/:return) and VALUE. Returns a
   result object {value, done}."
  (let ((gs (getf (js-object-internal gobj) :genstate)))
    (unless gs (js-throw (make-native-error "TypeError" "not a generator")))
    (when (genstate-done gs)
      ;; already finished: return/next -> {value: v, done:true}; throw -> throw
      (case mode
        (:throw (js-throw value))
        (:return (return-from generator-resume (iter-result value t)))
        (t (return-from generator-resume (iter-result *undefined* t)))))
    ;; re-entrant resume (e.g. the body calls its own .next/.return/.throw while
    ;; running) -> TypeError, per the "executing" generator state.
    (when (genstate-executing gs)
      (js-throw (make-native-error "TypeError" "Generator is already executing")))
    (setf (genstate-executing gs) t (genstate-mode gs) mode (genstate-sent gs) value)
    (sb-thread:signal-semaphore (genstate-to-gen-sem gs))
    (sb-thread:wait-on-semaphore (genstate-to-consumer-sem gs))
    (setf (genstate-executing gs) nil)
    (when (genstate-error gs)
      (let ((e (genstate-error gs))) (setf (genstate-error gs) nil) (error e)))
    (if (genstate-done gs)
        (iter-result (genstate-yielded gs) t)
        (iter-result (genstate-yielded gs) nil))))

(defun iter-result (value done)
  (let ((o (make-object :proto (%obj-proto))))
    (put o "value" value) (put o "done" (js-bool done)) o))

(defun yield-star-delegate (iterable)
  "yield* ITERABLE: drive the inner iterator, yielding each produced value and
   forwarding .next(sent) to it; return the iterator's final value."
  (let* ((it (get-iterator iterable))
         (next (js-get it "next"))
         (sent *undefined*))
    (loop
      (let ((r (js-call next it (list sent))))
        (unless (js-object-p r) (js-throw (make-native-error "TypeError" "iterator result is not an object")))
        (when (js-truthy (js-get r "done"))
          (return-from yield-star-delegate (js-get r "value")))
        (setf sent (gen-yield (js-get r "value")))))))

;;; ---- microtask queue ----
;;; A FIFO of thunks (CL closures). The top-level eval drains it after the script
;;; runs, so a resolved promise's reactions fire before the test's assertions read
;;; their side effects. There is no real event loop / timers here.
(defvar *symbol-to-string-tag* nil)   ; @@toStringTag (set at realm build if available)
(defvar *symbol-async-iterator* nil)  ; @@asyncIterator
(defvar *microtasks* nil)            ; a queue held as (head . tail) cons cells, or nil
(defvar *microtask-tail* nil)

(defun enqueue-microtask (thunk)
  (let ((cell (cons thunk nil)))
    (if *microtasks*
        (setf (cdr *microtask-tail*) cell *microtask-tail* cell)
        (setf *microtasks* cell *microtask-tail* cell))))

(defun drain-microtasks ()
  "Run queued microtasks to completion (each may enqueue more). Swallows JS
   throws from reactions (unhandled rejections have no observer here)."
  (loop while *microtasks* do
    (let ((thunk (car *microtasks*)))
      (setf *microtasks* (cdr *microtasks*))
      (unless *microtasks* (setf *microtask-tail* nil))
      (handler-case (funcall thunk)
        (shuttle-error () nil)
        (serious-condition () nil)))))

;;; ---- minimal Promise ----
;;; A promise object carries its state in :internal. States: :pending :fulfilled
;;; :rejected. Reactions are (on-fulfill . on-reject) CL-closure pairs queued while
;;; pending and flushed onto the microtask queue on settle.
(defvar *promise-proto-cache* nil)   ; alist (realm . %PromisePrototype%)
(defvar *promise-ctor-cache* nil)    ; alist (realm . Promise constructor)

(defun promisep (o)
  (and (js-object-p o) (member :promise-state (js-object-internal o))))
(defun promise-state (p) (getf (js-object-internal p) :promise-state))
(defun (setf promise-state) (v p) (setf (getf (js-object-internal p) :promise-state) v))
(defun promise-value (p) (getf (js-object-internal p) :promise-value))
(defun (setf promise-value) (v p) (setf (getf (js-object-internal p) :promise-value) v))
(defun promise-reactions (p) (getf (js-object-internal p) :promise-reactions))
(defun (setf promise-reactions) (v p) (setf (getf (js-object-internal p) :promise-reactions) v))
(defun promise-already-handled-p (p) (getf (js-object-internal p) :promise-handled))
(defun (setf promise-already-handled-p) (v p) (setf (getf (js-object-internal p) :promise-handled) v))

(defvar *promise-global-installed* '())   ; realms into which Promise has been installed
(defun ensure-promise-global ()
  "Install the Promise constructor as a global in the current realm (once)."
  (let ((realm *current-realm*))
    (unless (member realm *promise-global-installed*)
      (push realm *promise-global-installed*)
      (unless (nth-value 1 (env-get (realm-global-env realm) "Promise"))
        (install-promise-global realm)))))

(defun native-fn (fn &optional (len 1) (name ""))
  "A bare callable JS object wrapping CL FN (this args) -> value."
  (let ((o (make-object :proto (%fn-proto) :class "Function")))
    (setf (js-object-call o) fn)
    (put o "length" (float len 1d0) :enumerable nil :writable nil :configurable t)
    (put o "name" name :enumerable nil :writable nil :configurable t)
    o))

;;; ---- OrdinaryCreateFromConstructor helper ----
(defun get-proto-from-constructor (new-target default-proto)
  "GetPrototypeFromConstructor(newTarget, defaultProto): use newTarget.prototype if
   it is an object, else DEFAULT-PROTO."
  (if (js-object-p new-target)
      (let ((pp (js-get new-target "prototype")))
        (if (js-object-p pp) pp default-proto))
      default-proto))

(defun make-promise (&optional (proto (promise-prototype)))
  "Allocate a pending promise object whose [[Prototype]] is PROTO."
  (ensure-promise-global)
  (let ((p (make-object :proto proto :class "Promise")))
    (setf (js-object-internal p)
          (list* :promise-state :pending :promise-value *undefined* :promise-reactions '()
                 (js-object-internal p)))
    p))

;;; ---- PromiseCapability records ----
;;; A capability is (promise resolve reject) — resolve/reject are JS callables.
(defstruct pcap promise resolve reject)

(defun new-promise-capability (c)
  "NewPromiseCapability(C): C must be a constructor. Runs C with a
   GetCapabilitiesExecutor and captures the resolve/reject it hands back."
  (unless (and (js-object-p c) (js-object-construct c))
    (js-throw (make-native-error "TypeError" "Promise capability requires a constructor")))
  (let ((resolve *undefined*) (reject *undefined*))
    (let* ((executor
             (native-fn
              (lambda (this args) (declare (ignore this))
                ;; GetCapabilitiesExecutor: resolve/reject each set exactly once.
                (unless (js-undefined-p resolve)
                  (js-throw (make-native-error "TypeError" "capability resolve already set")))
                (unless (js-undefined-p reject)
                  (js-throw (make-native-error "TypeError" "capability reject already set")))
                (setf resolve (if args (car args) *undefined*))
                (setf reject (if (cdr args) (cadr args) *undefined*))
                *undefined*)
              2))
           (promise (js-construct c (list executor) c)))
      (unless (js-callable-p resolve)
        (js-throw (make-native-error "TypeError" "Promise resolve is not callable")))
      (unless (js-callable-p reject)
        (js-throw (make-native-error "TypeError" "Promise reject is not callable")))
      (make-pcap :promise promise :resolve resolve :reject reject))))

(defun cap-resolve (cap value)
  (js-call (pcap-resolve cap) *undefined* (list value)))
(defun cap-reject (cap reason)
  (js-call (pcap-reject cap) *undefined* (list reason)))

(defun promise-fulfill (p value)
  "FulfillPromise: transition pending P to fulfilled and schedule fulfill reactions."
  (let ((reactions (nreverse (promise-reactions p))))
    (setf (promise-state p) :fulfilled (promise-value p) value (promise-reactions p) '())
    (dolist (r reactions) (schedule-reaction p r))))

(defun promise-reject-internal (p reason)
  "RejectPromise: transition pending P to rejected and schedule reject reactions."
  (let ((reactions (nreverse (promise-reactions p))))
    (setf (promise-state p) :rejected (promise-value p) reason (promise-reactions p) '())
    (dolist (r reactions) (schedule-reaction p r))))

(defun promise-settle (p state value)
  "Legacy shim used by the async driver. Transition pending P to STATE/VALUE."
  (when (eq (promise-state p) :pending)
    (if (eq state :fulfilled) (promise-fulfill p value) (promise-reject-internal p value))))

;;; ---- resolving functions (spec CreateResolvingFunctions) ----
(defun make-resolving-functions (p)
  "Return (values resolveFn rejectFn) — the pair passed to a Promise executor. Both
   share an alreadyResolved guard; resolve adopts thenables via a job."
  (let ((already nil))
    (values
     (native-fn
      (lambda (this args) (declare (ignore this))
        (let ((resolution (if args (car args) *undefined*)))
          (unless already
            (setf already t)
            (cond
              ((eq resolution p)
               (when (eq (promise-state p) :pending)
                 (promise-reject-internal p (make-native-error "TypeError" "Chaining cycle detected"))))
              ((not (js-object-p resolution))
               (when (eq (promise-state p) :pending) (promise-fulfill p resolution)))
              (t
               (block resolve-get
                 (let ((then (handler-case (js-get resolution "then")
                               (shuttle-error (e)
                                 (when (eq (promise-state p) :pending)
                                   (promise-reject-internal p (shuttle-error-value e)))
                                 (return-from resolve-get)))))
                   (if (js-callable-p then)
                       (enqueue-microtask (make-then-job resolution then p))
                       (when (eq (promise-state p) :pending) (promise-fulfill p resolution)))))))))
        *undefined*)
      1)
     (native-fn
      (lambda (this args) (declare (ignore this))
        (unless already
          (setf already t)
          (when (eq (promise-state p) :pending)
            (promise-reject-internal p (if args (car args) *undefined*))))
        *undefined*)
      1))))

(defun make-then-job (thenable then p)
  "PromiseResolveThenableJob: a microtask that calls thenable.then with fresh
   resolving functions for P."
  (lambda ()
    (multiple-value-bind (res rej) (make-resolving-functions p)
      (handler-case (js-call then thenable (list res rej))
        (shuttle-error (e) (js-call rej *undefined* (list (shuttle-error-value e))))))))

(defun resolve-promise (p value)
  "Internal resolve used by the async driver / Promise.resolve fast path."
  (multiple-value-bind (res rej) (make-resolving-functions p)
    (declare (ignore rej))
    (js-call res *undefined* (list value))))

;;; ---- reactions ----
;;; A reaction is (kind . handler): KIND is :fulfill or :reject, HANDLER is a JS
;;; callable or NIL (default passthrough); CAP is the target capability. Stored as
;;; a list (cap fulfill-handler reject-handler) where handlers may be NIL.
(defun schedule-reaction (p reaction)
  "Queue REACTION against P's settled state on the microtask queue."
  (destructuring-bind (cap fulfill-handler reject-handler) reaction
    (let ((state (promise-state p)) (value (promise-value p)))
      (enqueue-microtask
       (lambda ()
         (let ((handler (if (eq state :fulfilled) fulfill-handler reject-handler)))
           (cond
             ((null handler)
              ;; default: passthrough (fulfill) or rethrow (reject)
              (if cap
                  (if (eq state :fulfilled) (cap-resolve cap value) (cap-reject cap value))
                  ;; internal reaction (CL closure form) — value ignored
                  nil))
             ((functionp handler)
              ;; internal CL closure reaction (async driver / await)
              (funcall handler value))
             (t
              (handler-case
                  (let ((r (js-call handler *undefined* (list value))))
                    (when cap (cap-resolve cap r)))
                (shuttle-error (e)
                  (when cap (cap-reject cap (shuttle-error-value e)))))))))))))

(defun promise-then (p on-fulfill on-reject)
  "Register CL-closure reactions (each (value)->_) on promise P. Internal use by the
   async driver and await (no result promise)."
  (setf (promise-already-handled-p p) t)
  (let ((reaction (list nil on-fulfill on-reject)))
    (if (eq (promise-state p) :pending)
        (push reaction (promise-reactions p))
        (schedule-reaction p reaction))))

(defun perform-promise-then (p on-fulfill on-reject result-cap)
  "PerformPromiseThen with JS handlers (or *undefined*) targeting RESULT-CAP."
  (setf (promise-already-handled-p p) t)
  (let* ((f (and (js-callable-p on-fulfill) on-fulfill))
         (r (and (js-callable-p on-reject) on-reject))
         (reaction (list result-cap f r)))
    (if (eq (promise-state p) :pending)
        (push reaction (promise-reactions p))
        (schedule-reaction p reaction))
    (if result-cap (pcap-promise result-cap) *undefined*)))

(defun js-promise-resolve (value &optional (c nil))
  "PromiseResolve(C, value). With no C, uses %Promise%. If VALUE is a promise whose
   constructor is C, return it; else new capability, resolve with VALUE."
  (let ((c (or c (promise-constructor))))
    (if (and (promisep value)
             (let ((ctor (ignore-errors (js-get value "constructor")))) (eq ctor c)))
        value
        (let ((cap (new-promise-capability c)))
          (cap-resolve cap value)
          (pcap-promise cap)))))

(defun promise-constructor ()
  (let ((cell (assoc *current-realm* *promise-ctor-cache*)))
    (if cell (cdr cell)
        (progn (ensure-promise-global)
               (cdr (assoc *current-realm* *promise-ctor-cache*))))))

(defun promise-species-ctor (o default)
  "SpeciesConstructor(O, defaultConstructor): C = O.constructor; if undefined return
   default; else S = C[@@species]; if null/undefined return default; must be ctor.
   (Named distinctly from builtins/regexp.lisp's 3-arg species-constructor.)"
  (let ((c (js-get o "constructor")))
    (if (js-undefined-p c) default
        (progn
          (unless (js-object-p c)
            (js-throw (make-native-error "TypeError" "constructor is not an object")))
          (let* ((species-sym (or *symbol-species* (well-known-symbol "species")))
                 (s (if species-sym (js-get c species-sym) *undefined*)))
            (if (js-null-or-undef s) default
                (if (and (js-object-p s) (js-object-construct s)) s
                    (js-throw (make-native-error "TypeError" "@@species is not a constructor")))))))))

(defvar *symbol-species* nil)   ; @@species (looked up lazily)

(defun promise-prototype ()
  (let ((cell (assoc *current-realm* *promise-proto-cache*)))
    (if cell (cdr cell)
        (let ((pp (make-object :proto (%obj-proto))))
          (flet ((native (name len fn)
                   (let ((f (native-fn fn len name)))
                     (put pp name f :enumerable nil :configurable t :writable t))))
            (native "then" 2
              (lambda (this args)
                (unless (promisep this)
                  (js-throw (make-native-error "TypeError" "Promise.prototype.then called on non-promise")))
                (let* ((onf (if args (car args) *undefined*))
                       (onr (if (cdr args) (cadr args) *undefined*))
                       (c (promise-species-ctor this (promise-constructor)))
                       (cap (new-promise-capability c)))
                  (perform-promise-then this onf onr cap))))
            (native "catch" 1
              (lambda (this args)
                (let ((then (js-get this "then")))
                  (js-call then this (list *undefined* (if args (car args) *undefined*))))))
            (native "finally" 1
              (lambda (this args)
                (unless (js-object-p this)
                  (js-throw (make-native-error "TypeError" "Promise.prototype.finally called on non-object")))
                (let* ((c (promise-species-ctor this (promise-constructor)))
                       (on-finally (if args (car args) *undefined*))
                       (then (js-get this "then")))
                  (if (js-callable-p on-finally)
                      (let ((then-finally
                              (native-fn
                               (lambda (th a) (declare (ignore th))
                                 (let* ((value (if a (car a) *undefined*))
                                        (result (js-call on-finally *undefined* '()))
                                        (promise (js-promise-resolve result c))
                                        (value-thunk (native-fn (lambda (t2 a2) (declare (ignore t2 a2)) value) 0)))
                                   (let ((th2 (js-get promise "then")))
                                     (js-call th2 promise (list value-thunk)))))
                               1))
                            (catch-finally
                              (native-fn
                               (lambda (th a) (declare (ignore th))
                                 (let* ((reason (if a (car a) *undefined*))
                                        (result (js-call on-finally *undefined* '()))
                                        (promise (js-promise-resolve result c))
                                        (thrower (native-fn (lambda (t2 a2) (declare (ignore t2 a2))
                                                              (js-throw reason)) 0)))
                                   (let ((th2 (js-get promise "then")))
                                     (js-call th2 promise (list thrower)))))
                               1)))
                        (js-call then this (list then-finally catch-finally)))
                      (js-call then this (list on-finally on-finally)))))))
          (let ((tag (or *symbol-to-string-tag* (well-known-symbol "toStringTag"))))
            (when tag
              (put pp tag "Promise" :enumerable nil :writable nil :configurable t)))
          (push (cons *current-realm* pp) *promise-proto-cache*)
          pp))))

(defun promise-executor-run (p executor)
  "Run a Promise EXECUTOR with fresh resolving functions bound to P. A synchronous
   throw rejects P via the reject function."
  (multiple-value-bind (res rej) (make-resolving-functions p)
    (handler-case (js-call executor *undefined* (list res rej))
      (shuttle-error (e) (js-call rej *undefined* (list (shuttle-error-value e)))))
    p))

(defun install-promise-global (realm)
  "Install the Promise constructor + statics into REALM's global."
  (let* ((*current-realm* realm)
         (proto (promise-prototype))
         (ctor (make-object :proto (%fn-proto) :class "Function")))
    (setf (js-object-call ctor)
          (lambda (this args) (declare (ignore this args))
            (js-throw (make-native-error "TypeError" "Promise constructor cannot be invoked without new"))))
    (setf (js-object-construct ctor)
          (lambda (args new-target)
            (when (js-undefined-p new-target)
              (js-throw (make-native-error "TypeError" "Promise constructor requires new")))
            (let ((executor (if args (car args) *undefined*)))
              (unless (js-callable-p executor)
                (js-throw (make-native-error "TypeError" "Promise resolver is not a function")))
              ;; OrdinaryCreateFromConstructor(newTarget, %Promise.prototype%)
              (let ((p (make-promise (get-proto-from-constructor new-target proto))))
                (promise-executor-run p executor)))))
    (put ctor "length" 1d0 :enumerable nil :writable nil :configurable t)
    (put ctor "name" "Promise" :enumerable nil :writable nil :configurable t)
    (put ctor "prototype" proto :enumerable nil :writable nil :configurable nil)
    (put proto "constructor" ctor :enumerable nil :writable t :configurable t)
    (push (cons realm ctor) *promise-ctor-cache*)
    (flet ((static (name len fn)
             (put ctor name (native-fn fn len name) :enumerable nil :writable t :configurable t)))
      (static "resolve" 1 (lambda (this args)
                            (unless (js-object-p this)
                              (js-throw (make-native-error "TypeError" "Promise.resolve called on non-object")))
                            (js-promise-resolve (if args (car args) *undefined*) this)))
      (static "reject" 1 (lambda (this args)
                           (let ((cap (new-promise-capability this)))
                             (cap-reject cap (if args (car args) *undefined*))
                             (pcap-promise cap))))
      (static "all" 1 (lambda (this args)
                        (promise-combine this (if args (car args) *undefined*) :all)))
      (static "allSettled" 1 (lambda (this args)
                               (promise-combine this (if args (car args) *undefined*) :all-settled)))
      (static "race" 1 (lambda (this args)
                         (promise-combine this (if args (car args) *undefined*) :race)))
      (static "any" 1 (lambda (this args)
                        (promise-combine this (if args (car args) *undefined*) :any)))
      (static "withResolvers" 0 (lambda (this args) (declare (ignore args))
                                  (let* ((cap (new-promise-capability this))
                                         (o (make-object :proto (%obj-proto))))
                                    (put o "promise" (pcap-promise cap))
                                    (put o "resolve" (pcap-resolve cap))
                                    (put o "reject" (pcap-reject cap))
                                    o)))
      (static "try" 1 (lambda (this args)
                        (unless (js-object-p this)
                          (js-throw (make-native-error "TypeError" "Promise.try called on non-object")))
                        (let* ((cap (new-promise-capability this))
                               (callback (if args (car args) *undefined*))
                               (extra (if args (cdr args) '())))
                          (handler-case
                              (let ((r (js-call callback *undefined* extra)))
                                (cap-resolve cap r))
                            (shuttle-error (e) (cap-reject cap (shuttle-error-value e))))
                          (pcap-promise cap)))))
    ;; @@species getter on the constructor: returns `this`.
    (let ((species-sym (or *symbol-species* (well-known-symbol "species"))))
      (when species-sym
        (setf *symbol-species* species-sym)
        (let ((getter (native-fn (lambda (this args) (declare (ignore args)) this) 0 "get [Symbol.species]")))
          (put-accessor ctor species-sym :get getter :enumerable nil :configurable t))))
    (define-global realm "Promise" ctor)
    ctor))

(defun promise-combine (c iterable mode)
  "Promise.all/allSettled/race/any spec algorithm. C is `this` (a constructor).
   Creates a capability from C, gets C.resolve once, iterates, applies MODE."
  (let ((cap (new-promise-capability c)))    ; throws TypeError if C not a ctor
    (handler-case
        (let ((promise-resolve (js-get c "resolve")))
          (unless (js-callable-p promise-resolve)
            (js-throw (make-native-error "TypeError" "Promise.resolve is not callable")))
          (perform-promise-combine c iterable mode cap promise-resolve))
      (shuttle-error (e)
        (cap-reject cap (shuttle-error-value e))))
    (pcap-promise cap)))

(defun perform-promise-combine (c iterable mode cap promise-resolve)
  "The Perform* body: iterate ITERABLE, calling C.resolve on each element and
   subscribing per-mode reactions. Uses a shared remaining counter. Results are
   stored into growable adjustable slot vectors indexed by natural order."
  (let ((it (get-iterator iterable))
        (remaining (list 1))          ; boxed guard: bumped per element, dropped after loop
        (slots (make-array 0 :adjustable t :fill-pointer 0))  ; result values, natural order
        (index 0)
        (iter-done nil))              ; t once next() reported done or itself threw
    (labels ((slot-set (i v) (setf (aref slots i) v))
             (settle-if-done ()
               (when (zerop (decf (car remaining)))
                 (ecase mode
                   ((:all :all-settled) (cap-resolve cap (make-array-object (coerce slots 'list))))
                   (:any (cap-reject cap (make-aggregate-error (coerce slots 'list))))
                   (:race nil)))))
      (handler-case
       (loop
        (let ((step (handler-case (iterator-step it)
                      (shuttle-error (e) (setf iter-done t) (error e)))))
          ;; IteratorComplete / IteratorValue: a throw reading done/value sets
          ;; the record's [[done]] (so no IteratorClose) — mirror with iter-done.
          (when (js-truthy (handler-case (js-get step "done")
                             (shuttle-error (e) (setf iter-done t) (error e))))
            (setf iter-done t) (return))
          (let* ((next-value (handler-case (js-get step "value")
                               (shuttle-error (e) (setf iter-done t) (error e))))
                 (idx index)
                 (next-promise (js-call promise-resolve c (list next-value)))
                 (then (js-get next-promise "then")))
            (vector-push-extend *undefined* slots)
            (incf index)
            (incf (car remaining))
            (ecase mode
              (:all
               (let ((already nil))
                 (let ((on-full (native-fn
                                 (lambda (th a) (declare (ignore th))
                                   (unless already
                                     (setf already t)
                                     (slot-set idx (if a (car a) *undefined*))
                                     (settle-if-done))
                                   *undefined*) 1)))
                   (js-call then next-promise (list on-full (pcap-reject cap))))))
              (:all-settled
               (let ((already nil))
                 (let ((on-full (native-fn
                                 (lambda (th a) (declare (ignore th))
                                   (unless already
                                     (setf already t)
                                     (let ((o (make-object :proto (%obj-proto))))
                                       (put o "status" "fulfilled")
                                       (put o "value" (if a (car a) *undefined*))
                                       (slot-set idx o))
                                     (settle-if-done))
                                   *undefined*) 1))
                       (on-rej (native-fn
                                (lambda (th a) (declare (ignore th))
                                  (unless already
                                    (setf already t)
                                    (let ((o (make-object :proto (%obj-proto))))
                                      (put o "status" "rejected")
                                      (put o "reason" (if a (car a) *undefined*))
                                      (slot-set idx o))
                                    (settle-if-done))
                                  *undefined*) 1)))
                   (js-call then next-promise (list on-full on-rej)))))
              (:any
               (let ((already nil))
                 (let ((on-rej (native-fn
                                (lambda (th a) (declare (ignore th))
                                  (unless already
                                    (setf already t)
                                    (slot-set idx (if a (car a) *undefined*))
                                    (settle-if-done))
                                  *undefined*) 1)))
                   (js-call then next-promise (list (pcap-resolve cap) on-rej)))))
              (:race
               (js-call then next-promise (list (pcap-resolve cap) (pcap-reject cap))))))))
       ;; Abrupt completion mid-iteration (Invoke resolve / Get then / then call
       ;; threw): the iterator is not done, so IteratorClose it, then re-throw so
       ;; promise-combine rejects the capability.
       (shuttle-error (e)
         (unless iter-done (iterator-close it))
         (error e)))                                       ; handler-case
      ;; drop the initial guard
      (settle-if-done))))                                  ; labels let defun

(defun make-aggregate-error (errors)
  "Build an AggregateError whose errors list is ERRORS (natural order)."
  (let ((ctor (ignore-errors (js-get (realm-global *current-realm*) "AggregateError"))))
    (if (and ctor (js-object-p ctor) (js-object-construct ctor))
        (js-construct ctor (list (make-array-object errors) "All promises were rejected"))
        (make-native-error "TypeError" "All promises were rejected"))))

(defun iterable-to-list (iterable)
  (let ((it (get-iterator iterable)) (out '()))
    (loop (let ((r (iterator-step it)))
            (when (js-truthy (js-get r "done")) (return))
            (push (js-get r "value") out)))
    (nreverse out)))

(defun well-known-symbol (name)
  "Look up a well-known symbol (e.g. \"asyncIterator\", \"toStringTag\") off the
   realm's Symbol constructor; nil if Symbol isn't installed."
  (multiple-value-bind (sym p) (env-get (realm-global-env *current-realm*) "Symbol")
    (when (and p (js-object-p sym))
      (let ((s (js-get sym name)))
        (when (js-symbol-p s) s)))))

(defun get-async-iterator (obj)
  "Get the async iterator of OBJ (@@asyncIterator), falling back to a sync
   iterator wrapped so its results present as {value,done}."
  (let ((o (to-object obj))
        (*symbol-async-iterator* (or *symbol-async-iterator* (well-known-symbol "asyncIterator"))))
    (let ((aif (and *symbol-async-iterator* (js-get o *symbol-async-iterator*))))
      (if (js-callable-p aif)
          (let ((it (js-call aif o '())))
            (unless (js-object-p it) (js-throw (make-native-error "TypeError" "async iterator is not an object")))
            it)
          ;; fall back to the sync iterator (its next() returns {value,done}; the
          ;; for-await loop awaits value/result which is fine for sync iterables)
          (get-iterator obj)))))

;;; ---- async functions ----
;;; An async function body runs on the SAME thread-coroutine machinery as a
;;; generator. `await x` is a suspension: the coroutine yields X to a driver, which
;;; resolves X as a promise and, when it settles, resumes the coroutine with the
;;; fulfilled value (or throws the rejection into it). The async call returns a
;;; Promise immediately; the body runs synchronously until the first await, then
;;; the remainder runs on microtasks.
(defstruct await-request value)   ; suspension marker: an `await`, vs. a plain yield
(defun async-await (value)
  "Called at an `await` inside an async coroutine worker. Hands VALUE out to the
   driver as an await request; resumes with the settled value or throws rejection."
  (gen-yield (make-await-request :value value)))

(defun make-async-function-object (code env this args fn)
  "Run an async function: create the coroutine, drive it, return the result Promise.
   Param binding runs synchronously; a throw there becomes a rejected promise (the
   make-js-function :async wrapper catches it)."
  (let* ((fenv (instantiate-fn-env code env this args fn))
         (gs (make-genstate))
         (result (make-promise))
         (realm *current-realm*))
    ;; the worker: like a generator, but there is no consumer calling .next — the
    ;; DRIVER pumps it. Each yield is an await request.
    (incf *generators-created*)
    (when (zerop (mod *generators-created* 64)) (reap-generators))
    (setf (genstate-thread gs)
          (sb-thread:make-thread
           (lambda ()
             (block worker
               (let ((*current-realm* realm) (*current-generator* gs) (*steps* 0) (*run-depth* 1))
                 (sb-thread:wait-on-semaphore (genstate-to-gen-sem gs))
                 (handler-case
                     (progn
                       (when (eq (genstate-mode gs) :terminate) (return-from worker))
                       (let ((rv (catch 'generator-return
                                   (run code fenv this args fn))))
                         (setf (genstate-yielded gs) rv (genstate-done gs) t)))
                   (generator-terminate () (return-from worker))
                   (shuttle-error (e) (setf (genstate-error gs) e (genstate-done gs) t))
                   (serious-condition (e)
                     (setf (genstate-error gs)
                           (make-condition 'shuttle-error
                                           :value (make-native-error "Error"
                                                    (format nil "async error: ~a" e)))
                           (genstate-done gs) t)))
                 (sb-thread:signal-semaphore (genstate-to-consumer-sem gs)))))
           :name "shuttle-async"))
    (push gs *live-generators*)
    ;; drive it: run to the first await/completion synchronously.
    (async-drive gs result :next *undefined*)
    result))

(defun async-drive (gs result mode value)
  "Resume the async coroutine GS with MODE/VALUE. If it awaits, subscribe to the
   awaited promise to resume later; if it completes, settle RESULT."
  (when (genstate-done gs)
    (return-from async-drive nil))
  (setf (genstate-mode gs) mode (genstate-sent gs) value)
  (sb-thread:signal-semaphore (genstate-to-gen-sem gs))
  (sb-thread:wait-on-semaphore (genstate-to-consumer-sem gs))
  (cond
    ((genstate-error gs)
     (let ((e (genstate-error gs))) (setf (genstate-error gs) nil)
       (promise-settle result :rejected (shuttle-error-value e))))
    ((genstate-done gs)
     (resolve-promise result (genstate-yielded gs)))
    (t
     ;; the coroutine awaited a value; wrap in a promise and subscribe to resume.
     (let* ((y (genstate-yielded gs))
            (awaited (js-promise-resolve (if (await-request-p y) (await-request-value y) y))))
       (promise-then awaited
         (lambda (v) (async-drive gs result :next v))
         (lambda (v) (async-drive gs result :throw v)))))))

;;; ---- async generators (minimal) ----
;;; An async generator's body yields values and awaits. Its next()/return()/throw()
;;; each return a Promise of {value,done}. We run the body on the coroutine and, per
;;; next(), pump until the next YIELD (resolving intervening awaits on the microtask
;;; queue), then resolve the promise with {value,done}.
(defun make-async-generator-object (code env this args fn)
  (incf *generators-created*)
  (when (zerop (mod *generators-created* 64)) (reap-generators))
  (let ((fenv (instantiate-fn-env code env this args fn)))   ; params bound synchronously
   (let* ((gs (make-genstate))
         (gproto (let ((pp (js-get fn "prototype"))) (if (js-object-p pp) pp (async-generator-prototype))))
         (gobj (make-object :proto gproto :class "AsyncGenerator"))
         (realm *current-realm*))
    (setf (getf (js-object-internal gobj) :genstate) gs)
    (setf (getf (js-object-internal gobj) :async-gen) t)
    (setf (genstate-thread gs)
          (sb-thread:make-thread
           (lambda ()
             (block worker
               (let ((*current-realm* realm) (*current-generator* gs) (*steps* 0) (*run-depth* 1))
                 (sb-thread:wait-on-semaphore (genstate-to-gen-sem gs))
                 (handler-case
                     (progn
                       (when (eq (genstate-mode gs) :terminate) (return-from worker))
                       (let ((rv (catch 'generator-return
                                   (case (genstate-mode gs)
                                     (:throw (js-throw (genstate-sent gs)))
                                     (:return (genstate-sent gs))
                                     (t (run code fenv this args fn))))))
                         (setf (genstate-yielded gs) rv (genstate-done gs) t)))
                   (generator-terminate () (return-from worker))
                   (shuttle-error (e) (setf (genstate-error gs) e (genstate-done gs) t))
                   (serious-condition (e)
                     (setf (genstate-error gs)
                           (make-condition 'shuttle-error
                                           :value (make-native-error "Error" (format nil "async generator error: ~a" e)))
                           (genstate-done gs) t)))
                 (sb-thread:signal-semaphore (genstate-to-consumer-sem gs)))))
           :name "shuttle-async-generator"))
    (push gs *live-generators*)
    gobj)))

(defun async-generator-step (gobj mode value)
  "next/return/throw on an async generator -> a Promise of {value,done}. Pumps the
   coroutine, resolving intervening awaits, until a yield or completion."
  (let ((gs (getf (js-object-internal gobj) :genstate))
        (result (make-promise)))
    (unless gs (promise-settle result :rejected (make-native-error "TypeError" "not an async generator"))
      (return-from async-generator-step result))
    (labels ((pump (m v)
               (when (genstate-done gs)
                 (case m
                   (:throw (promise-settle result :rejected v))
                   (t (resolve-promise result (iter-result (if (eq m :return) v *undefined*) t))))
                 (return-from pump))
               (setf (genstate-mode gs) m (genstate-sent gs) v)
               (sb-thread:signal-semaphore (genstate-to-gen-sem gs))
               (sb-thread:wait-on-semaphore (genstate-to-consumer-sem gs))
               (cond
                 ((genstate-error gs)
                  (let ((e (genstate-error gs))) (setf (genstate-error gs) nil)
                    (promise-settle result :rejected (shuttle-error-value e))))
                 ((genstate-done gs)
                  (resolve-promise result (iter-result (genstate-yielded gs) t)))
                 (t (let ((y (genstate-yielded gs)))
                      (if (await-request-p y)
                          ;; an await inside the async generator: settle then resume
                          (let ((awaited (js-promise-resolve (await-request-value y))))
                            (promise-then awaited
                              (lambda (rv) (pump :next rv))
                              (lambda (rv) (pump :throw rv))))
                          ;; a real yield: resolve the yielded value, then {value,done:false}
                          (let ((awaited (js-promise-resolve y)))
                            (promise-then awaited
                              (lambda (rv) (resolve-promise result (iter-result rv nil)))
                              (lambda (rv) (promise-settle result :rejected rv))))))))))
      (pump mode value))
    result))

(defvar *async-generator-proto-cache* nil)
(defun async-generator-prototype ()
  (let ((cell (assoc *current-realm* *async-generator-proto-cache*)))
    (if cell (cdr cell)
        (let ((gp (make-object :proto (%obj-proto))))
          (flet ((native (name fn) (let ((f (make-object :proto (%fn-proto) :class "Function")))
                                     (setf (js-object-call f) fn)
                                     (put f "name" name :enumerable nil :writable nil :configurable t)
                                     (put gp name f :enumerable nil :configurable t :writable t))))
            (native "next"   (lambda (this args) (async-generator-step this :next (if args (car args) *undefined*))))
            (native "return" (lambda (this args) (async-generator-step this :return (if args (car args) *undefined*))))
            (native "throw"  (lambda (this args) (async-generator-step this :throw (if args (car args) *undefined*)))))
          (let ((asit (or *symbol-async-iterator* (well-known-symbol "asyncIterator"))))
            (when asit
              (let ((f (make-object :proto (%fn-proto) :class "Function")))
                (setf (js-object-call f) (lambda (this args) (declare (ignore args)) this))
                (put f "name" "[Symbol.asyncIterator]" :enumerable nil :writable nil :configurable t)
                (put gp asit f :enumerable nil :configurable t))))
          (push (cons *current-realm* gp) *async-generator-proto-cache*)
          gp))))

;;; ---- classes ----
(defun build-class (ctor-code super derived env &optional cname)
  "Create the class: a constructor function + a prototype object. SUPER is the
   parent class value (undefined if none). Returns the constructor object."
  (let* ((super-present (not (eq super *undefined*)))
         (super-ctor (cond ((not super-present) nil)
                           ((eq super *null*) :null)
                           ((js-callable-p super) super)
                           (t (js-throw (make-native-error "TypeError" "Class extends value is not a constructor or null")))))
         (parent-proto (cond ((not super-present) (%obj-proto))
                             ((eq super *null*) *null*)
                             (t (let ((pp (js-get super "prototype")))
                                  (cond ((js-object-p pp) pp) ((eq pp *null*) *null*)
                                        (t (js-throw (make-native-error "TypeError" "Class extends prototype is not an object or null"))))))))
         (proto (make-object :proto parent-proto))
         (fn (make-js-function ctor-code env :kind (if derived :class-derived :class-base))))
    ;; wire prototype <-> constructor
    (put proto "constructor" fn :enumerable nil :writable t :configurable t)
    ;; replace the auto-created prototype with ours
    (js-define-own-property fn "prototype"
      (list :value proto :writable nil :enumerable nil :configurable nil))
    ;; constructor's [[Prototype]] chains to the parent constructor (static inherit)
    (when super-present
      (setf (js-object-proto fn) (if (eq super-ctor :null) (%fn-proto) super)))
    ;; the constructor's name is the class name (not "constructor")
    (js-define-own-property fn "name"
      (list :value (if cname cname "") :writable nil :enumerable nil :configurable t))
    ;; home object for super.* in the constructor = the prototype
    (setf (fn-home fn) proto)
    (setf (fn-super-ctor fn) (if (eq super-ctor :null) :null super-ctor))
    fn))

(defun run-super-ctor (super-ctor this args &optional new-target)
  "Execute super(...): run the parent class constructor's body on THIS.
   NEW-TARGET is the derived constructor currently running (for native bases whose
   [[Construct]] needs it). Returns the object to use as `this` (the base's
   [[Construct]] result, when it produces its own object)."
  (cond
    ((or (null super-ctor) (eq super-ctor :null))
     (js-throw (make-native-error "SyntaxError" "'super' keyword unexpected here")))
    (t
     ;; class ctors stash their raw runner under :ctor-run; native/builtin bases
     ;; expose [[Construct]] — invoke it (with the derived ctor as NewTarget) and
     ;; adopt its result as `this` (copying own props onto the pre-made instance
     ;; keeps the derived prototype chain the caller already installed).
     (let ((run-fn (getf (js-object-internal super-ctor) :ctor-run)))
       (cond
         (run-fn (funcall run-fn this args) this)
         ((js-object-construct super-ctor)
          (let ((r (funcall (js-object-construct super-ctor) args (or new-target super-ctor))))
            (if (js-object-p r)
                (progn
                  ;; adopt the base-created instance's own properties + internal
                  ;; slots + primitive onto THIS (which already carries the derived
                  ;; prototype the caller installed). Rebuild each own descriptor as
                  ;; a plist (js-get-own-property returns a PROP struct).
                  (dolist (k (js-own-keys r))
                    (let ((d (js-get-own-property r k)))
                      (when (prop-p d)
                        (js-define-own-property this k
                          (if (prop-accessor d)
                              (list :get (prop-get d) :set (prop-set d) :accessor t
                                    :enumerable (prop-enumerable d) :configurable (prop-configurable d))
                              (list :value (prop-value d) :writable (prop-writable d)
                                    :enumerable (prop-enumerable d) :configurable (prop-configurable d)))))))
                  (when (js-object-primitive r)
                    (setf (js-object-primitive this) (js-object-primitive r)))
                  (when (js-object-internal r)
                    (setf (js-object-internal this)
                          (append (js-object-internal r) (js-object-internal this))))
                  ;; adopt the base's exotic class (Array/Error/Map/...) so the
                  ;; instance carries the base exotic behavior (Object.prototype.toString
                  ;; tag, Array [[DefineOwnProperty]] length maintenance, etc.).
                  (when (and (js-object-class r)
                             (not (string= (js-object-class r) "Object")))
                    (setf (js-object-class this) (js-object-class r)))
                  this)
                this)))
         (t
          (let ((c (js-object-call super-ctor)))
            (if c (progn (funcall c this args) this)
                (js-throw (make-native-error "TypeError" "super constructor is not callable"))))))))))

;;; ---- operators ----
(defun to-int32 (v)
  (let ((n (to-number v)))
    (if (or (js-nan-p n) (= n *inf*) (= n *-inf*)) 0
        (let ((m (mod (truncate n) #x100000000))) (if (>= m #x80000000) (- m #x100000000) m)))))

(defun js-mod (a b)
  (with-js-floats
    (let ((x (to-number a)) (y (to-number b)))
      (cond ((or (js-nan-p x) (js-nan-p y) (zerop y) (= (abs x) *inf*)) *nan*)
            ((= (abs y) *inf*) x) ((zerop x) x) (t (rem x y))))))

(defun to-numeric (v)
  "ToNumeric: ToPrimitive(number) then, if a BigInt, keep it; else ToNumber."
  (let ((p (to-primitive v :number)))
    (if (js-bigint-p p) p (to-number p))))

(defun bigint-number-lessp (x y)
  "Mathematically-exact x < y where one is a BigInt integer and the other a Number.
   Returns :nan if the Number is NaN (relational -> undefined/false), else T/NIL."
  (let ((bi (if (integerp x) x y)) (num (if (floatp x) x y)) (bi-first (integerp x)))
    (cond
      ((js-nan-p num) :nan)
      ((= num *inf*) (if bi-first t nil))       ; bi < +Inf ; +Inf < bi -> nil
      ((= num *-inf*) (if bi-first nil t))      ; bi < -Inf -> nil ; -Inf < bi -> t
      (t (let ((rn (rationalize num)))
           (if bi-first (< bi rn) (< rn bi)))))))

(defun js-relational (op a b)
  (let ((pa (to-primitive a :number)) (pb (to-primitive b :number)))
    (cond
      ((and (stringp pa) (stringp pb))
       (js-bool (funcall (cond ((string= op "<") #'string<) ((string= op ">") #'string>)
                               ((string= op "<=") #'string<=) (t #'string>=)) pa pb)))
      ;; both BigInt
      ((and (js-bigint-p pa) (js-bigint-p pb))
       (js-bool (funcall (cond ((string= op "<") #'<) ((string= op ">") #'>)
                               ((string= op "<=") #'<=) (t #'>=)) pa pb)))
      ;; BigInt vs String: parse the string as a BigInt; unparseable -> undefined (false)
      ((or (and (js-bigint-p pa) (stringp pb)) (and (stringp pa) (js-bigint-p pb)))
       (let* ((sv (if (stringp pa) pa pb))
              (bi (if (stringp pa) pb pa))
              (parsed (string-to-bigint sv)))
         (if (not (integerp parsed)) *false*
             (let ((x (if (stringp pa) parsed bi)) (y (if (stringp pa) bi parsed)))
               (js-bool (funcall (cond ((string= op "<") #'<) ((string= op ">") #'>)
                                       ((string= op "<=") #'<=) (t #'>=)) x y))))))
      (t
       ;; General numeric relational: ToNumeric both. If exactly one is a BigInt,
       ;; compare mathematically (exact); otherwise both are Numbers.
       (let ((x (to-numeric pa)) (y (to-numeric pb)))
         (cond
           ((and (js-bigint-p x) (js-bigint-p y))
            (js-bool (funcall (cond ((string= op "<") #'<) ((string= op ">") #'>)
                                    ((string= op "<=") #'<=) (t #'>=)) x y)))
           ((or (js-bigint-p x) (js-bigint-p y))
            (flet ((lt (u w) (bigint-number-lessp u w)))
              (js-bool (cond
                         ((string= op "<")  (let ((r (lt x y))) (and (not (eq r :nan)) r)))
                         ((string= op ">")  (let ((r (lt y x))) (and (not (eq r :nan)) r)))
                         ((string= op "<=") (let ((r (lt y x))) (and (not (eq r :nan)) (not r))))
                         (t                 (let ((r (lt x y))) (and (not (eq r :nan)) (not r))))))))
           (t
            (if (or (js-nan-p x) (js-nan-p y)) *false*
                (js-bool (funcall (cond ((string= op "<") #'<) ((string= op ">") #'>)
                                        ((string= op "<=") #'<=) (t #'>=)) x y))))))))))

(defun bigint-mix-error ()
  (js-throw (make-native-error "TypeError" "Cannot mix BigInt and other types, use explicit conversions")))

(defun bigint-binop (op x y)
  "A numeric binary op where at least one operand (after ToNumeric) is a BigInt.
   Both must be BigInt; otherwise TypeError. >>> on BigInt -> TypeError."
  (unless (and (js-bigint-p x) (js-bigint-p y)) (bigint-mix-error))
  (cond
    ((string= op "-") (- x y))
    ((string= op "*") (* x y))
    ((string= op "/") (if (zerop y) (js-throw (make-native-error "RangeError" "Division by zero"))
                          (truncate x y)))
    ((string= op "%") (if (zerop y) (js-throw (make-native-error "RangeError" "Division by zero"))
                          (rem x y)))
    ((string= op "**") (if (minusp y) (js-throw (make-native-error "RangeError" "Exponent must be non-negative"))
                           (expt x y)))
    ((string= op "&") (logand x y))
    ((string= op "|") (logior x y))
    ((string= op "^") (logxor x y))
    ((string= op "<<") (ash x y))
    ((string= op ">>") (ash x (- y)))
    ((string= op ">>>") (js-throw (make-native-error "TypeError" "BigInts have no unsigned right shift, use >> instead")))
    (t (js-throw (format nil "operator ~a not supported for BigInt" op)))))

(defun js-numeric-binop (op a b)
  "Arithmetic/bitwise binary op with ToNumeric coercion: dispatches to the BigInt
   path if either coerced operand is a BigInt (else the Number path)."
  (let ((x (to-numeric a)) (y (to-numeric b)))
    (if (or (js-bigint-p x) (js-bigint-p y))
        (bigint-binop op x y)
        ;; both Number
        (with-js-floats
          (cond
            ((string= op "-") (- x y))
            ((string= op "*") (* x y))
            ((string= op "/") (/ x y))
            ((string= op "%") (js-mod x y))
            ((string= op "**") (js-pow x y))
            ((string= op "<<") (let ((m (mod (logand (to-int32 x) #xFFFFFFFF) #x100000000))
                                     (s (logand (to-int32 y) 31)))
                                 (let ((r (mod (ash m s) #x100000000)))
                                   (float (if (>= r #x80000000) (- r #x100000000) r) 1d0))))
            ((string= op ">>") (float (ash (to-int32 x) (- (logand (to-int32 y) 31))) 1d0))
            ((string= op ">>>") (float (ash (to-uint32 x) (- (logand (to-int32 y) 31))) 1d0))
            ((string= op "&") (float (logand (to-int32 x) (to-int32 y)) 1d0))
            ((string= op "|") (float (logior (to-int32 x) (to-int32 y)) 1d0))
            ((string= op "^") (float (logxor (to-int32 x) (to-int32 y)) 1d0))
            (t (js-throw (format nil "operator ~a not supported" op))))))))

(defun js-binop (op a b)
  (cond ((string= op "+") (js-add a b))
        ((member op '("-" "*" "/" "%" "**" "<<" ">>" ">>>" "&" "|" "^") :test #'string=)
         (js-numeric-binop op a b))
        ((string= op "===") (js-bool (js-strict-equal a b)))
        ((string= op "!==") (js-bool (not (js-strict-equal a b))))
        ((string= op "==") (js-bool (js-equal a b)))
        ((string= op "!=") (js-bool (not (js-equal a b))))
        ((member op '("<" ">" "<=" ">=") :test #'string=) (js-relational op a b))
        ((string= op "instanceof") (js-bool (js-instanceof a b)))
        ((string= op "in") (js-bool (and (js-object-p b) (js-has b (prop-key a)))))
        (t (js-throw (format nil "operator ~a not supported" op)))))

(defun js-instanceof (a b)
  (unless (js-callable-p b) (js-throw "Right-hand side of 'instanceof' is not callable"))
  (let ((proto (js-get b "prototype")))
    (and (js-object-p a)
         (loop for p = (js-get-proto a) then (js-get-proto p)
               while (js-object-p p) thereis (eq p proto)))))

(defun js-unop (op v)
  (cond ((string= op "!") (js-bool (not (js-truthy v))))
        ((string= op "-") (let ((n (to-numeric v))) (if (js-bigint-p n) (- n) (with-js-floats (- n)))))
        ((string= op "+")                    ; unary + on a BigInt -> TypeError
         (let ((p (to-primitive v :number)))
           (if (js-bigint-p p)
               (js-throw (make-native-error "TypeError" "Cannot convert a BigInt value to a number"))
               (to-number p))))
        ((string= op "~") (let ((n (to-numeric v)))
                            (if (js-bigint-p n) (lognot n) (float (lognot (to-int32 n)) 1d0))))
        ((string= op "void") *undefined*)
        ((string= op "typeof") (js-typeof v))
        (t (js-throw (format nil "unary ~a not supported" op)))))

;;; ---- the VM ----
(define-condition shuttle-timeout (error) ()   ; distinct from a JS throw
  (:report (lambda (c s) (declare (ignore c)) (format s "shuttle: instruction budget exceeded"))))
(declaim (type fixnum *steps* *max-steps*))
(defparameter *steps* 0) (defparameter *max-steps* 60000000)  ; per-run budget; the wall-clock is the real infinite-loop backstop, so keep this high enough for legit heavy harness loops (e.g. RegExp property-escapes buildString walks ~1.1M code points → ~31M steps)

(defvar *run-depth* 0)    ; 0 = top-level script run; drain microtasks when it unwinds

(defun realm-eval-intrinsic (realm)
  "The realm's %eval% function object (the value bound to the global `eval`),
   stashed under :eval in the intrinsics plist at install time. Used to tell a
   direct-eval call (`eval(x)` where eval is unshadowed) from an ordinary call."
  (getf (realm-intrinsics realm) :eval))

(defun perform-direct-eval (source env this strictp)
  "PerformEval for a *direct* eval call. Compile SOURCE and run it sharing the
   caller's variable environment (so `var`/function declarations hoist into the
   caller in sloppy mode, and outer bindings are visible), the caller's `this`,
   and — when the calling context is strict OR the eval code has its own
   \"use strict\" — a fresh child env so declarations don't leak (strict eval).
   A SyntaxError in the eval source is thrown as a JS SyntaxError."
  (let* ((code (handler-case (compile-toplevel source t)  ; direct eval = eval code
                 (shuttle-error (e) (error e))
                 (error (e)
                   (js-throw (make-native-error "SyntaxError"
                               (format nil "~a" (ignore-errors (princ-to-string e))))))))
         ;; strict eval (caller strict, or the code's own prologue) evaluates in
         ;; its own declaration scope; sloppy direct eval shares the caller env.
         (own-strict (code-strict code))
         (run-env (if (or strictp own-strict) (new-env env) env)))
    (with-js-floats (run code run-env this))))

(defun run (code env this &optional call-args fn-obj)
  (if (zerop *run-depth*)
      ;; outermost run of a script: run the body, then drain the microtask queue so
      ;; resolved-promise reactions (async .then) fire before the caller observes state.
      (let ((*run-depth* 1) (*microtasks* nil) (*microtask-tail* nil))
        (multiple-value-prog1 (%run code env this call-args fn-obj)
          (drain-microtasks)))
      (%run code env this call-args fn-obj)))

(defun %run (code env this &optional call-args fn-obj)
  (let ((instrs (code-instrs code)) (pc 0)
        (strictp (code-strict code))
        (call-args (coerce call-args 'vector))
        (stack (make-array 64 :adjustable t :fill-pointer 0)) (completion *empty-completion*)
        (home (and fn-obj (fn-home fn-obj)))          ; [[HomeObject]] for super
        (super-ctor (and fn-obj (fn-super-ctor fn-obj)))
        (handlers '()))                      ; ((catch-pc . saved-sp) ...) for try/catch
    (macrolet ((push! (v) `(vector-push-extend ,v stack))
               (pop! () `(vector-pop stack))
               (peek! () `(aref stack (1- (fill-pointer stack)))))
      (loop
       (handler-case
        (loop
        (when (>= pc (length instrs))
          (return-from %run (if (eq completion *empty-completion*) *undefined* completion)))
        (when (>= (incf *steps*) *max-steps*) (error 'shuttle-timeout))
        (let* ((in (aref instrs pc)) (op (car in)) (a (cdr in)))
          (incf pc)
          (case op
            (:push-handler (push (list (first a) (fill-pointer stack) env) handlers))
            (:pop-handler (pop handlers))
            (:const (push! (first a)))
            (:get-var (push! (env-get-checked env (first a))))
            (:typeof-var (push! (env-typeof env (first a))))
            (:set-var (env-set env (first a) (peek!) strictp))
            (:global-instantiate (global-declaration-instantiation env (first a)))
            (:eval-var-decl (eval-var-decl env (first a)))
            (:declare-var (env-declare env (first a) (pop!)))
            (:declare-var-absent                                    ; B.3.3: create var binding only if absent in var scope
             (let ((v (pop!)))
               (unless (env-var-scope-has env (first a)) (env-declare env (first a) v))))
            (:annexb-var-set (env-var-set env (first a) (peek!)))   ; B.3.3 sync var binding; leaves value
            (:push-env (setf env (new-block-env env)))
            (:pop-env (setf env (env-parent env)))
            (:to-object (push! (to-object (pop!))))
            (:to-prop-key (push! (prop-key (pop!))))     ; ToPropertyKey (string or symbol)
            (:array-append (let ((v (peek!)) (arr (env-get-checked env (first a))))  ; push V onto ARR (var), leave V
                             (let ((len (to-number (js-get arr "length"))))
                               (js-set arr (to-string len) v)
                               (js-set arr "length" (+ len 1d0)))))
            (:require-coercible                          ; RequireObjectCoercible: null/undefined -> TypeError (leaves value)
             (let ((v (peek!)))
               (when (or (eq v *null*) (eq v *undefined*))
                 (js-throw (make-native-error "TypeError"
                             (format nil "Cannot destructure '~a' as it is ~a."
                                     (to-string v) (to-string v)))))))
            (:push-with-env (setf env (new-with-env env (pop!))))
            (:tdz-declare (env-declare-lexical env (first a) *tdz*))
            (:init-let (env-declare-lexical env (first a) (pop!)))
            (:init-const (env-declare-const env (first a) (pop!)))
            (:get-this (push! this))
            (:dynamic-import
             ;; import() is a PROMISE, always -- including when the load fails, which is a
             ;; rejection rather than a throw.  The load itself is synchronous here because the
             ;; host loader is; a host that fetches would settle this promise later instead.
             (let ((spec (pop!)) (p (make-promise))
                   (*current-module* (or (and fn-obj (getf (js-object-internal fn-obj) :module))
                                         *current-module*)))
               (handler-case
                   (promise-fulfill p (%dynamic-import-now (to-string spec)))
                 (shuttle-error (e) (promise-reject-internal p (shuttle-error-value e))))
               (push! p)))
            (:import-meta
             (let ((*current-module* (or (and fn-obj (getf (js-object-internal fn-obj) :module))
                                         *current-module*)))
               (push! (%import-meta-object))))
            (:new-target (push! *new-target*))
            (:set-fn-name                                 ; NamedEvaluation: name an anonymous fn/class after its binding
             (let ((v (peek!)) (name (first a)))
               (when (and (js-object-p v)
                          (js-object-call v)               ; it's callable (function or class ctor)
                          (equal "" (js-get v "name")))    ; still anonymous
                 (put v "name" name :enumerable nil :writable nil :configurable t))))
            (:set-fn-name-dyn                             ; [.. key val] -> [.. val]; name val from key (computed prop)
             (let ((v (pop!)) (k (prop-key (pop!))))
               (when (and (js-object-p v) (js-object-call v) (equal "" (js-get v "name")))
                 (put v "name" (js-key-name k) :enumerable nil :writable nil :configurable t))
               (push! v)))
            (:load-arg (let ((n (first a))) (push! (if (< n (length call-args)) (aref call-args n) *undefined*))))
            (:load-rest (let ((n (first a)))
                          (push! (make-array-object
                                  (loop for i from n below (length call-args) collect (aref call-args i))))))
            (:pop (pop!))
            (:dup (push! (peek!)))
            (:dup2 (let ((b (peek!)) (n (fill-pointer stack)))
                     (declare (ignore b))
                     (let ((x (aref stack (- n 2))) (y (aref stack (- n 1))))
                       (push! x) (push! y))))
            (:to-num (push! (to-number (pop!))))
            (:to-numeric (push! (to-numeric (pop!))))
            (:num-step (let ((v (pop!)) (d (first a)))     ; v already ToNumeric'd
                         (push! (if (js-bigint-p v) (+ v d) (with-js-floats (+ v (float d 1d0)))))))
            (:to-str (push! (to-string (pop!))))
            (:swap (let ((n (fill-pointer stack)))
                     (rotatef (aref stack (- n 1)) (aref stack (- n 2)))))
            (:rot3 (let ((n (fill-pointer stack)))   ; [a b c] -> [b c a]
                     (let ((a (aref stack (- n 3))))
                       (setf (aref stack (- n 3)) (aref stack (- n 2))
                             (aref stack (- n 2)) (aref stack (- n 1))
                             (aref stack (- n 1)) a))))
            (:nullish-short (let ((v (peek!)))   ; if top is null/undefined, jump to SHORT (leave it)
                              (when (or (eq v *null*) (eq v *undefined*)) (setf pc (first a)))))
            (:nullish-short-2 (let ((v (peek!)))  ; if top nullish, DROP it then jump to SHORT (value below survives)
                                (when (or (eq v *null*) (eq v *undefined*)) (pop!) (setf pc (first a)))))
            (:save-completion (setf completion (pop!)))
            (:comp-clear (setf completion *empty-completion*))            ; enter a compound stmt: [[value]] := empty
            (:get-completion (push! (if (eq completion *empty-completion*) *undefined* completion)))
            (:comp-default-undef                                          ; leave a compound stmt: UpdateEmpty(., undefined)
             (when (eq completion *empty-completion*) (setf completion *undefined*)))
            (:bin (let ((b (pop!)) (x (pop!))) (push! (js-binop (first a) x b))))
            (:unary (push! (js-unop (first a) (pop!))))
            (:get-prop (let ((k (pop!)) (o (pop!))) (push! (js-get o k))))
            (:get-prop-c (push! (js-get (pop!) (first a))))
            (:set-prop (let ((v (pop!)) (k (pop!)) (o (pop!)))
                         (let ((ok (js-set o k v)))
                           (when (and strictp (not (js-truthy* ok)))
                             (js-throw (make-native-error "TypeError"
                               (format nil "Cannot assign to read-only property '~a' of ~a"
                                       (if (js-symbol-p k) (to-symbol-string k) (to-string k))
                                       (js-typeof o))))))
                         (push! v)))
            (:del-prop (let ((k (pop!)) (o (pop!)))
                         (let ((ok (if (js-object-p o) (js-delete o k) *true*)))
                           (when (and strictp (not (js-truthy* ok)))
                             (js-throw (make-native-error "TypeError"
                               (format nil "Cannot delete property '~a'"
                                       (if (js-symbol-p k) (to-symbol-string k) (to-string k))))))
                           (push! ok))))
            (:update-prop (let* ((delta (first a)) (prefix (second a))
                                 (k (pop!)) (o (pop!))
                                 (old (to-numeric (js-get o k)))
                                 (new (if (js-bigint-p old)
                                          (+ old (truncate delta))
                                          (with-js-floats (+ old delta)))))
                            (let ((ok (js-set o k new)))
                              (when (and strictp (not (js-truthy* ok)))
                                (js-throw (make-native-error "TypeError"
                                  (format nil "Cannot assign to read-only property '~a'"
                                          (if (js-symbol-p k) (to-symbol-string k) (to-string k)))))))
                            (push! (if prefix new old))))
            ;; ---- private class members (#x) ----
            (:private-get (let* ((pn (first a)) (o (pop!))
                                 (el (private-require o pn)))
                            (push! (private-element-get el o))))
            (:private-set (let* ((pn (first a)) (v (pop!)) (o (pop!))
                                 (el (private-require o pn)))
                            (private-element-set el o v) (push! v)))
            (:private-field-add (let* ((v (pop!)) (pn (pop!)) (o (pop!)))
                                  (when (and (js-object-p o) (gethash pn (object-private-table o)))
                                    (js-throw (make-native-error "TypeError"
                                      (format nil "Cannot initialize #~a twice on the same object"
                                              (private-name-description pn)))))
                                  (setf (gethash pn (object-private-table o)) (cons :field v))))
            (:private-method-add (let* ((fn (pop!)) (pn (pop!)) (o (pop!)) (kind (first a))
                                        (tbl (object-private-table o))
                                        (existing (gethash pn tbl)))
                                   (setf (fn-home fn) o)
                                   (put fn "name" (private-method-name kind pn) :enumerable nil :writable nil :configurable t)
                                   (case kind
                                     (:get (setf (gethash pn tbl)
                                                 (list :accessor fn (and existing (fourth existing)))))
                                     (:set (setf (gethash pn tbl)
                                                 (list :accessor (and existing (second existing)) fn)))
                                     (t (setf (gethash pn tbl) (cons :method fn))))))
            (:private-in (let* ((pn (first a)) (o (pop!)))
                           (push! (if (and (js-object-p o) (js-object-private o)
                                           (nth-value 1 (gethash pn (js-object-private o))))
                                      *true* *false*))))
            (:class-private-static (let* ((fn (pop!)) (pn (pop!)) (ctor (peek!)) (kind (first a))
                                          (tbl (object-private-table ctor))
                                          (existing (gethash pn tbl)))
                                     (setf (fn-home fn) ctor)
                                     (put fn "name" (private-method-name kind pn) :enumerable nil :writable nil :configurable t)
                                     (case kind
                                       (:get (setf (gethash pn tbl)
                                                   (list :accessor fn (and existing (fourth existing)))))
                                       (:set (setf (gethash pn tbl)
                                                   (list :accessor (and existing (second existing)) fn)))
                                       (t (setf (gethash pn tbl) (cons :method fn))))))
            (:class-private-static-field (let* ((v (pop!)) (pn (pop!)) (ctor (peek!)))
                                           (setf (gethash pn (object-private-table ctor)) (cons :field v))))
            (:run-static-block (let ((fn (pop!)) (ctor (peek!)))
                                 (setf (fn-home fn) ctor)   ; super refers to the class
                                 (js-call fn ctor '())))
            (:for-in-keys (push! (for-in-key-array (pop!))))
            (:get-iterator (push! (get-iterator (pop!))))
            (:iter-next (push! (iterator-step (pop!))))
            (:iter-step-checked                          ; done-var IT-var -> pushes element VALUE (or undefined)
             (let ((donev (first a)) (itv (second a)))
               (if (js-truthy (env-get-checked env donev))
                   (push! *undefined*)                    ; iterator already exhausted: value is undefined
                   ;; .next() (or reading its result) throwing marks the iterator done
                   ;; per spec (no IteratorClose then) — set done BEFORE the throw escapes.
                   (let ((r (handler-case (iterator-step (env-get-checked env itv))
                              (shuttle-error (e) (env-set env donev *true*) (error e)))))
                     (if (js-truthy (js-get r "done"))
                         (progn (env-set env donev *true*) (push! *undefined*))
                         (push! (js-get r "value")))))))
            (:iter-close-normal                          ; if not done, IteratorClose (normal-completion semantics)
             (let ((donev (first a)) (itv (second a)))
               (unless (js-truthy (env-get-checked env donev))
                 (env-set env donev *true*)
                 (iterator-close-normal (env-get-checked env itv)))))
            (:iter-close-abrupt                          ; unwinding a throw: close swallowing return() errors (leaves stack)
             (let ((donev (first a)) (itv (second a)))
               (unless (js-truthy (env-get-checked env donev))
                 (iterator-close (env-get-checked env itv)))))
            (:iter-rest (let ((it (pop!)) (out '()))
                          (loop (let ((r (iterator-step it)))
                                  (when (js-truthy (js-get r "done")) (return))
                                  (push (js-get r "value") out)))
                          (push! (make-array-object (nreverse out)))))
            (:object-rest (let ((src (pop!)) (taken (first a)))
                            (push! (object-rest-copy-keys src taken))))
            (:object-rest-dyn (let* ((src (pop!)) (excl-arr (pop!))   ; [exclKeys src] -> rest
                                     (taken (array-object-to-list excl-arr)))
                                (push! (object-rest-copy-keys src taken))))
            (:eval-direct
             ;; Direct eval: stack has [evalFn arg0 arg1 ...]. If evalFn is the
             ;; realm's %eval% intrinsic and arg0 is a string, run the code in
             ;; THIS lexical env / this / strict context. Otherwise ordinary call.
             (let* ((args (nreverse (loop repeat (first a) collect (pop!))))
                    (evalfn (pop!)))
               (if (and (boundp '*current-realm*)
                        (eq evalfn (realm-eval-intrinsic *current-realm*))
                        (stringp (first args)))
                   (push! (perform-direct-eval (first args) env this strictp))
                   (push! (js-call evalfn *undefined* args)))))
            (:call (let* ((args (loop repeat (first a) collect (pop!)))
                          (callee (pop!)) (thisv (pop!)))
                     (push! (js-call callee thisv (nreverse args)))))
            (:new (let* ((args (loop repeat (first a) collect (pop!))) (callee (pop!)))
                    (push! (js-construct callee (nreverse args)))))
            (:call-spread (let* ((argsarr (pop!)) (callee (pop!)) (thisv (pop!)))
                            (push! (js-call callee thisv (array-object-to-list argsarr)))))
            (:new-spread (let* ((argsarr (pop!)) (callee (pop!)))
                           (push! (js-construct callee (array-object-to-list argsarr)))))
            ;; LEXICAL-THIS = the enclosing frame's `this`, captured so an arrow
            ;; (:lexical this-mode) resolves `this` to its definition site.
            (:closure (push! (make-js-function (first a) env :lexical-this this)))
            (:genclosure (push! (make-js-function (first a) env :kind :generator :lexical-this this)))
            (:asyncclosure (push! (make-js-function (first a) env :kind :async :lexical-this this)))
            (:asyncgenclosure (push! (make-js-function (first a) env :kind :async-generator :lexical-this this)))
            ;; Named function EXPRESSION: bind its own name (immutable) to itself in
            ;; a fresh env captured as the function's closure scope, so the body can
            ;; reference the function by name even when the outer binding is reassigned.
            ((:named-closure :named-genclosure :named-asyncclosure :named-asyncgenclosure)
             (let* ((fenv (new-env env))
                    (fn (make-js-function (first a)
                                          fenv
                                          :kind (case op
                                                  (:named-genclosure :generator)
                                                  (:named-asyncclosure :async)
                                                  (:named-asyncgenclosure :async-generator))
                                          :lexical-this this)))
               (setf (gethash (second a) (env-vars fenv)) fn)
               (pushnew (second a) (env-nfe fenv) :test #'string=)
               (push! fn)))
            (:yield (push! (gen-yield (pop!))))
            (:yield-star (push! (yield-star-delegate (pop!))))
            (:await (push! (async-await (pop!))))
            (:get-async-iterator (push! (get-async-iterator (pop!))))
            ;; ---- classes ----
            (:make-class (let* ((super (pop!)) (ctor-code (first a)) (derived (second a))
                                (cname (third a)))
                           (push! (build-class ctor-code super derived env cname))))
            (:class-method (let* ((fn (pop!)) (k (pop!)) (ctor (peek!))
                                  (kind (first a)) (static (second a))
                                  (target (if static ctor (js-get ctor "prototype"))))
                             (setf (fn-home fn) target)     ; [[HomeObject]] for super
                             (put fn "name" (js-key-name k) :enumerable nil :writable nil)
                             (case kind
                               (:get (js-define-own-property target (prop-key k)
                                       (list :get fn :accessor t :enumerable nil :configurable t)))
                               (:set (js-define-own-property target (prop-key k)
                                       (list :set fn :accessor t :enumerable nil :configurable t)))
                               (t (js-define-own-property target (prop-key k)
                                    (list :value fn :writable t :enumerable nil :configurable t))))))
            (:class-static-field (let* ((v (pop!)) (k (pop!)) (ctor (peek!)))
                                   (js-define-own-property ctor (prop-key k)
                                     (list :value v :writable t :enumerable t :configurable t))))
            (:super-get (let ((k (pop!)))
                          (let ((base (and (js-object-p home) (js-object-proto home))))
                            (push! (if (js-object-p base) (js-get base k this) *undefined*)))))
            (:super-get-method (let ((k (pop!)))
                                 (let ((base (and (js-object-p home) (js-object-proto home))))
                                   (push! this)            ; thisv
                                   (push! (if (js-object-p base) (js-get base k this) *undefined*)))))
            (:super-call (let ((args (nreverse (loop repeat (first a) collect (pop!)))))
                           (run-super-ctor super-ctor this args fn-obj) (push! this)))
            (:super-call-spread (let ((argsarr (pop!)))
                                  (run-super-ctor super-ctor this (array-object-to-list argsarr) fn-obj) (push! this)))
            (:array (push! (make-array-object (nreverse (loop repeat (first a) collect (pop!))))))
            (:object (push! (make-plain-object
                             (nreverse (loop repeat (first a) collect (let ((v (pop!)) (k (pop!))) (cons k v)))))))
            (:new-object (push! (make-object :proto (%obj-proto))))
            (:new-array (push! (make-array-object '())))
            (:template-object (push! (get-template-object (first a))))
            (:def-prop (let ((v (pop!)) (k (pop!)))     ; obj key val -> obj
                         (js-define-own-property (peek!) (prop-key k)
                           (list :value v :writable t :enumerable t :configurable t))))
            (:def-getter (let ((fn (pop!)) (k (pop!)))  ; obj key fn -> obj
                           (js-define-own-property (peek!) (prop-key k)
                             (list :get fn :accessor t :enumerable t :configurable t))))
            (:def-setter (let ((fn (pop!)) (k (pop!)))
                           (js-define-own-property (peek!) (prop-key k)
                             (list :set fn :accessor t :enumerable t :configurable t))))
            (:set-proto (let ((pv (pop!)))              ; obj protoval -> obj
                          (when (or (js-object-p pv) (eq pv *null*))
                            (setf (js-object-proto (peek!)) pv))))
            (:def-spread (let ((src (pop!)))            ; obj src -> obj (copy own enumerable)
                           (let ((dst (peek!)))
                             (when (or (js-object-p src) (stringp src))
                               (let ((so (to-object src)))
                                 (dolist (k (js-own-keys so))
                                   (let ((d (js-get-own-property so k)))
                                     (when (and d (prop-enumerable d))
                                       (js-set dst k (js-get so k))))))))))
            (:array-spread (let ((iterable (pop!)) (idx (pop!)) (arr (pop!)))  ; arr idx iterable -> newidx
                             (let ((i (truncate (to-number idx))) (it (get-iterator iterable)))
                               (loop (let ((r (iterator-step it)))
                                       (when (js-truthy (js-get r "done")) (return))
                                       (js-set arr (princ-to-string i) (js-get r "value")) (incf i)))
                               (push! (float i 1d0)))))
            (:jmp (setf pc (first a)))
            (:jmp-if-false (unless (js-truthy (pop!)) (setf pc (first a))))
            (:jmp-if-true (when (js-truthy (pop!)) (setf pc (first a))))
            (:and-jmp (if (js-truthy (peek!)) (pop!) (setf pc (first a))))
            (:or-jmp (if (js-truthy (peek!)) (setf pc (first a)) (pop!)))
            (:nullish-jmp (let ((v (peek!)))    ; keep LHS if non-nullish, else eval RHS
                            (if (or (eq v *null*) (eq v *undefined*)) (pop!) (setf pc (first a)))))
            (:ret (return-from %run (pop!)))
            (:throw-op (js-throw (pop!)))
            (t (error "shuttle vm: bad op ~a" op)))))
        (shuttle-error (e)
          (if handlers
              (destructuring-bind (catch-pc saved-sp saved-env) (pop handlers)
                (setf (fill-pointer stack) saved-sp pc catch-pc env saved-env)  ; restore scope
                (vector-push-extend (shuttle-error-value e) stack))   ; thrown value -> catch param
              (error e))))))))
