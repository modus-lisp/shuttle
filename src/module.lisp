;;;; module.lisp — ES modules: the STATIC half, which is the half a bundler needs.
;;;;
;;;; ==================================================================================
;;;; WHY THIS FILE STOPS WHERE IT STOPS
;;;; ==================================================================================
;;;;
;;;; A module has two halves in the spec.  The STATIC half is what a module REQUESTS, what it
;;;; IMPORTS and what it EXPORTS -- all answerable from the source text alone, without running a
;;;; line of it.  The RUNTIME half is live bindings, cyclic evaluation order, the module namespace
;;;; exotic object, and the several ways those interact.
;;;;
;;;; A BUNDLER ONLY EVER NEEDS THE FIRST.  It does not execute the modules it reads: it takes their
;;;; shapes, orders them by dependency, renames what would collide, and emits ONE script for
;;;; somebody else to run.  esbuild never evaluates nostr-tools either.  So this file implements
;;;; the static half completely and the runtime half not at all.
;;;;
;;;; That boundary is deliberate and it is enforced: EVAL-SCRIPT still refuses module syntax rather
;;;; than half-running it.  A half-implemented `import` is worse than none, because it fails at the
;;;; point of USE -- deep in somebody's dependency, at runtime -- instead of at the point of parse.
;;;;
;;;; ==================================================================================
;;;; THE AST, WHICH IS THE SAME SHAPE AS EVERY OTHER NODE HERE
;;;; ==================================================================================
;;;;
;;;;   (:import        specifier entries)   entries: (:default local)
;;;;                                                 (:namespace local)
;;;;                                                 (:named imported local)
;;;;   (:export-named  pairs specifier)     pairs: (local . exported); specifier NIL unless re-export
;;;;   (:export-star   specifier as)        as NIL for `export * from`, a name for `export * as ns from`
;;;;   (:export-default node)
;;;;   (:export-decl   stmt)
;;;;
;;;; A module item that is neither is an ordinary statement, parsed by PARSE-STMT unchanged.

(in-package #:shuttle)

;;; ---- names -------------------------------------------------------------------------------
;;; ModuleExportName is an IdentifierName OR (ES2022) a string literal, which is how a module
;;; exports a name that is not a valid identifier: `export { x as "a-b" }`.

(defun module-export-name ()
  (case (cur-type)
    (:ident (prog1 (cur-val) (adv)))
    (:str   (prog1 (cur-val) (adv)))
    (t (js-throw (make-native-error "SyntaxError" "Expected a module export name")))))

(defun module-local-name ()
  "A binding this module introduces, so an identifier and never a string."
  (if (eq (cur-type) :ident)
      (prog1 (cur-val) (adv))
      (js-throw (make-native-error "SyntaxError" "Expected an identifier"))))

(defun parse-with-clause ()
  "The optional `with { type: \"json\" }` after a module specifier (import attributes).

`with` is contextual here -- it is also the `with` STATEMENT keyword -- so it only counts when a
`{` follows it.  Attribute VALUES must be string literals; keys may be identifiers or strings.
The attributes are recorded and not acted on: this host supports no attribute type at all, so a
non-empty clause is refused at load time rather than quietly ignored, which is what the spec means
by an unsupported attribute."
  (when (and (kw? "with")
             (let ((nx (aref *toks* (1+ *pos*))))
               (and (eq (car nx) :punct) (string= (cdr nx) "{"))))
    (adv) (eat "{")
    (let ((out '()))
      (loop until (punct? "}")
            do (let ((key (case (cur-type)
                            (:ident (prog1 (cur-val) (adv)))
                            (:str (prog1 (cur-val) (adv)))
                            (t (js-throw (make-native-error
                                          "SyntaxError" "Expected an import attribute key"))))))
                 (eat ":")
                 (unless (eq (cur-type) :str)
                   (js-throw (make-native-error
                              "SyntaxError" "An import attribute value must be a string literal")))
                 (push (cons key (cur-val)) out)
                 (adv)
                 (unless (punct? "}") (eat ","))))
      (eat "}")
      (nreverse out))))

(defun parse-from-clause ()
  (unless (kw? "from")
    (js-throw (make-native-error "SyntaxError" "Expected 'from' in a module declaration")))
  (adv)
  (unless (eq (cur-type) :str)
    (js-throw (make-native-error "SyntaxError" "Expected a module specifier string")))
  (prog1 (cur-val) (adv)))

;;; ---- import ------------------------------------------------------------------------------

(defun parse-import-list ()
  "`{ a, b as c, \"d\" as e }` -> ((:named imported local) ...)."
  (eat "{")
  (let ((out '()))
    (loop until (punct? "}")
          do (let ((string-name (eq (cur-type) :str)))
               (let* ((imported (module-export-name))
                      (local (cond ((kw? "as") (adv) (module-local-name))
                                   ;; `import { "x" }` cannot bind: a string is not an identifier,
                                   ;; so the `as` is not optional there the way it is for a name.
                                   (string-name
                                    (js-throw (make-native-error
                                               "SyntaxError"
                                               "A string module export name needs 'as'")))
                                   (t imported))))
                 (push (list :named imported local) out))
               (unless (punct? "}") (eat ","))))
    (eat "}")
    (nreverse out)))

(defun parse-namespace-import ()
  (adv)                                             ; '*'
  (unless (kw? "as")
    (js-throw (make-native-error "SyntaxError" "Expected 'as' after '*' in an import")))
  (adv)
  (list :namespace (module-local-name)))

(defun parse-import-decl ()
  (adv)                                             ; 'import'
  ;; `import "side-effect";` -- no bindings at all, and the one form with no `from`.
  (when (eq (cur-type) :str)
    (return-from parse-import-decl
      (let ((spec (cur-val)))
        (adv)
        (let ((attrs (parse-with-clause))) (opt ";") (list :import spec '() attrs)))))
  (let ((entries '()))
    (cond
      ((punct? "*") (push (parse-namespace-import) entries))
      ((punct? "{") (setf entries (reverse (parse-import-list))))
      (t
       ;; ImportedDefaultBinding, optionally followed by one of the other two forms.
       (push (list :default (module-local-name)) entries)
       (when (opt ",")
         (cond ((punct? "*") (push (parse-namespace-import) entries))
               ((punct? "{") (dolist (e (parse-import-list)) (push e entries)))
               (t (js-throw (make-native-error
                             "SyntaxError"
                             "Expected '*' or '{' after the default import")))))))
    (let* ((spec (parse-from-clause))
           (attrs (parse-with-clause)))
      (opt ";")
      (list :import spec (nreverse entries) attrs))))

;;; ---- export ------------------------------------------------------------------------------

(defun parse-export-list ()
  "`{ a, b as c }` -> ((local . exported) ...)."
  (eat "{")
  (let ((out '()))
    (loop until (punct? "}")
          do (let* ((local (module-export-name))
                    (exported (if (kw? "as") (progn (adv) (module-export-name)) local)))
               (push (cons local exported) out)
               (unless (punct? "}") (eat ","))))
    (eat "}")
    (nreverse out)))

(defun parse-export-decl ()
  (adv)                                             ; 'export'
  (cond
    ;; export * from "m";   /   export * as ns from "m";
    ((punct? "*")
     (adv)
     (let* ((as (when (kw? "as") (adv) (module-export-name)))
            (spec (parse-from-clause))
            (attrs (parse-with-clause)))
       (declare (ignore attrs))
       (opt ";")
       (list :export-star spec as)))

    ;; export { ... };   /   export { ... } from "m";
    ((punct? "{")
     (let* ((pairs (parse-export-list))
            (spec (when (kw? "from") (parse-from-clause)))
            (attrs (and spec (parse-with-clause))))
       (declare (ignore attrs))
       (opt ";")
       (list :export-named pairs spec)))

    ;; export default ...
    ;;
    ;; Parsed in the EXPRESSION forms of function and class, because `export default function(){}`
    ;; is legally anonymous and the declaration forms are not.  A named one still carries its name
    ;; in the node, which is all a bundler needs to know it also binds that name locally.
    ;; THREE different productions wear the same node shape once parsed, and only the parser can
    ;; tell them apart -- `export default function(){}` is a HoistableDeclaration and is callable
    ;; above its own text, while `export default (function(){})` is an AssignmentExpression and
    ;; is in TDZ until the line runs.  After parsing, both are (:func NIL ...).  So the kind is
    ;; recorded here rather than guessed at later.
    ((kw? "default")
     (adv)
     (cond ((kw? "function") (list :export-default (parse-function t) :hoistable))
           ((async-function-follows-p) (adv) (list :export-default (parse-function t t) :hoistable))
           ((kw? "class") (list :export-default (parse-class t) :class))
           (t (prog1 (list :export-default (parse-expr 1) :expression) (opt ";")))))

    ;; export <var|let|const|function|class|async function> ...
    (t (list :export-decl (parse-stmt)))))

;;; ---- module items ------------------------------------------------------------------------

(defun import-declaration-follows-p ()
  "`import` begins a DECLARATION unless it is `import(` (dynamic) or `import.meta`, both of which
are expressions and belong to PARSE-STMT."
  (and (kw? "import")
       (let ((nxt (aref *toks* (1+ *pos*))))
         (not (and (eq (car nxt) :punct)
                   (or (string= (cdr nxt) "(") (string= (cdr nxt) ".")))))))

(defun parse-module-item ()
  (cond ((import-declaration-follows-p) (parse-import-decl))
        ((kw? "export") (parse-export-decl))
        (t (parse-stmt))))

(defun parse-module-items (src)
  "SRC parsed with Module as the goal symbol.

Returns (values ITEMS SPANS STARTS).  SPANS is parallel to ITEMS, each (CHAR-START CHAR-END
TOK-FROM TOK-TO); STARTS is the token-offset vector.  CHAR-END is the start of the NEXT token, so a
span carries its item's trailing whitespace -- which is what makes deleting one leave no ragged
hole.  The token indices are what let the emitter slice `export ` off the front of a declaration
without touching a byte of the declaration itself: the payload begins at (aref starts (1+ from))."
  (multiple-value-bind (toks escaped starts) (tokenize src)
    ;; The Module goal symbol is [+Await]: `await` is a keyword at the top level of a module and
    ;; is never an identifier there, whether or not the module actually uses top-level await.
    (let ((*toks* toks) (*escaped-idents* escaped) (*pos* 0) (*in-async* t)
          (items '()) (spans '()))
      (loop until (eq (cur-type) :eof)
            do (let ((from *pos*))
                 (push (parse-module-item) items)
                 (push (list (aref starts from) (aref starts *pos*) from *pos*) spans)))
      (values (nreverse items) (nreverse spans) starts))))

(defun module-has-tla-p (items)
  "Does a top-level AWAIT appear in ITEMS -- not counting the inside of a nested function, which
has its own await and its own promise?  This is the spec's [[HasTLA]], and it decides whether the
module evaluates synchronously or becomes an async body driven by a promise."
  ;; CAR and CDR, not the list's elements.  A var declarator is a DOTTED pair -- (target . init)
  ;; -- so `const x = await p` is ("x" :await ...) and the :await node is never an element of
  ;; anything.  Walking it as a cons tree is the only shape-independent way to find one.
  (labels ((walk (node)
             (cond
               ((not (consp node)) nil)
               ;; a nested function or class is a different await context, with its own promise
               ;; A nested FUNCTION is a different await context, with its own promise.  A CLASS
               ;; is not: its heritage and its computed member keys are evaluated right here, so
               ;; `class C extends fn(await x) {}` really is a top-level await.  Only the member
               ;; BODIES are elsewhere, and those are :method-func, which stops below anyway.
               ((member (car node) '(:func :genfunc :asyncfunc :asyncgenfunc
                                     :arrow :async-arrow :method-func))
                nil)
               ((member (car node) '(:await :for-await-of)) t)
               (t (or (walk (car node)) (walk (cdr node)))))))
    (some #'walk items)))

(defun span-start (sp) (first sp))
(defun span-end (sp) (second sp))
(defun span-from (sp) (third sp))
(defun span-to (sp) (fourth sp))

;;; ---- the record --------------------------------------------------------------------------
;;;
;;; The spec's ImportEntry and ExportEntry, which are exactly the questions a linker asks.  CLOS
;;; rather than DEFSTRUCT so a running image survives these being redefined.

(defclass import-entry ()
  ((request :initarg :request :reader entry-request
            :documentation "The specifier string this name comes from.")
   (import-name :initarg :import-name :reader entry-import-name
                :documentation "The name in the OTHER module: a string, :default, or :namespace.")
   (local-name :initarg :local-name :reader entry-local-name
               :documentation "The name it is bound to in THIS module.")))

(defclass export-entry ()
  ((export-name :initarg :export-name :initform nil :reader entry-export-name
                :documentation "The name seen by importers; NIL for `export * from`.")
   (request :initarg :request :initform nil :reader entry-request
            :documentation "Non-NIL when this export comes from another module.")
   (import-name :initarg :import-name :initform nil :reader entry-import-name
                :documentation "The name in that other module, or :all for a star re-export.")
   (local-name :initarg :local-name :initform nil :reader entry-local-name
               :documentation "The local binding exported, for a local export.")))

(defclass module-record ()
  ((source :initarg :source :reader module-source
           :documentation "The original text.  The bundler emits from THIS, spliced at spans.")
   (spans :initarg :spans :reader module-spans
          :documentation "(CHAR-START CHAR-END TOK-FROM TOK-TO) per item, parallel to ITEMS.")
   (starts :initarg :starts :reader module-starts
           :documentation "Token -> source offset, so the emitter can cut inside an item.")
   (items :initarg :items :reader module-items)
   (requests :initarg :requests :reader module-requests
             :documentation "Every specifier this module requests, in source order, deduplicated.")
   (request-attrs :initarg :request-attrs :initform nil :reader module-request-attrs
                  :documentation "Specifier -> import attributes, e.g. ((\"./x.json\" . ((\"type\" . \"json\")))).
Attributes are part of a module's IDENTITY, so the loader keys on them too.")
   (imports :initarg :imports :reader module-imports)
   (exports :initarg :exports :reader module-exports)))

(defun %target-names (tgt acc)
  "The names a binding TARGET introduces.  A blind walk for strings would also collect an object
pattern's KEYFORMs, which name properties being read and not bindings being made."
  (cond
    ((stringp tgt) (cons tgt acc))
    ((not (consp tgt)) acc)
    ((eq (car tgt) :apat)
     ;; elem: nil (hole) | TARGET | (:default TARGET EXPR) | (:rest TARGET)
     (dolist (e (second tgt) acc)
       (setf acc (cond ((null e) acc)
                       ((and (consp e) (member (car e) '(:default :rest)))
                        (%target-names (second e) acc))
                       (t (%target-names e acc))))))
    ((eq (car tgt) :opat)
     ;; prop: (KEYFORM TARGET) | (KEYFORM TARGET DEFAULT) | (:rest NAME) -- the binding is second
     ;; in both shapes, which is the one convenient thing about this grammar.
     (dolist (pr (second tgt) acc)
       (setf acc (%target-names (second pr) acc))))
    (t acc)))

(defun %declared-names (stmt)
  "The names an exported DECLARATION binds.  `export const {a, b} = x` exports both."
  (case (car stmt)
    ;; (:var KIND ((target . init) ...)) -- KIND is var/let/const and is not a name.
    (:var (let ((acc '()))
            (dolist (d (third stmt) (nreverse acc))
              (setf acc (%target-names (car d) acc)))))
    ((:func :genfunc :asyncfunc :asyncgenfunc :class)
     (let ((n (second stmt))) (when (stringp n) (list n))))
    (t '())))

(defun analyse-module (items)
  "ITEMS -> (values requests imports exports), the spec's static tables."
  (let ((requests '()) (imports '()) (exports '()) (attrs-of '()))
    (flet ((request (spec &optional attrs)
             (pushnew spec requests :test #'string=)
             (when (and attrs (not (assoc spec attrs-of :test #'string=)))
               (push (cons spec attrs) attrs-of))))
      (dolist (it items)
        (case (car it)
          (:import
           (destructuring-bind (spec entries &optional attrs) (rest it)
             (request spec attrs)
             (dolist (e entries)
               (push (make-instance
                      'import-entry :request spec
                      :import-name (ecase (first e)
                                     (:default :default) (:namespace :namespace)
                                     (:named (second e)))
                      :local-name (if (eq (first e) :named) (third e) (second e)))
                     imports))))
          (:export-named
           (destructuring-bind (pairs spec) (rest it)
             (when spec (request spec))
             (dolist (p pairs)
               (push (if spec
                         (make-instance 'export-entry :export-name (cdr p)
                                                      :request spec :import-name (car p))
                         (make-instance 'export-entry :export-name (cdr p)
                                                      :local-name (car p)))
                     exports))))
          (:export-star
           (destructuring-bind (spec as) (rest it)
             (request spec)
             (push (make-instance 'export-entry :export-name as :request spec :import-name :all)
                   exports)))
          (:export-default
           ;; `export default function f(){}` is a DECLARATION: it binds f in module scope, and f
           ;; is the local name the export refers to.  Only an ANONYMOUS default needs the
           ;; synthetic *default*, a name no source text can collide with.  Getting this wrong
           ;; makes the export resolve to a binding nobody ever creates, which surfaces as
           ;; "Cannot access '*default*' before initialization" -- from a module that plainly
           ;; does define its default.
           (let* ((node (second it))
                  (named (and (member (third it) '(:hoistable :class))
                              (consp node)
                              (member (car node) '(:func :genfunc :asyncfunc :asyncgenfunc :class))
                              (stringp (second node))
                              (second node))))
             (push (make-instance 'export-entry :export-name "default"
                                                :local-name (or named "*default*"))
                   exports)))
          (:export-decl
           (dolist (n (%declared-names (second it)))
             (push (make-instance 'export-entry :export-name n :local-name n) exports))))))
    (values (nreverse requests) (nreverse imports) (nreverse exports) (nreverse attrs-of))))

(defun %module-early-errors (items exports imports)
  "The two early errors a Module has beyond ordinary syntax (spec 16.2.1.6.1):

  * its exported NAMES must be unique -- `export {a}; export {a}` is a SyntaxError, not a
    last-one-wins;
  * every locally-exported name must actually be DECLARED somewhere in the module, so
    `export { nope }` fails at parse rather than resolving to nothing at link time.

Both are static, and the tables to check them are already built."
  (let ((seen '()))
    (dolist (e exports)
      (let ((n (entry-export-name e)))
        (when n
          (when (member n seen :test #'string=)
            (js-throw (make-native-error "SyntaxError"
                                         (format nil "Duplicate export of '~a'" n))))
          (push n seen)))))
  (let ((declared (mapcar #'entry-local-name imports))
        (stmts '()))
    (dolist (it items)
      (case (car it)
        ((:import :export-named :export-star))
        (:export-decl (push (second it) stmts))
        (:export-default
         ;; a named default declares its own name; an anonymous one declares *default*
         (let ((n (second it)))
           (push (if (and (consp n) (stringp (second n))) (second n) "*default*") declared)
           (push "*default*" declared)))
        (t (push it stmts))))
    (setf stmts (nreverse stmts))
    ;; COLLECT-VAR-NAMES reaches nested blocks, which matters: `{ var x } export {x}` is legal
    ;; because a var is module-scoped wherever it is written.
    (setf declared (append declared
                           (ignore-errors (collect-var-names (list :block stmts)))
                           (ignore-errors (block-lexical-names stmts))
                           (loop for st in stmts
                                 when (and (consp st)
                                           (member (car st) '(:func :genfunc :asyncfunc
                                                              :asyncgenfunc :class))
                                           (stringp (second st)))
                                   collect (second st))))
    (dolist (e exports)
      (let ((l (entry-local-name e)))
        (when (and l (not (member l declared :test #'string=)))
          (js-throw (make-native-error
                     "SyntaxError"
                     (format nil "Export '~a' is not defined in module" l))))))))

(defun parse-module (src)
  "SRC -> a MODULE-RECORD.  Static only: nothing here evaluates, links or instantiates."
  (multiple-value-bind (items spans starts) (parse-module-items src)
    (multiple-value-bind (requests imports exports attrs-of) (analyse-module items)
      (%module-early-errors items exports imports)
      (make-instance 'module-record :source src :items items :spans spans :starts starts
                                    :requests requests :imports imports :exports exports
                                    :request-attrs attrs-of))))
