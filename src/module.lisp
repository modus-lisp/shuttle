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
      (let ((spec (cur-val))) (adv) (opt ";") (list :import spec '()))))
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
    (let ((spec (parse-from-clause)))
      (opt ";")
      (list :import spec (nreverse entries)))))

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
            (spec (parse-from-clause)))
       (opt ";")
       (list :export-star spec as)))

    ;; export { ... };   /   export { ... } from "m";
    ((punct? "{")
     (let* ((pairs (parse-export-list))
            (spec (when (kw? "from") (parse-from-clause))))
       (opt ";")
       (list :export-named pairs spec)))

    ;; export default ...
    ;;
    ;; Parsed in the EXPRESSION forms of function and class, because `export default function(){}`
    ;; is legally anonymous and the declaration forms are not.  A named one still carries its name
    ;; in the node, which is all a bundler needs to know it also binds that name locally.
    ((kw? "default")
     (adv)
     (cond ((kw? "function") (list :export-default (parse-function t)))
           ((async-function-follows-p) (adv) (list :export-default (parse-function t t)))
           ((kw? "class") (list :export-default (parse-class t)))
           (t (prog1 (list :export-default (parse-expr 1)) (opt ";")))))

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
    (let ((*toks* toks) (*escaped-idents* escaped) (*pos* 0) (items '()) (spans '()))
      (loop until (eq (cur-type) :eof)
            do (let ((from *pos*))
                 (push (parse-module-item) items)
                 (push (list (aref starts from) (aref starts *pos*) from *pos*) spans)))
      (values (nreverse items) (nreverse spans) starts))))

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
  (let ((requests '()) (imports '()) (exports '()))
    (flet ((request (spec) (pushnew spec requests :test #'string=)))
      (dolist (it items)
        (case (car it)
          (:import
           (destructuring-bind (spec entries) (rest it)
             (request spec)
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
           (push (make-instance 'export-entry :export-name "default" :local-name "*default*")
                 exports))
          (:export-decl
           (dolist (n (%declared-names (second it)))
             (push (make-instance 'export-entry :export-name n :local-name n) exports))))))
    (values (nreverse requests) (nreverse imports) (nreverse exports))))

(defun parse-module (src)
  "SRC -> a MODULE-RECORD.  Static only: nothing here evaluates, links or instantiates."
  (multiple-value-bind (items spans starts) (parse-module-items src)
    (multiple-value-bind (requests imports exports) (analyse-module items)
      (make-instance 'module-record :source src :items items :spans spans :starts starts
                                    :requests requests :imports imports :exports exports))))
