;;;; module-runtime.lisp — ES modules, the RUNTIME half: link, evaluate, and live bindings.
;;;;
;;;; ==================================================================================
;;;; WHAT THE STATIC HALF COULD NOT DO
;;;; ==================================================================================
;;;;
;;;; module.lisp answers what a module requests, imports and exports -- everything readable from
;;;; the source text, which is all a BUNDLER needs.  This is the other half: actually running the
;;;; things.  It is where the parts that cannot be read off the page live --
;;;;
;;;;   LIVE BINDINGS.  `import { n }` does not copy n.  It binds a name to somebody else's
;;;;   binding, and reading it later sees whatever that binding holds now.  The bundler had to
;;;;   rewrite references to property reads to fake this; here it is real, via an INDIRECT-BINDING
;;;;   stored in the environment that ENV-GET dereferences.
;;;;
;;;;   CYCLES.  a imports b imports a is legal.  Linking and evaluation are both depth-first with
;;;;   strongly-connected components (the spec's index / ancestor-index pair is Tarjan's), so a
;;;;   cycle links as a unit and evaluates once.  A binding read before its module has run throws
;;;;   -- TDZ across a module boundary, which is exactly what a cycle exposes.
;;;;
;;;;   NAMESPACES.  `import * as ns` is not an ordinary object: its keys are sorted, its
;;;;   properties are non-configurable, writes fail, and reading an uninitialised export throws.
;;;;
;;;; ==================================================================================
;;;; THE HOST OWNS RESOLUTION, AND THAT IS NOT A DETAIL
;;;; ==================================================================================
;;;;
;;;; shuttle is embedded.  It has no filesystem, no URL semantics, and no opinion about what
;;;; "./x.js" means -- weft will answer that over HTTP, the bundler answers it with node
;;;; resolution, test262 answers it with a sibling file.  So a MODULE-HOST supplies two functions,
;;;; resolve and load, and the engine supplies everything downstream of them.
;;;;
;;;; NOT IMPLEMENTED, deliberately and visibly: top-level await.  An `await` at module top level
;;;; is a SyntaxError here rather than a hang or a wrong answer, and the evaluation algorithm
;;;; below is the pre-TLA one -- correct for every module that is not async, which is the whole
;;;; language minus that feature.

(in-package #:shuttle)

;;; ---- reading files, and joining paths the way a specifier means them -----------------------
;;;
;;; These live here rather than in the bundler because the FILE MODULE HOST below needs them and
;;; core cannot depend on a system that depends on core.  CL:MERGE-PATHNAMES keeps "./" and "../"
;;; as literal components -- it produces "/a/b/./c", which PROBE-FILE then does not find -- so a
;;; module specifier gets POSIX joining rather than pathname arithmetic.

(defun slurp-file (path)
  (with-open-file (s path :external-format :utf-8)
    (let ((b (make-string (file-length s)))) (subseq b 0 (read-sequence b s)))))

(defun %split-slash (s)
  (loop with start = 0
        for p = (position #\/ s :start start)
        collect (subseq s start p)
        while p do (setf start (1+ p))))

(defun %probe-native (path)
  "PROBE-FILE on a POSIX path taken LITERALLY, never as a CL pathname pattern.

A module specifier is arbitrary user text: `import(somePromise)` stringifies to \"[object
Promise]\", and PROBE-FILE reads the brackets as a wild pathname and SIGNALS rather than
answering NIL.  A host that crashes on a specifier it merely cannot resolve is worse than one
that rejects it."
  (ignore-errors (probe-file (sb-ext:parse-native-namestring path))))

(defun %norm-join (dir spec)
  "DIR + SPEC -> a normalised absolute namestring.

An ABSOLUTE spec ignores DIR, which is what a leading slash means everywhere else and what the
file host needs when it is handed a full path as the entry key."
  (when (and (plusp (length spec)) (char= (char spec 0) #\/))
    (setf dir ""))
  (let ((segs '()))
    (dolist (seg (append (%split-slash dir) (%split-slash spec)))
      (cond ((or (string= seg "") (string= seg ".")))
            ((string= seg "..") (when segs (pop segs)))
            (t (push seg segs))))
    (format nil "/~{~a~^/~}" (nreverse segs))))

;;; ---- the host seam -------------------------------------------------------------------------

(defclass module-host ()
  ((resolve :initarg :resolve :reader host-resolve
            :documentation "(specifier referrer-key) -> a key, or NIL if unresolvable.")
   (loader :initarg :loader :reader host-loader
           :documentation "key -> source text, or NIL.")
   (registry :initform (make-hash-table :test 'equal) :reader host-registry
             :documentation "key -> SOURCE-TEXT-MODULE.  One module per key, per host.")))

(defvar *module-host* nil "The MODULE-HOST in force for the current load.")

(defclass source-text-module ()
  ((key :initarg :key :reader mod-key)
   (record :initarg :record :reader mod-record)
   (realm :initarg :realm :reader mod-realm)
   (status :initform :unlinked :accessor mod-status)   ; :unlinked :linking :linked :evaluating
                                                       ; :evaluated
   (env :initform nil :accessor mod-env)
   (namespace :initform nil :accessor mod-namespace)
   (error-value :initform nil :accessor mod-error-value)
   (errored :initform nil :accessor mod-errored-p)
   (dfs-index :initform nil :accessor mod-dfs-index)
   (dfs-ancestor :initform nil :accessor mod-dfs-ancestor)
   ;; THE MODULE CARRIES ITS HOST.  *MODULE-HOST* is a dynamic binding, and a dynamic binding is
   ;; gone by the time an async function's continuation runs -- so a deferred `import()` inside
   ;; `await` would find no host at all.  Whoever loaded this module is the right answer forever.
   (host :initarg :host :initform nil :reader mod-host)
   ;; A JSON MODULE is not source text: it has exactly one export, "default", holding the parsed
   ;; value, and no body to run.  Everything downstream works unchanged because its RECORD says
   ;; so -- one export entry, no requests, no imports.
   (json-value :initarg :json-value :initform nil :reader mod-json-value)
   ;; ---- top-level await.  A module with TLA does not finish when its body returns: its body
   ;; IS a promise, and everything importing it has to wait.  These are the spec's slots for
   ;; that, and the reason evaluation stops being a simple depth-first walk.
   (has-tla :initform nil :accessor mod-has-tla)
   (async-evaluation :initform nil :accessor mod-async-evaluation)  ; NIL or an ordinal
   (top-level-capability :initform nil :accessor mod-top-capability)
   (async-parents :initform nil :accessor mod-async-parents)
   (pending-deps :initform 0 :accessor mod-pending-deps)
   (cycle-root :initform nil :accessor mod-cycle-root)
   (meta :initform nil :accessor mod-meta)
   (deps :initform nil :accessor mod-deps)))           ; specifier -> module

(defun %mod-error (kind fmt &rest args)
  (js-throw (make-native-error kind (apply #'format nil fmt args))))

;;; ---- loading -------------------------------------------------------------------------------

(defun %json-module-record ()
  "The record a JSON module presents: one export named \"default\", nothing else."
  (make-instance 'module-record
                 :source "" :items '() :spans '() :starts (vector 0)
                 :requests '() :imports '()
                 :exports (list (make-instance 'export-entry
                                               :export-name "default" :local-name "*default*"))))

(defun %attr (attrs name)
  (cdr (assoc name attrs :test #'string=)))

(defun resolve-imported-module (referrer specifier &optional attrs)
  "HostResolveImportedModule: the same (referrer, specifier, attributes) must always give the same
module.  ATTRIBUTES ARE PART OF IDENTITY -- the same file imported as JSON and as source is two
different modules -- so the registry key carries the type."
  (let* ((host (or (and referrer (mod-host referrer))
                   *module-host*
                   (and (boundp '*current-realm*) *current-realm*
                        (realm-module-host *current-realm*))
                   (%mod-error "TypeError" "no module host is installed")))
         (type (%attr attrs "type"))
         (key (funcall (host-resolve host) specifier (and referrer (mod-key referrer)))))
    (unless key
      (%mod-error "TypeError" "Cannot resolve module ~s~@[ imported by ~a~]"
                  specifier (and referrer (mod-key referrer))))
    (when (and type (not (string= type "json")))
      (%mod-error "TypeError" "Unsupported import attribute type ~s for ~a" type key))
    (let ((rkey (if type (concatenate 'string key (string #\Nul) "type=" type) key)))
      (or (gethash rkey (host-registry host))
          (let ((src (funcall (host-loader host) key)))
            (unless src (%mod-error "TypeError" "Cannot load module ~a" key))
            (let ((m (if (equal type "json")
                         (make-instance 'source-text-module
                                        :key rkey :realm *current-realm* :host host
                                        :record (%json-module-record)
                                        :json-value (parse-json-text src))
                         (let ((mm (make-instance 'source-text-module
                                                  :key key :realm *current-realm* :host host
                                                  :record (parse-module src))))
                           (setf (mod-has-tla mm)
                                 (module-has-tla-p (module-items (mod-record mm))))
                           mm))))
              (setf (gethash rkey (host-registry host)) m)
              m))))))

(defun parse-json-text (text)
  "JSON source -> a JS value, using the engine's own parser.  A JSON module whose text does not
parse is a SyntaxError at load, which is where the spec puts it."
  (let ((p (%make-jparse :str text :pos 0 :len (length text))))
    (prog1 (json-parse-value p)
      (jp-skip-ws p)
      (unless (jp-eof-p p)
        (js-throw (make-native-error "SyntaxError" "Unexpected trailing content in JSON module"))))))

(defun %mod-dep (m specifier)
  (or (cdr (assoc specifier (mod-deps m) :test #'string=))
      (let ((dep (resolve-imported-module
                  m specifier
                  (cdr (assoc specifier (module-request-attrs (mod-record m)) :test #'string=)))))
        (push (cons specifier dep) (mod-deps m))
        dep)))

;;; ---- ResolveExport -------------------------------------------------------------------------

(defun resolve-export (m export-name &optional resolve-set)
  "Where does M's export EXPORT-NAME actually live?

Returns (values MODULE LOCAL-NAME) for a real binding, :NAMESPACE for `export * as ns`,
:AMBIGUOUS when two star exports disagree, or NIL when there is no such export.

RESOLVE-SET is the spec's cycle guard: a re-export loop returns NIL rather than spinning."
  (let ((seen (assoc m resolve-set)))
    (when (and seen (member export-name (cdr seen) :test #'string=))
      (return-from resolve-export nil))          ; already asking this question; a cycle
    (if seen
        (push export-name (cdr seen))
        (push (cons m (list export-name)) resolve-set)))
  (let ((rec (mod-record m)))
    ;; 1. a binding this module declares itself
    (dolist (e (module-exports rec))
      (when (and (entry-local-name e) (equal (entry-export-name e) export-name))
        ;; ...unless that binding IS a namespace import.  `import * as foo from "./x.js";
        ;; export { foo }` exports x's namespace, and it has to resolve THROUGH to x -- otherwise
        ;; two modules doing exactly that, of the same x, look like two different bindings and a
        ;; star-export of both is wrongly ambiguous.  It is the same namespace object either way.
        (let ((via (find-if (lambda (ie) (equal (entry-local-name ie) (entry-local-name e)))
                            (module-imports rec))))
          (return-from resolve-export
            (cond
              ((null via) (values m (entry-local-name e)))
              ;; `import * as foo from x; export { foo }` exports x's NAMESPACE...
              ((eq (entry-import-name via) :namespace)
               (values (%mod-dep m (entry-request via)) :namespace))
              ;; ...and `import { foo } from x; export { foo }` exports x's BINDING.  Either way
              ;; it has to resolve through, or two modules re-exporting the same thing this way
              ;; look like two different bindings and a star-export of both is wrongly ambiguous.
              (t (resolve-export (%mod-dep m (entry-request via))
                                 (if (eq (entry-import-name via) :default)
                                     "default" (entry-import-name via))
                                 resolve-set)))))))
    ;; 2. `export {x} from`, and `export * as ns from` which resolves to a namespace
    (dolist (e (module-exports rec))
      (when (and (entry-request e) (equal (entry-export-name e) export-name))
        (let ((dep (%mod-dep m (entry-request e))))
          (return-from resolve-export
            (if (eq (entry-import-name e) :all)
                (values dep :namespace)
                (resolve-export dep (entry-import-name e) resolve-set))))))
    ;; 3. `export * from` -- every star, and they must agree
    ;;    "default" is deliberately never provided by a star export.
    (unless (string= export-name "default")
      (let ((found nil) (found-name nil))
        (dolist (e (module-exports rec))
          (when (and (eq (entry-import-name e) :all) (null (entry-export-name e)))
            (let ((dep (%mod-dep m (entry-request e))))
              (multiple-value-bind (rm rn) (resolve-export dep export-name resolve-set)
                (cond ((eq rm :ambiguous) (return-from resolve-export :ambiguous))
                      ((null rm))
                      ((null found) (setf found rm found-name rn))
                      ;; the same binding reached twice by different paths is not ambiguous
                      ((not (and (eq found rm) (equal found-name rn)))
                       (return-from resolve-export :ambiguous)))))))
        (when found (return-from resolve-export (values found found-name)))))
    nil))

;;; ---- the module namespace exotic object ----------------------------------------------------

(defun module-exported-names (m &optional export-star-set)
  "Every name M exports, sorted, with star re-exports flattened."
  (when (member m export-star-set) (return-from module-exported-names '()))
  (push m export-star-set)
  (let ((names '()) (rec (mod-record m)))
    (dolist (e (module-exports rec))
      (cond ((entry-export-name e) (pushnew (entry-export-name e) names :test #'string=))
            ((eq (entry-import-name e) :all)
             (dolist (n (module-exported-names (%mod-dep m (entry-request e)) export-star-set))
               (unless (string= n "default") (pushnew n names :test #'string=))))))
    (sort names #'string<)))

(defun namespace-object (m)
  "M's namespace: a module namespace exotic object (spec 10.4.6), not an ordinary one.

Every internal method is overridden, and the shape they make is deliberately hostile to being
treated as a plain object -- keys sorted, prototype null and unchangeable, not extensible, writes
and deletes refused, and a read of an export whose module has not evaluated THROWS rather than
giving undefined.  Symbol keys fall through to ordinary behaviour, which is how @@toStringTag can
be a real own property saying \"Module\"."
  (or (mod-namespace m)
      (let* ((realm (or (mod-realm m) *current-realm*))
             ;; An ambiguous name is OMITTED from the namespace -- `'both' in ns` is false --
             ;; rather than present and throwing.  RESOLVE-EXPORT says :AMBIGUOUS, which is
             ;; truthy, so testing it for truth alone would keep exactly the wrong ones.
             (names (remove-if-not (lambda (n)
                                     (let ((r (resolve-export m n)))
                                       (and r (not (eq r :ambiguous)))))
                                   (module-exported-names m)))
             (obj nil))
        ;; PROP-KEY first: `ns[0]` arrives as a number, and a module really can export the name
        ;; "0" (export { x as "0" }), so comparing the raw key would miss it.
        (flet ((exported-p (key)
                 (let ((k (and (not (js-symbol-p key)) (prop-key key))))
                   (and (stringp k) (member k names :test #'string=)))))
          (setf obj
                (make-host-object
                 realm :proto *null*
                 :get-proto (lambda (o) (declare (ignore o)) *null*)
                 ;; [[SetPrototypeOf]] accepts only the prototype it already has.  A LISP
                 ;; boolean, because that is what ORDINARY-SET-PROTO returns and what callers
                 ;; test -- unlike [[Delete]] next door, which really does return a JS one.
                 :set-proto (lambda (o v) (declare (ignore o)) (and (eq v *null*) t))
                 :is-extensible (lambda (o) (declare (ignore o)) nil)
                 :prevent-extensions (lambda (o) (declare (ignore o)) t)
                 :get (lambda (o key &optional receiver)
                        (declare (ignore receiver))
                        (if (exported-p key) (namespace-read m (prop-key key)) (ordinary-get o key)))
                 :set (lambda (o key v &optional receiver)
                        (declare (ignore o key v receiver))
                        *false*)                       ; a namespace is never writable
                 ;; ORDINARY-HAS returns a Lisp boolean; match it rather than the JS one.
                 :has (lambda (o key)
                        (cond ((exported-p key) t)
                              ((js-symbol-p key) (ordinary-has o key))
                              (t nil)))
                 :delete (lambda (o key)
                           (if (exported-p key) *false*
                               (if (js-symbol-p key) (ordinary-delete o key) *true*)))
                 ;; Without GET-OWN-PROPERTY, OWN-KEYS lists names that ordinary
                 ;; [[GetOwnProperty]] then fails to find, and Object.keys sees nothing.
                 ;; The odd attribute is real: a namespace property is writable TRUE even
                 ;; though [[Set]] always fails.
                 :get-own-property
                 (lambda (o key)
                   (if (exported-p key)
                       (make-prop :value (namespace-read m (prop-key key))
                                  :writable t :enumerable t :configurable nil)
                       (and (js-symbol-p key) (props-get o (prop-key key)))))
                 ;; A define is allowed only if it asks for exactly what is already there.
                 :define-own-property
                 (lambda (o key desc)
                   (cond
                     ((js-symbol-p key) (ordinary-define-own-property o key desc))
                     ((not (exported-p key)) nil)
                     ((or (getf desc :get) (getf desc :set) (getf desc :accessor)) nil)
                     ((and (present-p desc :configurable) (getf desc :configurable)) nil)
                     ((and (present-p desc :enumerable) (not (getf desc :enumerable))) nil)
                     ((and (present-p desc :writable) (not (getf desc :writable))) nil)
                     ((present-p desc :value)
                      (same-value (getf desc :value) (namespace-read m (prop-key key))))
                     (t t)))
                 :own-keys (lambda (o)
                             ;; string exports first, sorted, then the symbol keys -- which is
                             ;; the spec's order and the reason own-property-keys-sort exists.
                             (append (copy-list names)
                                     (remove-if-not #'js-symbol-p (ordinary-own-keys o))))))
          ;; @@toStringTag is an ORDINARY own property here, which is why the traps above hand
          ;; symbol keys back to ordinary behaviour instead of answering for them.
          (let ((tag (well-known-symbol "toStringTag")))
            (when tag
              (put obj tag "Module" :enumerable nil :writable nil :configurable nil)))
          ;; The STRUCT SLOT too, not only the trap.  Ordinary [[DefineOwnProperty]] -- which the
          ;; symbol keys above are handed to -- reads the slot, so with the trap alone a
          ;; namespace would happily accept a brand-new symbol property while reporting itself
          ;; as not extensible.  Set after @@toStringTag, which has to go on first.
          (setf (js-object-extensible obj) nil)
          (setf (mod-namespace m) obj)))))

(defun namespace-read (m name)
  (multiple-value-bind (tm tn) (resolve-export m name)
    (cond ((eq tm :namespace) (namespace-object tn))
          ((null tm) *undefined*)
          ((eq tn :namespace) (namespace-object tm))
          (t (let ((env (mod-env tm)))
               (unless env
                 (%mod-error "ReferenceError" "Cannot access '~a' before initialization" name))
               (multiple-value-bind (v p) (gethash tn (env-vars env))
                 (cond ((not p)
                        (%mod-error "ReferenceError" "Cannot access '~a' before initialization" name))
                       ((eq v *tdz*)
                        (%mod-error "ReferenceError" "Cannot access '~a' before initialization" name))
                       ((indirect-binding-p v) (deref-indirect v 0))
                       (t v))))))))

(defun deref-indirect (ib depth)
  (when (> depth *indirect-depth-limit*)
    (%mod-error "ReferenceError" "circular import binding for '~a'" (ib-name ib)))
  (let* ((m (ib-module ib))
         (env (mod-env m)))
    (unless env
      (%mod-error "ReferenceError" "Cannot access '~a' before initialization" (ib-name ib)))
    (multiple-value-bind (v p) (gethash (ib-name ib) (env-vars env))
      (cond ((not p) (%mod-error "ReferenceError" "Cannot access '~a' before initialization"
                                 (ib-name ib)))
            ((eq v *tdz*) (%mod-error "ReferenceError" "Cannot access '~a' before initialization"
                                      (ib-name ib)))
            ((indirect-binding-p v) (deref-indirect v (1+ depth)))
            (t v)))))

;;; ---- the module body, as statements the compiler already understands -----------------------

(defun module-body-statements (rec)
  "Module items minus the declarations that are linking's business, with `export` peeled off the
ones that also declare something.  `export default <expr>` becomes a const binding of *default*,
a name no source text can collide with."
  (let ((out '()))
    (when (some (lambda (it)
                  (and (eq (car it) :export-default)
                       (eq (third it) :hoistable)
                       (not (stringp (second (second it))))))
                (module-items rec))
      ;; The hoisted anonymous default exists before the first statement, so its name is set
      ;; there too -- code above the declaration can already call it and read .name.
      (push (list :name-default) out))
    (dolist (item (module-items rec) (nreverse out))
      (case (car item)
        ((:import :export-named :export-star))          ; linking handled these
        (:export-decl (push (second item) out))
        (:export-default
         (let ((node (second item)) (kind (third item)))
           (cond
             ;; a NAMED default is a declaration: it binds its own name too
             ((and (member kind '(:hoistable :class)) (consp node) (stringp (second node)))
              (push node out))
             ;; An ANONYMOUS HoistableDeclaration is hoisted and callable above its own text,
             ;; exactly like `function f(){}`.  Giving it the synthetic name makes the ordinary
             ;; hoisting path do that for free.  A class and an expression are NOT hoisted and
             ;; keep the const, which leaves them in TDZ until the line runs -- which is the
             ;; difference test262 checks between `export default function(){}` and
             ;; `export default (function(){})`.
             ((eq kind :hoistable)
              (push (list* (car node) "*default*" (cddr node)) out))
             (t
              (push (list :var "const" (list (cons "*default*" node))) out)
              (push (list :name-default) out)))))
        (t (push item out))))))

;;; ---- linking -------------------------------------------------------------------------------

(defun initialize-environment (m)
  "Create M's environment and its import bindings.  Every indirect export must resolve here, which
is where `export {nope} from './x.js'` becomes a SyntaxError rather than an undefined at runtime."
  (let ((rec (mod-record m)))
    ;; indirect exports must resolve, per InitializeEnvironment step 2
    (dolist (e (module-exports rec))
      (when (and (entry-request e) (entry-export-name e) (not (eq (entry-import-name e) :all)))
        (let ((r (resolve-export m (entry-export-name e))))
          (cond ((eq r :ambiguous)
                 (%mod-error "SyntaxError" "Ambiguous export '~a' in ~a"
                             (entry-export-name e) (mod-key m)))
                ((null r)
                 (%mod-error "SyntaxError" "Module ~a has no export named '~a'"
                             (entry-request e) (entry-import-name e)))))))
    (let ((env (new-env (realm-global-env (or (mod-realm m) *current-realm*)))))
      (setf (env-module env) t)                  ; var scope stops here, not at globalThis
      (setf (mod-env m) env)
      (when (mod-json-value m)
        ;; The whole of a JSON module: one binding, already evaluated.
        (setf (gethash "*default*" (env-vars env)) (mod-json-value m)))
      ;; ModuleDeclarationInstantiation steps 9-11: the module's OWN bindings exist before any
      ;; body runs -- vars as undefined, lexicals in TDZ.  A cycle makes this observable: the
      ;; other module in the loop reads these names while this one has not evaluated a line.
      (let* ((stmts (module-body-statements (mod-record m)))
             (body (list :block stmts)))
        (dolist (n (collect-var-names body))
          (unless (nth-value 1 (gethash n (env-vars env)))
            (setf (gethash n (env-vars env)) *undefined*)))
        (dolist (n (block-lexical-names stmts))
          (unless (nth-value 1 (gethash n (env-vars env)))
            (setf (gethash n (env-vars env)) *tdz*))))
      (dolist (ie (module-imports rec))
        (let ((dep (%mod-dep m (entry-request ie))))
          (if (eq (entry-import-name ie) :namespace)
              ;; Immutable, like every import: `import * as ns` then `ns = null` is a TypeError.
              ;; It holds the namespace object directly rather than an indirect binding, so the
              ;; immutability has to be recorded separately.
              (progn
                (setf (gethash (entry-local-name ie) (env-vars env)) (namespace-object dep))
                (pushnew (entry-local-name ie) (env-consts env) :test #'string=))
              (let ((want (if (eq (entry-import-name ie) :default) "default" (entry-import-name ie))))
                (multiple-value-bind (tm tn) (resolve-export dep want)
                  (cond
                    ((eq tm :ambiguous)
                     (%mod-error "SyntaxError" "Ambiguous import '~a' from ~a" want (mod-key dep)))
                    ((null tm)
                     (%mod-error "SyntaxError" "Module ~a has no export named '~a'"
                                 (mod-key dep) want))
                    ((eq tn :namespace)
                     (setf (gethash (entry-local-name ie) (env-vars env)) (namespace-object tm)))
                    (t
                     ;; THE LIVE BINDING.  Not a copy of tm's value -- a pointer to tm's binding,
                     ;; dereferenced by ENV-GET every time somebody reads this name.
                     (setf (gethash (entry-local-name ie) (env-vars env))
                           (make-indirect-binding :module tm :name tn)))))))))
      env)))

(defun link-module (m)
  (let ((stack '()) (index 0))
    (labels
        ((inner (m idx)
           (when (member (mod-status m) '(:linked :evaluating :evaluated))
             (return-from inner idx))
           (when (eq (mod-status m) :linking) (return-from inner idx))
           (setf (mod-status m) :linking
                 (mod-dfs-index m) idx
                 (mod-dfs-ancestor m) idx)
           (incf idx)
           (push m stack)
           (dolist (spec (module-requests (mod-record m)))
             (let ((dep (%mod-dep m spec)))
               (setf idx (inner dep idx))
               (when (eq (mod-status dep) :linking)
                 (setf (mod-dfs-ancestor m)
                       (min (mod-dfs-ancestor m) (mod-dfs-ancestor dep))))))
           (initialize-environment m)
           ;; A strongly-connected component links as one unit: everything down to M on the
           ;; stack becomes :linked together, because none of them is usable without the rest.
           (when (= (mod-dfs-ancestor m) (mod-dfs-index m))
             (loop for other = (pop stack)
                   do (setf (mod-status other) :linked)
                   until (eq other m)))
           idx))
      (inner m index))
    m))

;;; ---- evaluation ----------------------------------------------------------------------------

;; *CURRENT-MODULE* is declared in vm.lisp, which needs it for the two module opcodes.  It is
;; bound while a module BODY runs; a function defined in that body captures it separately, so a
;; deferred import() still knows where it came from.

(defun %dynamic-import-now (specifier)
  "import(): resolve, link, evaluate, and hand back the namespace.  Synchronous because the host
loader is; the VM wraps the result in a promise either way, so a fetching host can settle it late
without any of this changing."
  (let* ((*module-host* (or (and *current-module* (mod-host *current-module*))
                            *module-host*
                            (and (boundp '*current-realm*) *current-realm*
                                 (realm-module-host *current-realm*))))
         (*current-realm* (or (and *current-module* (mod-realm *current-module*)) *current-realm*))
         (m (resolve-imported-module *current-module* specifier)))
    (link-module m)
    (let ((p (evaluate-module m)))
      ;; Evaluation is a promise now, and with no I/O every await settles through the microtask
      ;; queue -- so draining it is what "wait for the graph" means here.  A promise still pending
      ;; afterwards is a module awaiting something nothing will ever resolve, and saying so is
      ;; better than returning a namespace whose bindings were never initialised.
      (drain-microtasks)
      (case (promise-state p)
        (:rejected (js-throw (promise-value p)))
        (:pending (%mod-error "Error" "module ~a is still awaiting: nothing will settle it"
                              (mod-key m)))))
    (namespace-object m)))

(defun %import-meta-object ()
  "import.meta -- a plain, extensible, module-specific object.  `url` is the host's key for the
module, which is what a filesystem host can honestly say."
  (let ((m *current-module*))
    (unless m
      (%mod-error "SyntaxError" "Cannot use 'import.meta' outside a module"))
    (or (mod-meta m)
        (setf (mod-meta m)
              (let ((o (make-object :proto (%obj-proto))))
                (put o "url" (mod-key m) :enumerable t :writable t :configurable t)
                o)))))

(defun %run-module-body (m)
  "Run M's body.  Returns a PROMISE when M has top-level await, NIL otherwise.

A TLA body is compiled and driven as an async function -- the same coroutine machinery any
`async function` uses -- except that it runs in the MODULE's own environment rather than a fresh
child, because linking already built that environment and the exports are read out of it."
  (let* ((rec (mod-record m))
         (stmts (module-body-statements rec))
         ;; MODULE CODE IS ALWAYS STRICT, with no directive to say so.  Compiling it sloppy is
         ;; not a small difference: a failed [[Set]] or [[Delete]] silently succeeds instead of
         ;; throwing, `this` at the top is wrong, and an assignment to an undeclared name quietly
         ;; creates a global.  Every one of those reads as a module bug and is not one.
         (realm (or (mod-realm m) *current-realm*)))
    (if (mod-has-tla m)
        (let ((code (let ((*strict* t) (*in-async* t))
                      (compile-fn-split nil '() (list :block stmts)))))
          (let ((*current-realm* realm) (*current-module* m))
            (make-async-function-object code (env-parent (mod-env m)) *undefined* '() nil
                                        (mod-env m))))
        (let ((code (let ((*strict* t)) (compile-fn nil '() (list :block stmts) t))))
          (let ((*current-realm* realm) (*current-module* m))
            (run code (mod-env m) *undefined*))
          nil))))

(defvar *async-eval-counter* 0
  "Increasing ordinal for [[AsyncEvaluation]], which the spec uses to run ready ancestors in the
order they became async rather than in whatever order they were gathered.")

(defun %settle-top (m ok value)
  (let ((cap (mod-top-capability m)))
    (when cap
      (if ok (promise-fulfill cap *undefined*) (promise-reject-internal cap value)))))

(defun %execute-module (m)
  "ExecuteModule for a SYNCHRONOUS module: run the body, let an error propagate."
  (%run-module-body m))

(defun %execute-async-module (m)
  "ExecuteAsyncModule: start the body and hang the module's completion off its promise."
  (let ((p (%run-module-body m)))
    (if (promisep p)
        (promise-then p
                      (lambda (v) (declare (ignore v)) (%async-module-fulfilled m))
                      (lambda (e) (%async-module-rejected m e)))
        ;; a module marked HasTLA whose body somehow finished synchronously
        (%async-module-fulfilled m))))

(defun %gather-available-ancestors (m acc)
  "Every async parent of M whose last outstanding dependency was M."
  (dolist (parent (reverse (mod-async-parents m)) acc)
    (unless (or (member parent acc)
                (and (mod-cycle-root parent) (mod-errored-p (mod-cycle-root parent))))
      (decf (mod-pending-deps parent))
      (when (zerop (mod-pending-deps parent))
        (push parent acc)
        (unless (mod-has-tla parent)
          (setf acc (%gather-available-ancestors parent acc))))))
  acc)

(defun %async-module-fulfilled (m)
  (unless (eq (mod-status m) :evaluated)
    (setf (mod-async-evaluation m) nil
          (mod-status m) :evaluated)
    (%settle-top m t nil)
    ;; Ancestors that were only waiting on M can run now -- in the order they BECAME async,
    ;; which is what the ordinal is for.
    (let ((ready (sort (%gather-available-ancestors m '())
                       #'< :key (lambda (x) (or (mod-async-evaluation x) 0)))))
      (dolist (parent ready)
        (cond
          ((eq (mod-status parent) :evaluated))
          ((mod-has-tla parent) (%execute-async-module parent))
          (t (handler-case
                 (progn (%execute-module parent)
                        (setf (mod-async-evaluation parent) nil
                              (mod-status parent) :evaluated)
                        (%settle-top parent t nil))
               (shuttle-error (e) (%async-module-rejected parent (shuttle-error-value e))))))))))

(defun %async-module-rejected (m error)
  (unless (eq (mod-status m) :evaluated)
    (setf (mod-errored-p m) t
          (mod-error-value m) error
          (mod-status m) :evaluated)
    (dolist (parent (mod-async-parents m)) (%async-module-rejected parent error))
    (%settle-top m nil error)))

(defun %inner-module-evaluation (m stack idx)
  (when (member (mod-status m) '(:evaluating-async :evaluated))
    (when (mod-errored-p m) (js-throw (mod-error-value m)))
    (return-from %inner-module-evaluation idx))
  (when (eq (mod-status m) :evaluating) (return-from %inner-module-evaluation idx))
  (unless (eq (mod-status m) :linked)
    (%mod-error "TypeError" "module ~a is not linked" (mod-key m)))
  (setf (mod-status m) :evaluating
        (mod-dfs-index m) idx
        (mod-dfs-ancestor m) idx
        (mod-pending-deps m) 0)
  (incf idx)
  (push m (car stack))
  (dolist (spec (module-requests (mod-record m)))
    (let ((dep (%mod-dep m spec)))
      (setf idx (%inner-module-evaluation dep stack idx))
      (if (eq (mod-status dep) :evaluating)
          (setf (mod-dfs-ancestor m) (min (mod-dfs-ancestor m) (mod-dfs-ancestor dep)))
          (let ((root (or (mod-cycle-root dep) dep)))
            (when (mod-errored-p root) (js-throw (mod-error-value root)))
            (setf dep root)))
      ;; A dependency still evaluating asynchronously is one this module has to wait for.
      (when (mod-async-evaluation dep)
        (incf (mod-pending-deps m))
        (pushnew m (mod-async-parents dep)))))
  (cond
    ((or (plusp (mod-pending-deps m)) (mod-has-tla m))
     (setf (mod-async-evaluation m) (incf *async-eval-counter*))
     (when (zerop (mod-pending-deps m)) (%execute-async-module m)))
    (t (%execute-module m)))
  ;; Close the strongly-connected component.
  (when (= (mod-dfs-ancestor m) (mod-dfs-index m))
    (loop for other = (pop (car stack))
          do (setf (mod-status other) (if (mod-async-evaluation other) :evaluating-async :evaluated)
                   (mod-cycle-root other) m)
          until (eq other m)))
  idx)

(defun evaluate-module (m)
  "Evaluate M and its dependencies.  Returns a PROMISE for the whole graph's completion.

With top-level await this stops being a depth-first walk that returns when it is done: a module
whose body awaits is left EVALUATING-ASYNC, its dependents are counted as pending against it, and
they are run from the promise callback when it settles.  Errors propagate to every async parent,
and a module that already threw stays thrown rather than running its side effects again."
  (let* ((root (if (member (mod-status m) '(:evaluating-async :evaluated))
                   (or (mod-cycle-root m) m)
                   m)))
    (when (and (not (eq root m)) (mod-top-capability root))
      (return-from evaluate-module (mod-top-capability root)))
    (when (mod-top-capability root)
      (return-from evaluate-module (mod-top-capability root)))
    (let ((cap (make-promise))
          (stack (list '())))
      (setf (mod-top-capability root) cap)
      (handler-case
          (progn
            (%inner-module-evaluation root stack 0)
            (unless (mod-async-evaluation root)
              (promise-fulfill cap *undefined*)))
        (shuttle-error (e)
          (dolist (other (car stack))
            (setf (mod-errored-p other) t
                  (mod-error-value other) (shuttle-error-value e)
                  (mod-status other) :evaluated))
          (promise-reject-internal cap (shuttle-error-value e))))
      cap)))

;;; ---- the consumer API ----------------------------------------------------------------------

(defun make-file-module-host (&key (root "") (extensions '("" ".js" ".mjs")))
  "A host that reads modules from the filesystem, resolving relative to the importer -- enough for
test262's sibling _FIXTURE files and for anyone scripting locally."
  (make-instance
   'module-host
   :resolve (lambda (specifier referrer)
              (let* ((dir (if referrer
                              (namestring (make-pathname :name nil :type nil :version nil
                                                         :defaults (pathname referrer)))
                              root))
                     (base (%norm-join dir specifier)))
                (loop for ext in extensions
                      for cand = (concatenate 'string base ext)
                      for hit = (%probe-native cand)
                      when (and hit (pathname-name hit)) return (namestring hit))))
   :loader (lambda (key)
             (let ((p (%probe-native key)))
               (and p (pathname-name p) (slurp-file p))))))

(defun set-module-host (realm host)
  "Give REALM a module host, so `import()` works from SCRIPT code too -- which has no module to
inherit one from.  This is the seam an embedder installs: weft will answer over HTTP where
MAKE-FILE-MODULE-HOST answers from disk."
  (setf (realm-module-host realm) host))

(defun eval-module (realm key &key host)
  "Load, link and evaluate the module named KEY.  Returns its namespace object."
  (let* ((*current-realm* realm)
         (*module-host* (or host (realm-module-host realm) *module-host*
                            (%mod-error "TypeError" "no module host is installed")))
         (m (progn (unless (realm-module-host realm)
                     (setf (realm-module-host realm) *module-host*))
                   (resolve-imported-module nil key))))
    (link-module m)
    (let ((p (evaluate-module m)))
      ;; Evaluation is a promise now, and with no I/O every await settles through the microtask
      ;; queue -- so draining it is what "wait for the graph" means here.  A promise still pending
      ;; afterwards is a module awaiting something nothing will ever resolve, and saying so is
      ;; better than returning a namespace whose bindings were never initialised.
      (drain-microtasks)
      (case (promise-state p)
        (:rejected (js-throw (promise-value p)))
        (:pending (%mod-error "Error" "module ~a is still awaiting: nothing will settle it"
                              (mod-key m)))))
    (namespace-object m)))
