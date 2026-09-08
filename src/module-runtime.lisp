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

(defun %norm-join (dir spec)
  "Absolute DIR + relative SPEC -> a normalised absolute namestring."
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
   (meta :initform nil :accessor mod-meta)
   (deps :initform nil :accessor mod-deps)))           ; specifier -> module

(defun %mod-error (kind fmt &rest args)
  (js-throw (make-native-error kind (apply #'format nil fmt args))))

;;; ---- loading -------------------------------------------------------------------------------

(defun resolve-imported-module (referrer specifier)
  "HostResolveImportedModule: the same (referrer, specifier) must always give the same module."
  (let* ((host (or (and referrer (mod-host referrer)) *module-host*
                   (%mod-error "TypeError" "no module host is installed")))
         (key (funcall (host-resolve host) specifier (and referrer (mod-key referrer)))))
    (unless key
      (%mod-error "TypeError" "Cannot resolve module ~s~@[ imported by ~a~]"
                  specifier (and referrer (mod-key referrer))))
    (or (gethash key (host-registry host))
        (let ((src (funcall (host-loader host) key)))
          (unless src (%mod-error "TypeError" "Cannot load module ~a" key))
          (let ((m (make-instance 'source-text-module
                                  :key key :realm *current-realm* :host host
                                  :record (parse-module src))))
            (setf (gethash key (host-registry host)) m)
            m)))))

(defun %mod-dep (m specifier)
  (or (cdr (assoc specifier (mod-deps m) :test #'string=))
      (let ((dep (resolve-imported-module m specifier)))
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
        (return-from resolve-export (values m (entry-local-name e)))))
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
             (names (remove-if-not (lambda (n) (resolve-export m n)) (module-exported-names m)))
             (obj nil))
        (flet ((exported-p (key) (and (stringp key) (member key names :test #'string=))))
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
                        (if (exported-p key) (namespace-read m key) (ordinary-get o key)))
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
                       (make-prop :value (namespace-read m key)
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
                      (same-value (getf desc :value) (namespace-read m key)))
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
    (dolist (item (module-items rec) (nreverse out))
      (case (car item)
        ((:import :export-named :export-star))          ; linking handled these
        (:export-decl (push (second item) out))
        (:export-default
         (let ((node (second item)))
           (if (and (consp node)
                    (member (car node) '(:func :genfunc :asyncfunc :asyncgenfunc :class))
                    (stringp (second node)))
               ;; a NAMED default is a declaration: it binds its own name too
               (push node out)
               (push (list :var "const" (list (cons "*default*" node))) out))))
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
              (setf (gethash (entry-local-name ie) (env-vars env)) (namespace-object dep))
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
  (let* ((*module-host* (or (and *current-module* (mod-host *current-module*)) *module-host*))
         (*current-realm* (or (and *current-module* (mod-realm *current-module*)) *current-realm*))
         (m (resolve-imported-module *current-module* specifier)))
    (link-module m)
    (evaluate-module m)
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
  (let* ((rec (mod-record m))
         (stmts (module-body-statements rec))
         ;; MODULE CODE IS ALWAYS STRICT, with no directive to say so.  Compiling it sloppy is
         ;; not a small difference: a failed [[Set]] or [[Delete]] silently succeeds instead of
         ;; throwing, `this` at the top is wrong, and an assignment to an undeclared name quietly
         ;; creates a global.  Every one of those reads as a module bug and is not one.
         (code (let ((*strict* t)) (compile-fn nil '() (list :block stmts) t)))
         (realm (or (mod-realm m) *current-realm*)))
    (let ((*current-realm* realm) (*current-module* m))
      (run code (mod-env m) *undefined*))))

(defun evaluate-module (m)
  "Evaluate M and everything it depends on, dependencies first, each exactly once.

An error is REMEMBERED: a module that threw stays thrown, and asking for it again rethrows the
same value rather than running its side effects a second time."
  (let ((stack '()) (index 0))
    (labels
        ((inner (m idx)
           (when (mod-errored-p m) (js-throw (mod-error-value m)))
           (when (member (mod-status m) '(:evaluated :evaluating)) (return-from inner idx))
           (unless (eq (mod-status m) :linked)
             (%mod-error "TypeError" "module ~a is not linked" (mod-key m)))
           (setf (mod-status m) :evaluating
                 (mod-dfs-index m) idx
                 (mod-dfs-ancestor m) idx)
           (incf idx)
           (push m stack)
           (dolist (spec (module-requests (mod-record m)))
             (let ((dep (%mod-dep m spec)))
               (setf idx (inner dep idx))
               (when (eq (mod-status dep) :evaluating)
                 (setf (mod-dfs-ancestor m)
                       (min (mod-dfs-ancestor m) (mod-dfs-ancestor dep))))))
           (handler-bind
               ((shuttle-error
                  (lambda (e)
                    ;; every module in the component is poisoned by the same error
                    (loop for other in stack
                          do (setf (mod-errored-p other) t
                                   (mod-error-value other) (shuttle-error-value e)
                                   (mod-status other) :evaluated)))))
             (%run-module-body m))
           (when (= (mod-dfs-ancestor m) (mod-dfs-index m))
             (loop for other = (pop stack)
                   do (setf (mod-status other) :evaluated)
                   until (eq other m)))
           idx))
      (inner m index))
    m))

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
                      when (probe-file cand) return (namestring (truename cand)))))
   :loader (lambda (key) (and (probe-file key) (slurp-file key)))))

(defun eval-module (realm key &key host)
  "Load, link and evaluate the module named KEY.  Returns its namespace object."
  (let* ((*current-realm* realm)
         (*module-host* (or host *module-host*
                            (%mod-error "TypeError" "no module host is installed")))
         (m (resolve-imported-module nil key)))
    (link-module m)
    (evaluate-module m)
    (namespace-object m)))
