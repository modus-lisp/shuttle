;;;; bundle.lisp — one script out of a module graph.
;;;;
;;;; ==================================================================================
;;;; WHAT THIS REPLACES, AND WHY IT IS HERE AND NOT IN A BUILD SCRIPT
;;;; ==================================================================================
;;;;
;;;; The phone client is authored as an ES module and shipped as one script, and the thing that
;;;; did the flattening was esbuild -- a node binary, fetched by npm, holding the deploy path of a
;;;; system whose display layer is meant to run on bare metal.  shuttle already parses the module
;;;; graph (module.lisp); this walks it and prints it.
;;;;
;;;; It does NOT execute what it bundles, and that is the whole reason the job is tractable: a
;;;; bundler needs a module's SHAPE, not its behaviour.
;;;;
;;;; ==================================================================================
;;;; THE SOURCE PASSES THROUGH UNTOUCHED, EXCEPT WHERE IT DOES NOT
;;;; ==================================================================================
;;;;
;;;; Every byte of a module body is copied verbatim; only the import and export DECLARATIONS are
;;;; rewritten, by splicing at the spans module.lisp recorded.  There is deliberately no printer
;;;; here -- no AST -> JS pass -- because a printer is a second implementation of the language's
;;;; syntax, and a bug in it corrupts somebody else's cryptography silently.  "Unchanged except
;;;; where we deliberately changed it" is a property worth designing around.
;;;;
;;;; That is also why there is no renaming.  Each module keeps its own function scope, so two
;;;; modules may both define `bytesToHex` and neither has to be touched.

(in-package #:shuttle)

;;; ---- reading, and the JSON the engine parses for itself ------------------------------------

(defun slurp-file (path)
  (with-open-file (s path :external-format :utf-8)
    (let ((b (make-string (file-length s)))) (subseq b 0 (read-sequence b s)))))

(defvar *json-realm* nil)

(defun parse-json-file (path)
  "PATH's JSON as a JS object, parsed by shuttle.  A bundler that needed a JSON library to read
package.json would be admitting it could not read JavaScript."
  (unless *json-realm* (setf *json-realm* (make-realm)))
  (define-global *json-realm* "__pkgtext" (slurp-file path))
  (eval-script *json-realm* "JSON.parse(__pkgtext)"))

(defun jsref (obj key)
  "OBJ[KEY] as a Lisp value, or NIL when absent.  Strings come back as strings."
  (when (and obj (js-object-p obj))
    (let ((v (js-get obj key)))
      (cond ((or (null v) (eq v *undefined*) (eq v *null*)) nil)
            (t v)))))

(defun jsstr (v) (and (stringp v) v))

;;; ---- resolution ----------------------------------------------------------------------------

(defparameter *extensions* '("" ".js" ".mjs")
  "Tried in order against a relative specifier before falling back to /index.js.")

(defparameter *conditions* '("import" "module" "browser" "default")
  "Export conditions, most specific first.  `require` is deliberately absent: this resolves the
ESM graph, and taking a CommonJS entry point would hand the parser a `module.exports` file that is
not a module at all.")

;;; ---- paths, joined the way the specifier means them ---------------------------------------
;;;
;;; CL:MERGE-PATHNAMES keeps "./" and "../" as literal directory components -- it produces
;;; "/a/b/./c" and "/a/b/../c", which PROBE-FILE then does not find.  A module specifier is a
;;; POSIX path, so it gets POSIX joining rather than pathname arithmetic.

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

(defun %existing-file (path)
  (let ((p (probe-file path)))
    (and p (pathname-name p) p)))

(defun resolve-relative (spec dir)
  (let ((base (%norm-join dir spec)))
    (or (loop for ext in *extensions*
              thereis (%existing-file (concatenate 'string base ext)))
        (%existing-file (concatenate 'string base "/index.js")))))

(defun split-bare (spec)
  "`@noble/curves/abstract/utils` -> (values \"@noble/curves\" \"./abstract/utils\")."
  (let* ((parts (loop with start = 0
                      for p = (position #\/ spec :start start)
                      collect (subseq spec start p)
                      while p do (setf start (1+ p))))
         (scoped (and (plusp (length spec)) (char= (char spec 0) #\@)))
         (n (if scoped 2 1))
         (pkg (format nil "~{~a~^/~}" (subseq parts 0 (min n (length parts)))))
         (rest (nthcdr n parts)))
    (values pkg (if rest (format nil "./~{~a~^/~}" rest) "."))))

(defun %condition-pick (v)
  "V is either a target string or a conditions object; walk to a string."
  (cond ((stringp v) v)
        ((and v (js-object-p v))
         (loop for c in *conditions*
               for hit = (jsref v c)
               when hit return (%condition-pick hit)))
        (t nil)))

(defun %exports-target (exports subpath)
  "Match SUBPATH against an `exports` field, including a trailing-* pattern."
  (cond
    ((stringp exports) (and (string= subpath ".") exports))
    ((not (and exports (js-object-p exports))) nil)
    (t
     (let ((keys (js-own-keys exports)))
       (if (notany (lambda (k) (and (stringp k) (plusp (length k)) (char= (char k 0) #\.))) keys)
           ;; No "./" keys at all: the whole object is a conditions map for "." itself.
           (and (string= subpath ".") (%condition-pick exports))
           (or (%condition-pick (jsref exports subpath))
               ;; "./lib/*": the one pattern form that matters in practice.
               (loop for k in keys
                     for star = (and (stringp k) (position #\* k))
                     when (and star
                               (>= (length subpath) (1- (length k)))
                               (string= (subseq k 0 star) (subseq subpath 0 (min star (length subpath)))))
                       return (let ((tail (subseq subpath star))
                                    (tgt (%condition-pick (jsref exports k))))
                                (when (and tgt (position #\* tgt))
                                  (concatenate 'string (subseq tgt 0 (position #\* tgt)) tail))))))))))

(defun package-dirs (from-dir)
  "Every node_modules/ visible from FROM-DIR, nearest first — which is what makes @noble/curves'
own nested copy of @noble/hashes win for files inside it, exactly as node would."
  (let ((segs (remove "" (%split-slash (string-right-trim "/" (namestring from-dir)))
                      :test #'string=))
        (out '()))
    (loop for n from (length segs) downto 0
          do (push (format nil "/~{~a/~}node_modules/" (subseq segs 0 n)) out))
    (nreverse out)))

(defun resolve-bare (spec from-dir)
  (multiple-value-bind (pkg subpath) (split-bare spec)
    (loop for nm in (package-dirs from-dir)
          for root = (concatenate 'string nm pkg "/")
          for pj = (concatenate 'string root "package.json")
          when (probe-file pj)
            do (let* ((json (parse-json-file pj))
                      (tgt (or (%exports-target (jsref json "exports") subpath)
                               ;; No exports map: the legacy fields, ESM first.
                               (and (string= subpath ".")
                                    (or (jsstr (jsref json "module")) (jsstr (jsref json "main"))))
                               (and (not (string= subpath "."))
                                    (subseq subpath 1)))))
                 (let ((hit (and tgt (resolve-relative tgt root))))
                   (when hit (return hit))))
          finally (return nil))))

(defun resolve-module (spec referrer)
  "SPEC as written in REFERRER -> a truename, or NIL."
  (let ((dir (namestring (make-pathname :name nil :type nil :version nil
                                        :defaults (truename referrer)))))
    (if (or (eql 0 (search "./" spec)) (eql 0 (search "../" spec))
            (and (plusp (length spec)) (char= (char spec 0) #\/)))
        (resolve-relative spec dir)
        (resolve-bare spec dir))))

;;; ---- the graph -----------------------------------------------------------------------------

(defclass bundle-module ()
  ((path :initarg :path :reader bm-path)
   (id :initarg :id :reader bm-id
       :documentation "The name this module answers to in the emitted registry.")
   (record :initarg :record :reader bm-record)
   (edges :initarg :edges :accessor bm-edges
          :documentation "Specifier string -> the BUNDLE-MODULE it resolved to.")))

(define-condition bundle-error (error)
  ((text :initarg :text :reader bundle-error-text))
  (:report (lambda (c s) (write-string (bundle-error-text c) s))))

(defun %bail (fmt &rest args)
  (error 'bundle-error :text (apply #'format nil fmt args)))

(defun build-graph (entry &key (id-root nil))
  "Walk from ENTRY.  Returns (values ORDERED CYCLES), ORDERED in dependency order — every module
before the ones that import it — and CYCLES a list of paths that close a loop.

Cycles are REPORTED rather than worked around.  A cycle means some binding is read before the
module that owns it has finished evaluating, and a snapshot-style emitter gets that silently
wrong; naming it is worth more than guessing."
  (let ((seen (make-hash-table :test 'equal))
        (state (make-hash-table :test 'equal))
        (order '()) (cycles '()))
    (labels ((rel (p)
               (let ((s (namestring p)) (r (and id-root (namestring id-root))))
                 (if (and r (eql 0 (search r s))) (subseq s (length r)) s)))
             (walk (path stack)
               (let ((key (namestring path)))
                 (case (gethash key state)
                   (:done (return-from walk (gethash key seen)))
                   (:open (push (reverse (cons (rel path) (mapcar #'rel stack))) cycles)
                          (return-from walk (gethash key seen))))
                 (setf (gethash key state) :open)
                 (let* ((rec (handler-case (parse-module (slurp-file path))
                               (error (e) (%bail "~a~%  while parsing ~a" e path))))
                        (m (make-instance 'bundle-module :path path :id (rel path)
                                                         :record rec :edges nil)))
                   (setf (gethash key seen) m)
                   (let ((edges '()))
                     (dolist (spec (module-requests rec))
                       (let ((hit (resolve-module spec path)))
                         (unless hit
                           (%bail "cannot resolve ~s~%  imported by ~a" spec path))
                         (push (cons spec (walk hit (cons path stack))) edges)))
                     (setf (bm-edges m) (nreverse edges)))
                   (setf (gethash key state) :done)
                   (push m order)
                   m))))
      (walk (truename entry) '()))
    (values (nreverse order) (nreverse cycles))))

;;; ---- emission ------------------------------------------------------------------------------
;;;
;;; THE SHAPE.  Each module becomes a factory in a tiny registry; the entry is required last.
;;; Modules keep their own function scope, which is what buys us "no renaming" -- two modules may
;;; both define `bytesToHex` and neither is touched.
;;;
;;; EXPORTS ARE GETTERS, not copies.  `__x.a = a` would snapshot at declaration time and get a
;;; `const` declared later wrong; a getter reads the binding when somebody asks, which is what a
;;; live ES binding does.  It also gets TDZ right for free: reading an exported `const` too early
;;; throws, exactly as it would across a real module boundary.
;;;
;;; IMPORTS ARE SNAPSHOTS, and that is only sound because BUILD-GRAPH proved the graph acyclic and
;;; the registry evaluates dependencies first -- so the binding has its final value by the time
;;; the importing module runs.  The one case that would defeat it is an exporter REASSIGNING its
;;; own exported binding after evaluation, from inside a function called later.  That is checked
;;; for below and REFUSED rather than silently miscompiled.

(defparameter *runtime* "var __m = {};
function __d(id, f) { __m[id] = { f: f, e: null }; }
function __r(id) {
  var m = __m[id];
  if (!m) throw new Error('module not in bundle: ' + id);
  if (!m.e) { m.e = {}; m.f(m.e, __r); }
  return m.e;
}
function __star(t, x) {
  for (var k in t) {
    if (k !== 'default' && !Object.prototype.hasOwnProperty.call(x, k)) {
      (function (k) {
        Object.defineProperty(x, k, { get: function () { return t[k]; }, enumerable: true });
      })(k);
    }
  }
}
")

(defun %jstr (s)
  (with-output-to-string (o)
    (write-char #\" o)
    (loop for c across s
          do (case c (#\" (write-string "\\\"" o)) (#\\ (write-string "\\\\" o))
                     (#\Newline (write-string "\\n" o)) (t (write-char c o))))
    (write-char #\" o)))

(defun %getter (export-name expr)
  (format nil "Object.defineProperty(__x, ~a, {get: function(){return ~a;}, enumerable: true});~%"
          (%jstr export-name) expr))

(defun %local-ref (name) (if (string= name "*default*") "__default" name))

(defun %dep-id (m spec)
  (let ((hit (cdr (assoc spec (bm-edges m) :test #'string=))))
    (unless hit (%bail "internal: unresolved edge ~s in ~a" spec (bm-id m)))
    (bm-id hit)))

(defun %exported-locals (rec)
  (loop for e in (module-exports rec)
        for l = (entry-local-name e)
        when (and l (not (string= l "*default*"))) collect l))

(defun module-level-kinds (rec)
  "Module-level name -> :CONST / :LET / :VAR / :FUNC / :CLASS.  Only the top level: a nested
declaration is a different binding and is not what an export names."
  (let ((h (make-hash-table :test 'equal)))
    (labels ((note (stmt)
               (case (car stmt)
                 (:var (let ((kind (intern (string-upcase (second stmt)) :keyword)))
                         (dolist (d (third stmt))
                           (dolist (n (%target-names (car d) '()))
                             (setf (gethash n h) kind)))))
                 ((:func :genfunc :asyncfunc :asyncgenfunc)
                  (when (stringp (second stmt)) (setf (gethash (second stmt) h) :func)))
                 (:class (when (stringp (second stmt)) (setf (gethash (second stmt) h) :class))))))
      (dolist (item (module-items rec))
        (case (car item)
          (:export-decl (note (second item)))
          (t (note item)))))
    h))

(defun module-live-exports (rec)
  "Exported bindings this module REASSIGNS after declaring them, so that an importer holding a
snapshot would hold a stale value.

A CONST export is skipped outright, and that is not an optimisation -- the language forbids
assigning it, so no scope analysis can be needed to prove what the declaration already proves.
That single rule is what separates noVNC's `export let Debug`, which really is reassigned by
initLogging(), from @scure/base's `export const str`, where the only `str =` in the file assigns a
PARAMETER of that name inside some other function.  Both look identical to a token scan; only the
declaration tells them apart."
  (let* ((kinds (module-level-kinds rec))
         (names (remove-if (lambda (n) (member (gethash n kinds) '(:const nil)))
                           (%exported-locals rec))))
    (when names
      (let ((toks (tokenize (module-source rec))) (live '()))
        (loop for i from 0 below (1- (length toks))
              for tk = (aref toks i)
              for nx = (aref toks (1+ i))
              when (and (eq (car tk) :ident) (member (cdr tk) names :test #'equal)
                        (eq (car nx) :punct)
                        (member (cdr nx) '("=" "+=" "-=" "*=" "/=" "%=" "**=" "||=" "&&=" "??="
                                           "|=" "&=" "^=" "<<=" ">>=" ">>>=" "++" "--")
                                :test #'string=)
                        (not (and (plusp i)
                                  (let ((pv (aref toks (1- i))))
                                    (and (eq (car pv) :ident)
                                         (member (cdr pv) '("var" "let" "const") :test #'equal))))))
                do (pushnew (cdr tk) live :test #'equal))
        (nreverse live)))))

(defun %live-locals (m live-of)
  "Local names in M bound to an exported binding its exporter REASSIGNS.  These cannot be
snapshotted into a `var`, because JS has no way to make a local name alias another object's
property -- so every reference to one is rewritten to a property read instead.

A NAMESPACE import needs none of this and gets liveness for free: `Log.Debug` is already a read
through the exporter's getter, which is why noVNC -- who import * as Log almost everywhere -- turn
out to need four rewrites in the whole graph."
  (let ((out '()))
    (dolist (e (module-imports (bm-record m)) out)
      (let* ((dep (cdr (assoc (entry-request e) (bm-edges m) :test #'string=)))
             (live (and dep (gethash (bm-id dep) live-of))))
        (when (and live (stringp (entry-import-name e))
                   (member (entry-import-name e) live :test #'equal))
          (push (cons (entry-local-name e) (entry-import-name e)) out))))))

(defun %rewrite-points (rec live-map ns-of)
  "Source spans to replace, as (START END TEXT), for every genuine REFERENCE to a live local.

Token-level, and deliberately so: a string or a comment mentioning the name is not a token, so it
cannot be hit.  What has to be excluded is the two places an identifier token is not a reference --
after a dot, and as an object literal key -- plus shorthand `{Debug}`, which IS a reference and has
to become `Debug: ns.Debug` rather than a bare property read."
  (let* ((src (module-source rec))
         (starts (module-starts rec))
         (toks (tokenize src))
         (out '()))
    (loop for i from 0 below (length toks)
          for tk = (aref toks i)
          for hit = (and (eq (car tk) :ident) (assoc (cdr tk) live-map :test #'equal))
          when hit
            do (let* ((name (cdr tk))
                      (prev (and (plusp i) (aref toks (1- i))))
                      (next (and (< (1+ i) (length toks)) (aref toks (1+ i))))
                      (punct (lambda (tok v) (and tok (eq (car tok) :punct) (string= (cdr tok) v))))
                      (ns (cdr (assoc (car hit) ns-of :test #'equal)))
                      (ref (format nil "~a[~a]" ns (%jstr (cdr hit))))
                      (s (aref starts i))
                      (e (+ s (length name))))
                 (cond
                   ;; a.Debug / a?.Debug -- a property of something else entirely
                   ((or (funcall punct prev ".") (funcall punct prev "?.")) nil)
                   ;; #Debug -- a private name
                   ((funcall punct prev "#") nil)
                   ;; { Debug: ... } or , Debug: ... -- a key, not a reference
                   ((and (or (funcall punct prev "{") (funcall punct prev ","))
                         (funcall punct next ":"))
                    nil)
                   ;; { Debug } / { Debug, } -- shorthand, which MEANS { Debug: Debug }
                   ((and (or (funcall punct prev "{") (funcall punct prev ","))
                         (or (funcall punct next ",") (funcall punct next "}")))
                    (push (list s e (format nil "~a: ~a" name ref)) out))
                   (t (push (list s e ref) out)))))
    (sort (nreverse out) #'< :key #'first)))

(defun %copy-span (src s e rewrites out)
  "Copy SRC[S,E) to OUT, applying any REWRITES that fall inside it."
  (let ((at s))
    (dolist (rw rewrites)
      (destructuring-bind (rs re text) rw
        (when (and (>= rs at) (<= re e))
          (write-string (subseq src at rs) out)
          (write-string text out)
          (setf at re))))
    (write-string (subseq src at e) out)))

(defun emit-module (m &optional live-of)
  "One factory for M: imports hoisted, exports installed as getters, body verbatim between.

TWO PASSES, and the reason is ES hoisting.  An import declaration may appear textually AFTER code
that uses what it binds -- legal, because imports are hoisted -- so every import has to be seen
before a byte of body is emitted.  Pass one fills the preamble and learns which namespace variable
each live local reads through; pass two copies the body, splicing at spans and at rewrite points."
  (let* ((rec (bm-record m))
         (src (module-source rec))
         (starts (module-starts rec))
         (spans (module-spans rec))
         (items (module-items rec))
         (pre (make-string-output-stream))
         (body (make-string-output-stream))
         (live-map (and live-of (%live-locals m live-of)))
         (ns-of '())
         (ns-counter 0))
    (flet ((next-ns () (format nil "__n~a" (incf ns-counter))))
      ;; ---- pass one: imports, and the namespaces everything else will read through -----------
      (let ((ns-for-item (make-hash-table :test 'eq)))
        (dolist (item items)
          (case (car item)
            (:import
             (destructuring-bind (spec entries) (rest item)
               (let ((ns (next-ns)))
                 (setf (gethash item ns-for-item) ns)
                 (format pre "var ~a = __r(~a);~%" ns (%jstr (%dep-id m spec)))
                 (dolist (en entries)
                   (ecase (first en)
                     (:default   (format pre "var ~a = ~a.default;~%" (second en) ns))
                     (:namespace (format pre "var ~a = ~a;~%" (second en) ns))
                     (:named
                      ;; A live binding gets NO local: JS cannot alias one, so every reference is
                      ;; rewritten to a read through this namespace instead.
                      (if (assoc (third en) live-map :test #'equal)
                          (push (cons (third en) ns) ns-of)
                          (format pre "var ~a = ~a[~a];~%"
                                  (third en) ns (%jstr (second en)))))))))) 
            ((:export-named :export-star)
             (let ((spec (third item)))
               (when (and (eq (car item) :export-named) spec)
                 (setf (gethash item ns-for-item) (next-ns)))
               (when (eq (car item) :export-star)
                 (setf (gethash item ns-for-item) (next-ns)))))))

        ;; ---- pass two: the body ---------------------------------------------------------------
        (let ((rewrites (if live-map (%rewrite-points rec live-map ns-of) '())))
          (%copy-span src 0 (if spans (span-start (first spans)) (length src)) rewrites body)
          (loop for item in items
                for sp in spans
                do (let ((s (span-start sp)) (e (span-end sp)) (from (span-from sp)))
                     (case (car item)
                       (:import)                       ; hoisted into PRE; nothing left here
                       (:export-decl
                        ;; keep the declaration, drop the word `export` -- the text from the
                        ;; span's start up to its SECOND token
                        (%copy-span src (aref starts (1+ from)) e rewrites body)
                        (dolist (n (%declared-names (second item)))
                          (write-string (%getter n n) pre)))
                       (:export-default
                        ;; `export default function f(){}` is a DECLARATION: it binds f in module
                        ;; scope as well as exporting it.  Emitting `const __default = function
                        ;; f(){}` instead makes a named function EXPRESSION, whose name is visible
                        ;; only inside its own body -- so a later call to f() in the same module
                        ;; fails.  noVNC's crc table is built by exactly that shape.
                        (let ((named (let ((n (second item)))
                                       (and (consp n)
                                            (member (car n) '(:func :genfunc :asyncfunc
                                                              :asyncgenfunc :class))
                                            (stringp (second n))
                                            (second n)))))
                          (cond
                            (named
                             (%copy-span src (aref starts (+ from 2)) e rewrites body)
                             (write-string (%getter "default" named) pre))
                            (t
                             (write-string "const __default = " body)
                             (%copy-span src (aref starts (+ from 2)) e rewrites body)
                             (write-string ";" body)
                             (write-string (%getter "default" "__default") pre)))))
                       (:export-named
                        (destructuring-bind (pairs spec) (rest item)
                          (if spec
                              (let ((ns (gethash item ns-for-item)))
                                (format pre "var ~a = __r(~a);~%" ns (%jstr (%dep-id m spec)))
                                (dolist (pr pairs)
                                  (write-string
                                   (%getter (cdr pr) (format nil "~a[~a]" ns (%jstr (car pr)))) pre)))
                              (dolist (pr pairs)
                                (write-string (%getter (cdr pr) (%local-ref (car pr))) pre)))))
                       (:export-star
                        (destructuring-bind (spec as) (rest item)
                          (let ((ns (gethash item ns-for-item)))
                            (format pre "var ~a = __r(~a);~%" ns (%jstr (%dep-id m spec)))
                            (if as
                                (write-string (%getter as ns) pre)
                                (format pre "__star(~a, __x);~%" ns)))))
                       (t (%copy-span src s e rewrites body))))))))
    (format nil "__d(~a, function (__x, __r) {~%\"use strict\";~%~a~a~%});~%"
            (%jstr (bm-id m)) (get-output-stream-string pre) (get-output-stream-string body))))

(defun bundle (entry &key (id-root nil))
  "ENTRY -> one script, as a string."
  (multiple-value-bind (order cycles) (build-graph entry :id-root id-root)
    (when cycles
      (%bail "the graph has ~a cycle~:p, which this emitter will not guess at:~%~{  ~{~a~^ -> ~}~%~}"
             (length cycles) cycles))
    (let ((live-of (make-hash-table :test 'equal)))
      (dolist (m order)
        (let ((live (module-live-exports (bm-record m))))
          (when live (setf (gethash (bm-id m) live-of) live))))
      (let ((out (with-output-to-string (o)
                   (format o "(function () {~%~a~%" *runtime*)
                   (dolist (m order) (write-string (emit-module m live-of) o))
                   (format o "return __r(~a);~%})();~%" (%jstr (bm-id (car (last order))))))))
        ;; THE OUTPUT IS PARSED BEFORE IT IS RETURNED.  Every rewrite above is textual, and the
        ;; failure mode of a bad one -- `{__n1["Debug"]: 1}`, a key turned into a property read --
        ;; is a SYNTAX error rather than a subtly wrong program.  Parsing here is what converts
        ;; that whole class from silent corruption into a refusal.
        (handler-case (parse-program out)
          (error (e) (%bail "the emitted bundle does not parse, so a rewrite above is wrong:~%  ~a" e)))
        out))))
