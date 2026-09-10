;;;; registry.lisp — talk to an npm registry, and refuse anything that does not verify.
;;;;
;;;; ============================================================================================
;;;; INTEGRITY IS NOT A FEATURE HERE, IT IS THE POINT
;;;; ============================================================================================
;;;;
;;;; Everything this file fetches is code that will later be executed.  Two checks stand between
;;;; the registry and that, and BOTH are mandatory rather than optional:
;;;;
;;;;   The connection is TLS with full certificate validation (seal, verify on by default) --
;;;;   without it "fetch over https" means "fetch from whoever answers".
;;;;
;;;;   The tarball is hashed and compared against the `integrity` the registry published for it.
;;;;   A mismatch signals; there is no flag to skip it.  This is what makes a lockfile mean
;;;;   something: the hash pins the bytes, not the version number.
;;;;
;;;; Where a package predates SRI and only carries `dist.shasum`, that SHA-1 is checked instead --
;;;; and the resolution records WHICH check ran, because "verified" against SHA-1 is a weaker
;;;; claim than against SHA-512 and a lockfile that hides the difference is lying by omission.

(in-package #:shuttle)

(define-condition registry-error (error)
  ((text :initarg :text :reader registry-error-text))
  (:report (lambda (c s) (write-string (registry-error-text c) s))))

(defun %reg-fail (fmt &rest args)
  (error 'registry-error :text (apply #'format nil fmt args)))

(defparameter *registry* "https://registry.npmjs.org"
  "Base URL.  A private registry is a different string, not a different code path.")

(defparameter *b64-alphabet*
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/")

(defun %b64 (bytes)
  (let ((out (make-string-output-stream)) (n (length bytes)))
    (loop for i from 0 below n by 3
          do (let* ((b0 (aref bytes i))
                    (b1 (if (< (+ i 1) n) (aref bytes (+ i 1)) 0))
                    (b2 (if (< (+ i 2) n) (aref bytes (+ i 2)) 0))
                    (v (logior (ash b0 16) (ash b1 8) b2)))
               (write-char (char *b64-alphabet* (ldb (byte 6 18) v)) out)
               (write-char (char *b64-alphabet* (ldb (byte 6 12) v)) out)
               (write-char (if (< (+ i 1) n) (char *b64-alphabet* (ldb (byte 6 6) v)) #\=) out)
               (write-char (if (< (+ i 2) n) (char *b64-alphabet* (ldb (byte 6 0) v)) #\=) out)))
    (get-output-stream-string out)))

(defun %hex (bytes)
  (string-downcase (format nil "~{~2,'0x~}" (coerce bytes 'list))))

(defun %url-for (name &optional version)
  "A scoped name keeps its slash: the registry serves /@scope/name directly."
  (format nil "~a/~a~@[/~a~]" *registry* name version))

(defun registry-packument (name)
  "The registry's metadata document for NAME, as a parsed JS object."
  (let ((text (handler-case (seal.http:get-string (%url-for name))
                (error (e) (%reg-fail "fetching ~a: ~a" name e)))))
    (unless *json-realm* (setf *json-realm* (make-realm)))
    (define-global *json-realm* "__pkgtext" text)
    (handler-case (eval-script *json-realm* "JSON.parse(__pkgtext)")
      (error (e) (%reg-fail "~a: the registry returned something that is not JSON: ~a" name e)))))

(defun packument-versions (packument)
  "Every published version string in PACKUMENT."
  (let ((versions (jsref packument "versions")))
    (unless versions (%reg-fail "no `versions` in the packument"))
    ;; ORDINARY-OWN-KEYS rather than reaching into the object's storage: it is the engine's own
    ;; answer to `Object.keys`, so a change in how small objects are stored cannot silently change
    ;; which versions a resolver can see.
    (remove-if-not #'stringp (ordinary-own-keys versions))))

(defun packument-manifest (packument version)
  (or (jsref (jsref packument "versions") version)
      (%reg-fail "version ~a is not published" version)))

(defclass resolved ()
  ((name :initarg :name :reader resolved-name)
   (version :initarg :version :reader resolved-version)
   (tarball :initarg :tarball :reader resolved-tarball)
   (integrity :initarg :integrity :reader resolved-integrity)
   (algorithm :initarg :algorithm :reader resolved-algorithm
              :documentation "Which hash actually verified the bytes -- :sha512 or :sha1.")
   (dependencies :initarg :dependencies :initform '() :reader resolved-dependencies
                 :documentation "An alist of (NAME . RANGE) from the manifest's `dependencies`.")
   (peers :initarg :peers :initform '() :reader resolved-peers
          :documentation "An alist of (NAME . RANGE) from `peerDependencies`.  A peer is provided
by whoever DEPENDS on this package, not by this package -- see resolve.lisp.")
   (optional-peers :initarg :optional-peers :initform '() :reader resolved-optional-peers
                   :documentation "Names from `peerDependenciesMeta` marked optional: wanted if
present, never a reason to install or to fail.")
   (optional-deps :initarg :optional-deps :initform '() :reader resolved-optional-deps
                  :documentation "An alist of (NAME . RANGE) from `optionalDependencies`.")
   (os :initarg :os :initform nil :reader resolved-os
       :documentation "The manifest's `os` field: which platforms this package is FOR.")
   (cpu :initarg :cpu :initform nil :reader resolved-cpu)
   (libc :initarg :libc :initform nil :reader resolved-libc)
   (engine-node :initarg :engine-node :initform nil :reader resolved-engine-node
                :documentation "The manifest's `engines.node` range, or NIL."))
  (:documentation "One package pinned to one version, with the hash that pins its bytes."))

(defun manifest-dependencies (manifest &key (field "dependencies"))
  (let ((deps (jsref manifest field)) (acc '()))
    (when deps
      (dolist (k (remove-if-not #'stringp (ordinary-own-keys deps)))
        (let ((r (jsstr (jsref deps k))))
          (when r (push (cons k r) acc)))))
    (nreverse acc)))

(defun manifest-string-list (manifest field)
  (let ((v (jsref manifest field)) (acc '()))
    (when (and v (js-object-p v))
      (dolist (k (remove-if-not #'stringp (ordinary-own-keys v)))
        (let ((e (jsstr (jsref v k)))) (when e (push e acc)))))
    (nreverse acc)))

(defparameter *platform-os*
  (let ((s (string-downcase (software-type))))
    (cond ((search "linux" s) "linux") ((search "darwin" s) "darwin")
          ((search "bsd" s) (subseq s 0 (min 7 (length s))))
          ((search "win" s) "win32") (t s)))
  "This host, spelled the way npm spells it.")

(defparameter *platform-cpu*
  (let ((s (string-downcase (machine-type))))
    (cond ((or (search "x86-64" s) (search "x86_64" s) (search "amd64" s)) "x64")
          ((search "aarch64" s) "arm64") ((search "arm" s) "arm")
          ((search "x86" s) "ia32") (t s))))

(defun %platform-field-ok-p (values current)
  "npm's `os`/`cpu` matching: a list of names, any of which may be NEGATED with a leading `!`.

An empty list means `anywhere`.  A list of negations is a blocklist; a list of plain names is an
allowlist; npm treats a mixture as an allowlist that the negations then veto."
  (if (null values)
      t
      (let ((allow '()) (deny '()))
        (dolist (v values)
          (if (and (plusp (length v)) (char= (char v 0) #\!))
              (push (subseq v 1) deny)
              (push v allow)))
        (and (not (member current deny :test #'string-equal))
             (or (null allow) (member current allow :test #'string-equal))))))

(defparameter *platform-libc*
  ;; npm 10 added a `libc` field so a package can ship separate glibc and musl binaries.  Without
  ;; it a glibc host installs BOTH rollup binaries -- the musl one is dead weight that will not
  ;; load.  Detected by looking for musl's loader; absence of it means glibc on any Linux that
  ;; runs SBCL.
  (when (string= *platform-os* "linux")
    (if (or (directory "/lib/ld-musl-*.so.1") (directory "/lib/libc.musl-*.so.1"))
        "musl" "glibc")))

(defvar *target-node* nil
  "The Node version this project targets, as a version string, or NIL for `unspecified`.

`engines.node` is a claim about a RUNTIME, and shuttle is not one -- there is no ambient node
version here to compare against, which is rather the point of the exercise.  npm silently skips an
OPTIONAL dependency whose engines the running node does not satisfy, and that is worth matching,
but only when there is something real to match against.  So the target is declared rather than
guessed: the project's own package.json `engines.node` if it has one, or --target-node.  Left NIL,
engines are not consulted at all and nothing is skipped for them -- inventing a target would mean
silently dropping packages on the strength of a number nobody supplied.")

(defun resolved-runs-here-p (r)
  "Is this package FOR this platform and target?  An OPTIONAL dependency that is not gets skipped,
which is how a package ships one prebuilt binary per platform and each host takes only its own."
  (and (%platform-field-ok-p (resolved-os r) *platform-os*)
       (%platform-field-ok-p (resolved-cpu r) *platform-cpu*)
       (or (null *platform-libc*)
           (%platform-field-ok-p (resolved-libc r) *platform-libc*))
       (or (null *target-node*)
           (null (resolved-engine-node r))
           (let ((range (parse-range (resolved-engine-node r))))
             ;; An engines range we cannot parse is not a reason to drop a package.
             (or (null range) (semver-satisfies-p *target-node* range))))))

(defun manifest-optional-peers (manifest)
  "Names in `peerDependenciesMeta` flagged `optional: true`.

npm's convention for \"use this if the host has it\" -- an ESLint plugin that can work with or
without a TypeScript parser, say.  Treating one as required turns an optional integration into a
failed install."
  (let ((meta (jsref manifest "peerDependenciesMeta")) (acc '()))
    (when meta
      (dolist (k (remove-if-not #'stringp (ordinary-own-keys meta)))
        (let ((e (jsref meta k)))
          (when (and e (js-truthy* (jsref e "optional"))) (push k acc)))))
    (nreverse acc)))

(defun resolve-version (name range &key packument)
  "The highest published version of NAME satisfying RANGE, as a RESOLVED.

Signals rather than guessing when nothing satisfies: a resolver that falls back to `latest`
because it could not satisfy a constraint has stopped being a resolver."
  (let* ((p (or packument (registry-packument name)))
         (all (packument-versions p))
         (parsed-range (parse-range range)))
    (unless parsed-range
      (%reg-fail "~a: `~a` is not a version range this understands" name range))
    (let* ((tags (jsref p "dist-tags"))
           (latest (and tags (jsstr (jsref tags "latest"))))
           ;; PREFER THE `latest` TAG WHEN IT SATISFIES, even if a higher version exists.  This is
           ;; npm's rule and it is not cosmetic: a publisher who ships 1.3.1 and then moves the
           ;; `latest` tag back to 1.3.0 is saying "do not hand this one out by default".  Taking
           ;; the maximum unconditionally installs versions that were deliberately un-latested --
           ;; which is how get-intrinsic@1.3.1 turned up here and in no npm tree.
           (best (if (and latest (semver-satisfies-p latest parsed-range))
                     (parse-semver latest)
                     (semver-max-satisfying all parsed-range))))
      (unless best
        (%reg-fail "~a: nothing published satisfies ~a (~d versions, newest ~a)"
                   name range (length all)
                   (let ((m (semver-max-satisfying all (parse-range "*"))))
                     (and m (semver-string m)))))
      (let* ((vs (semver-string best))
             (manifest (packument-manifest p vs))
             (dist (jsref manifest "dist")))
        (make-instance 'resolved
                       :name name :version vs
                       :tarball (or (jsstr (jsref dist "tarball"))
                                    (%reg-fail "~a@~a: no tarball url" name vs))
                       :integrity (or (jsstr (jsref dist "integrity"))
                                      (jsstr (jsref dist "shasum"))
                                      (%reg-fail "~a@~a: the registry published NO integrity hash ~
and no shasum, so these bytes cannot be verified" name vs))
                       :algorithm (if (jsstr (jsref dist "integrity")) :sha512 :sha1)
                       ;; THE REGISTRY DUPLICATES OPTIONAL DEPENDENCIES INTO `dependencies`.
                       ;; A packument manifest lists fsevents under BOTH for vite, and a client
                       ;; that reads only `dependencies` therefore installs a macOS-only package
                       ;; on Linux -- as a REQUIRED one, so a platform it cannot run on becomes a
                       ;; failed install rather than a skipped extra.  Subtract them.
                       :dependencies (let ((opt (manifest-dependencies
                                                 manifest :field "optionalDependencies")))
                                       (remove-if (lambda (d)
                                                    (assoc (car d) opt :test #'string=))
                                                  (manifest-dependencies manifest)))
                       :optional-deps (manifest-dependencies
                                       manifest :field "optionalDependencies")
                       :os (manifest-string-list manifest "os")
                       :cpu (manifest-string-list manifest "cpu")
                       :libc (manifest-string-list manifest "libc")
                       :engine-node (let ((e (jsref manifest "engines")))
                                      (and e (jsstr (jsref e "node"))))
                       :peers (manifest-dependencies manifest :field "peerDependencies")
                       :optional-peers (manifest-optional-peers manifest))))))

(defun verify-integrity (bytes resolved)
  "Signal unless BYTES hash to what the registry published for RESOLVED."
  (let* ((want (resolved-integrity resolved))
         (got (ecase (resolved-algorithm resolved)
                (:sha512 (concatenate 'string "sha512-" (%b64 (natrium:sha512 bytes))))
                (:sha1 (%hex (seal:sha1 bytes))))))
    (unless (string= want got)
      (%reg-fail "~a@~a: INTEGRITY MISMATCH.~%  registry says ~a~%  bytes hash to ~a~%  ~
Refusing to install bytes that are not the bytes that were published."
                 (resolved-name resolved) (resolved-version resolved) want got))
    t))

(defun fetch-package (resolved)
  "The tarball for RESOLVED as a byte vector, verified.  Returns the UNCOMPRESSED tar."
  (let ((tgz (handler-case (coerce (seal.http:response-body
                                    (seal.http:http-get (resolved-tarball resolved)))
                                   '(vector (unsigned-byte 8)))
               (error (e) (%reg-fail "~a@~a: fetching the tarball: ~a"
                                     (resolved-name resolved) (resolved-version resolved) e)))))
    (verify-integrity tgz resolved)
    (values (cram:gzip-decompress tgz) tgz)))
