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
                 :documentation "An alist of (NAME . RANGE) from the manifest's `dependencies`."))
  (:documentation "One package pinned to one version, with the hash that pins its bytes."))

(defun manifest-dependencies (manifest &key (field "dependencies"))
  (let ((deps (jsref manifest field)) (acc '()))
    (when deps
      (dolist (k (remove-if-not #'stringp (ordinary-own-keys deps)))
        (let ((r (jsstr (jsref deps k))))
          (when r (push (cons k r) acc)))))
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
    (let ((best (semver-max-satisfying all parsed-range)))
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
                       :dependencies (manifest-dependencies manifest))))))

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
