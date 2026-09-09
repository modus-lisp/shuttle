;;;; webcrypto.lisp — `crypto.getRandomValues`, which REFUSES rather than inventing entropy.
;;;;
;;;; ============================================================================================
;;;; AN ENGINE MUST NEVER MAKE UP RANDOMNESS
;;;; ============================================================================================
;;;;
;;;; Everything that calls this is generating a key, a nonce, or a token.  There is no such thing
;;;; as a degraded mode: bytes from a PRNG seeded by the clock look exactly like bytes from a
;;;; CSPRNG right up until someone reproduces them, and by then the key is published.  So there is
;;;; no fallback here.  With no entropy source installed, `crypto.getRandomValues` THROWS, and it
;;;; says how to fix it.
;;;;
;;;; That is also why the source is INJECTED rather than chosen here.  Shuttle is a language
;;;; implementation; it has no business deciding what this host considers a secure source.  The
;;;; embedder installs one -- natrium's CSPRNG, /dev/urandom, a hardware device -- and owns that
;;;; decision:
;;;;
;;;;     (setf shuttle:*entropy-source* (lambda (n) (natrium:random-bytes n)))
;;;;
;;;; A source that returns the wrong number of bytes is a broken source, and is rejected rather
;;;; than padded: silently topping up short entropy is exactly the failure this file exists to
;;;; prevent.
;;;;
;;;; The `crypto` global exists either way, because feature-detection in the wild is
;;;; `typeof crypto !== 'undefined'` and a library that finds it missing tends to fall back to
;;;; Math.random rather than fail.  Present-and-throwing is the safer shape than absent.

(in-package #:shuttle)

(defvar *entropy-source* nil
  "NIL, or a function of one argument N returning N cryptographically secure bytes as an
(unsigned-byte 8) vector.  See the file header: there is deliberately no default.")

(defparameter +get-random-values-quota+ 65536
  "The Web Crypto limit, in bytes, on one call.")

(defun %integer-typed-array-p (o)
  "Web Crypto accepts only INTEGER typed arrays -- filling a Float64Array with random bits would
produce NaNs and infinities, so the spec refuses it and so does this."
  (and (typed-array-p o)
       (let ((name (ta-type-name (ta-type-of o))))
         (not (or (string= name "Float32Array") (string= name "Float64Array")
                  (string= name "Float16Array"))))))

(defun install-web-crypto (realm)
  (let ((crypto (make-object :proto (realm-object-proto realm))))
    (def-method realm crypto "getRandomValues" 1 (this args)
      (declare (ignore this))
      (let ((ta (arg 0 args)))
        (unless (%integer-typed-array-p ta)
          (js-throw (make-native-error
                     "TypeError"
                     "crypto.getRandomValues expects an integer TypedArray")))
        (when (ta-out-of-bounds-p ta)
          (js-throw (make-native-error "TypeError" "the TypedArray has been detached")))
        (let* ((count (ta-length-checked ta))
               (size (ta-type-size (ta-type-of ta)))
               (nbytes (* count size)))
          (when (> nbytes +get-random-values-quota+)
            (js-throw (make-native-error
                       "RangeError"
                       (format nil "crypto.getRandomValues: ~d bytes requested, the limit is ~d"
                               nbytes +get-random-values-quota+))))
          (unless *entropy-source*
            ;; The whole point.  No clock-seeded fallback, no Math.random, no "good enough".
            (js-throw (make-native-error
                       "Error"
                       "crypto.getRandomValues: no entropy source is installed, and this engine
will not invent one.  Bytes from a predictable generator are indistinguishable from secure ones
until someone reproduces your key.  The embedder must install a source:
    (setf shuttle:*entropy-source* (lambda (n) ...n secure bytes...))")))
          (when (plusp nbytes)
            (let ((bytes (funcall *entropy-source* nbytes)))
              (unless (and (typep bytes 'sequence) (= (length bytes) nbytes))
                ;; Short entropy is a broken source.  Padding it would be the same lie as
                ;; inventing it in the first place.
                (js-throw (make-native-error
                           "Error"
                           (format nil "crypto.getRandomValues: the installed entropy source ~
returned ~a bytes, not ~d" (if (typep bytes 'sequence) (length bytes) "non-sequence") nbytes))))
              (let ((dst (ta-bytes ta)) (off (ta-raw-offset ta)))
                (dotimes (i nbytes) (setf (aref dst (+ off i)) (elt bytes i))))))
          ta)))
    (define-global realm "crypto" crypto)
    (put (realm-global realm) "crypto" crypto :enumerable nil :writable t :configurable t)))

(register-builtin-installer 'install-web-crypto)
