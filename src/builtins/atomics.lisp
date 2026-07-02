;;;; builtins/atomics.lisp — the Atomics namespace (single-threaded semantics:
;;;; plain read-modify-write on the backing bytes; wait/notify per the
;;;;
;;;; Ops work on the raw unsigned bit pattern of the element (two's complement
;;;; wrap via ldb), reusing the ta-type encode/decode codecs from typedarray.lisp.
;;;; Validation order (pinned by test262):
;;;;   RMW ops:  ValidateIntegerTypedArray (TypeError: non-TA / detached-or-OOB /
;;;;             wrong element type) -> ValidateAtomicAccess (capture length,
;;;;             ToIndex, RangeError) -> coerce value(s) -> revalidate -> RMW.
;;;;   wait:     validate(waitable) -> require SAB (TypeError, BEFORE index
;;;;             coercion) -> index -> value -> timeout.
;;;;   notify:   validate(waitable) -> index -> count -> (non-shared: 0) -> 0.
(in-package #:shuttle)

(defun atomics-validate (v waitable)
  "ValidateIntegerTypedArray: V must be a non-detached, in-bounds typed array
   whose element type is an integer type (waitable: Int32/BigInt64 only).
   Returns V's ta-type."
  (unless (typed-array-p v)
    (js-throw (make-native-error "TypeError" "Atomics operand is not a TypedArray")))
  (when (ta-out-of-bounds-p v)
    (js-throw (make-native-error "TypeError"
               "TypedArray is out of bounds or backed by a detached ArrayBuffer")))
  (let ((ty (ta-type-of v)))
    (if waitable
        (unless (member (ta-type-name ty) '("Int32Array" "BigInt64Array")
                        :test #'string=)
          (js-throw (make-native-error "TypeError"
                     "typedArray must be an Int32Array or BigInt64Array")))
        (when (or (ta-type-clamped ty) (ta-type-float ty))
          (js-throw (make-native-error "TypeError"
                     "typedArray must be an integer TypedArray"))))
    ty))

(defun atomics-index (ta idx-arg)
  "ValidateAtomicAccess: capture the CURRENT length first (index coercion may
   resize a resizable backing buffer), then ToIndex (RangeError on negatives /
   overlarge), then RangeError when index >= that captured length."
  (let* ((len (ta-elt-length ta))
         (i (to-index idx-arg)))
    (when (>= i len)
      (js-throw (make-native-error "RangeError" "Atomics access index out of range")))
    i))

(defun atomics-coerce (ty v)
  "ToBigInt for the 64-bit bigint element types, else F(ToIntegerOrInfinity)
   (note the spec's F() maps -0 to +0 — observable in Atomics.store's return)."
  (if (ta-type-bigint ty)
      (to-bigint v)
      (let ((n (to-integer-or-infinity v)))
        (if (and (floatp n) (js-negative-zero-p n)) 0d0 n))))

(defun atomics-revalidate (ta i)
  "RevalidateAtomicAccess: value coercion may have detached / shrunk the
   backing buffer (non-shared case)."
  (when (ta-out-of-bounds-p ta)
    (js-throw (make-native-error "TypeError"
               "TypedArray is out of bounds or backed by a detached ArrayBuffer")))
  (when (>= i (ta-elt-length ta))
    (js-throw (make-native-error "RangeError" "Atomics access index out of range"))))

(defun atomics-raw-read (ta i)
  "The raw unsigned bit pattern of element I (little-endian bytes)."
  (let* ((ty (ta-type-of ta)) (size (ta-type-size ty))
         (base (+ (ta-byte-offset ta) (* i size)))
         (bytes (ta-bytes ta)) (u 0))
    (dotimes (b size)
      (setf u (logior u (ash (aref bytes (+ base b)) (* 8 b)))))
    u))

(defun atomics-raw-write (ta i u)
  (let* ((ty (ta-type-of ta)) (size (ta-type-size ty))
         (base (+ (ta-byte-offset ta) (* i size)))
         (bytes (ta-bytes ta)))
    (dotimes (b size)
      (setf (aref bytes (+ base b)) (logand (ash u (* -8 b)) #xFF)))))

(defun atomics-rmw (args op)
  "AtomicReadModifyWrite: OP maps (old-bits value-bits) -> new bits (wrapped
   to the element width here). Returns the OLD element value."
  (let ((ta (arg 0 args)))
    (atomics-validate ta nil)
    (let* ((i (atomics-index ta (arg 1 args)))
           (ty (ta-type-of ta))
           (v (atomics-coerce ty (arg 2 args))))
      (atomics-revalidate ta i)
      (let* ((bits (* 8 (ta-type-size ty)))
             (old-u (atomics-raw-read ta i))
             (v-u (funcall (ta-type-encode ty) v))
             (new-u (ldb (byte bits 0) (funcall op old-u v-u))))
        (atomics-raw-write ta i new-u)
        (funcall (ta-type-decode ty) old-u)))))

(defun atomics-result-object (realm async value)
  "The DoWait result object: { async, value } (plain data properties)."
  (let ((res (make-object :proto (realm-object-proto realm))))
    (put res "async" (js-bool async))
    (put res "value" value)
    res))

(defun atomics-do-wait (realm args mode)
  "DoWait(mode, typedArray, index, value, timeout). Single-agent world: nobody
   can ever notify us, so an equal value + finite timeout sleeps (bounded) and
   times out; 'not-equal' works exactly per spec. CanBlock is treated as true
   (the runner skips CanBlockIsFalse-flagged tests)."
  (let ((ta (arg 0 args)))
    (atomics-validate ta t)
    ;; wait (unlike notify) requires a shared backing buffer, and the check
    ;; runs BEFORE index/value/timeout coercion.
    (unless (shared-array-buffer-p (ta-buffer ta))
      (js-throw (make-native-error "TypeError"
                 "Atomics.wait requires a SharedArrayBuffer-backed typed array")))
    (let* ((i (atomics-index ta (arg 1 args)))
           (ty (ta-type-of ta))
           (v (atomics-coerce ty (arg 2 args)))     ; ToInt32 / ToBigInt64
           (q (to-number (arg 3 args)))             ; ToNumber(timeout)
           (timeout (if (js-nan-p q) *inf* (max 0d0 q)))
           (old-u (atomics-raw-read ta i))
           (v-u (funcall (ta-type-encode ty) v))
           (sync (eq mode :sync)))
      (cond
        ((/= old-u v-u)
         (if sync "not-equal" (atomics-result-object realm nil "not-equal")))
        ((and (not sync) (<= timeout 0d0))
         (atomics-result-object realm nil "timed-out"))
        (sync
         ;; No other agent exists to notify: waiting always times out. Sleep
         ;; the (finite, bounded) timeout for observable elapsed-time honesty;
         ;; an infinite timeout would hang the host — report timed-out instead
         ;; (single-agent limitation; real blocking tests need $262.agent).
         (when (and (plusp timeout) (/= timeout *inf*))
           (sleep (min (/ timeout 1000d0) 3d0)))
         "timed-out")
        (t
         ;; async mode with a positive timeout: {async: true, value: promise}.
         ;; The promise resolves "timed-out" (immediately — no waiters possible).
         (let* ((pctor (js-get (realm-global realm) "Promise"))
                (value (if (and (js-object-p pctor) (js-callable-p (js-get pctor "resolve")))
                           (js-call (js-get pctor "resolve") pctor (list "timed-out"))
                           "timed-out")))
           (atomics-result-object realm t value)))))))

(defun install-atomics (realm)
  (let* ((op (realm-object-proto realm))
         (ns (make-object :proto op :class "Atomics")))
    ;; ---- read-modify-write family ----
    (def-method realm ns "add" 3 (this args) (atomics-rmw args #'+))
    (def-method realm ns "sub" 3 (this args) (atomics-rmw args #'-))
    (def-method realm ns "and" 3 (this args) (atomics-rmw args #'logand))
    (def-method realm ns "or" 3 (this args) (atomics-rmw args #'logior))
    (def-method realm ns "xor" 3 (this args) (atomics-rmw args #'logxor))
    (def-method realm ns "exchange" 3 (this args)
      (atomics-rmw args (lambda (old v) (declare (ignore old)) v)))
    (def-method realm ns "compareExchange" 4 (this args)
      (let ((ta (arg 0 args)))
        (atomics-validate ta nil)
        (let* ((i (atomics-index ta (arg 1 args)))
               (ty (ta-type-of ta))
               ;; expectedValue is coerced before replacementValue
               (expected (atomics-coerce ty (arg 2 args)))
               (replacement (atomics-coerce ty (arg 3 args))))
          (atomics-revalidate ta i)
          (let ((old-u (atomics-raw-read ta i))
                (exp-u (funcall (ta-type-encode ty) expected)))
            (when (= old-u exp-u)
              (atomics-raw-write ta i (funcall (ta-type-encode ty) replacement)))
            (funcall (ta-type-decode ty) old-u)))))
    ;; ---- load / store ----
    (def-method realm ns "load" 2 (this args)
      (let ((ta (arg 0 args)))
        (atomics-validate ta nil)
        (let ((i (atomics-index ta (arg 1 args))))
          (funcall (ta-type-decode (ta-type-of ta)) (atomics-raw-read ta i)))))
    (def-method realm ns "store" 3 (this args)
      (let ((ta (arg 0 args)))
        (atomics-validate ta nil)
        (let* ((i (atomics-index ta (arg 1 args)))
               (ty (ta-type-of ta))
               (v (atomics-coerce ty (arg 2 args))))
          (atomics-revalidate ta i)
          (atomics-raw-write ta i (funcall (ta-type-encode ty) v))
          ;; store returns the coerced value UNwrapped (e.g. 300 stored into an
          ;; Int8Array returns 300; an out-of-range bigint returns itself).
          v)))
    ;; ---- isLockFree ----
    (def-method realm ns "isLockFree" 1 (this args)
      (let ((n (to-integer-or-infinity (arg 0 args))))
        (js-bool (and (floatp n) (member n '(1d0 2d0 4d0 8d0) :test #'=)))))
    ;; ---- wait / waitAsync / notify / pause ----
    (def-method realm ns "wait" 4 (this args) (atomics-do-wait realm args :sync))
    (def-method realm ns "waitAsync" 4 (this args) (atomics-do-wait realm args :async))
    (def-method realm ns "notify" 3 (this args)
      (let ((ta (arg 0 args)))
        (atomics-validate ta t)
        (atomics-index ta (arg 1 args))
        ;; count: undefined -> +inf, else max(ToIntegerOrInfinity, 0) — the
        ;; coercion is observable (may throw) even though nobody can be waiting.
        (let ((c-arg (arg 2 args)))
          (unless (js-undefined-p c-arg)
            (to-integer-or-infinity c-arg)))
        ;; non-shared buffers return +0 here too; with no agents there are
        ;; never waiters to wake, so the result is always +0.
        0d0))
    (def-method realm ns "pause" 0 (this args)
      (let ((n (arg 0 args)))
        (unless (js-undefined-p n)
          (unless (and (floatp n) (not (js-nan-p n))
                       (/= n *inf*) (/= n *-inf*)
                       (= n (with-js-floats (ftruncate n))))
            (js-throw (make-native-error "TypeError"
                       "pause: iterationNumber must be an integral Number"))))
        *undefined*))
    ;; @@toStringTag
    (put ns (symbol-tostringtag realm) "Atomics"
         :enumerable nil :writable nil :configurable t)
    (define-global realm "Atomics" ns)
    ;; Global namespace binding must be non-enumerable.
    (def-value (realm-global realm) "Atomics" ns)))

(register-builtin-installer 'install-atomics)
