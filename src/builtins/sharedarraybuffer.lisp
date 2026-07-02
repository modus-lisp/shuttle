;;;; builtins/sharedarraybuffer.lisp — SharedArrayBuffer (single-threaded impl:
;;;; same byte-vector representation as ArrayBuffer; cannot be detached;
;;;; Brand: internal :shared-array-buffer (disjoint from :array-buffer — the
;;;; ArrayBuffer.prototype getters reject SABs and vice versa). Predicates
;;;; shared-array-buffer-p / any-array-buffer-p / buffer-resizable-p live in
;;;; arraybuffer.lisp (loaded first) so TypedArray/DataView can use them.
(in-package #:shuttle)

(defvar *sharedarraybuffer-proto* nil)

(defun sab-growable-p (o)
  (and (shared-array-buffer-p o) (getf (js-object-internal o) :max-byte-length) t))
(defun sab-max-byte-length (o) (getf (js-object-internal o) :max-byte-length))

(defun make-shared-array-buffer (bytes proto &optional max-byte-length)
  "Wrap a byte vector as a new SharedArrayBuffer object.
   MAX-BYTE-LENGTH non-nil marks the buffer growable."
  (let ((o (make-object :proto (or proto *sharedarraybuffer-proto*)
                        :class "SharedArrayBuffer")))
    (setf (getf (js-object-internal o) :shared-array-buffer) t)
    (when max-byte-length
      (setf (getf (js-object-internal o) :max-byte-length) max-byte-length))
    (setf (js-object-primitive o) bytes)
    o))

(defun install-sharedarraybuffer (realm)
  (let* ((op (realm-object-proto realm))
         (proto (make-object :proto op :class "SharedArrayBuffer"))
         (ctor (native-function realm "SharedArrayBuffer"
                 (lambda (this args) (declare (ignore this args))
                   (js-throw (make-native-error "TypeError"
                              "Constructor SharedArrayBuffer requires 'new'")))
                 1)))
    (setf *sharedarraybuffer-proto* proto)
    (setf (js-object-construct ctor)
          (lambda (args nt)
            (let* ((len (to-index (arg 0 args)))
                   (maxlen (get-max-byte-length-option (arg 1 args))))
              (when (and maxlen (> len maxlen))
                (js-throw (make-native-error "RangeError" "length exceeds maxByteLength")))
              ;; OrdinaryCreateFromConstructor reads nt.prototype (may throw)
              ;; BEFORE CreateSharedByteDataBlock allocates / range-checks.
              (let ((rproto (ab-proto-from-newtarget nt proto)))
                (when maxlen (guard-alloc maxlen))
                (guard-alloc len)
                (make-shared-array-buffer (make-byte-vector len) rproto maxlen)))))
    (def-value ctor "prototype" proto :writable nil :configurable nil)
    (def-value proto "constructor" ctor)
    ;; get SharedArrayBuffer[@@species] → this
    (let ((species (well-known-species realm)))
      (when species
        (put-accessor ctor species
                      :get (native-function realm "get [Symbol.species]"
                             (lambda (this args) (declare (ignore args)) this) 0)
                      :enumerable nil :configurable t)))
    (flet ((require-sab (this)
             (unless (shared-array-buffer-p this)
               (js-throw (make-native-error "TypeError" "not a SharedArrayBuffer")))))
      ;; ---- prototype getters ----
      (def-getter realm proto "byteLength"
        (lambda (this args) (declare (ignore args))
          (require-sab this)
          (float (length (ab-bytes this)) 1d0)))
      (def-getter realm proto "growable"
        (lambda (this args) (declare (ignore args))
          (require-sab this)
          (js-bool (sab-growable-p this))))
      (def-getter realm proto "maxByteLength"
        (lambda (this args) (declare (ignore args))
          (require-sab this)
          (float (or (sab-max-byte-length this) (length (ab-bytes this))) 1d0)))
      ;; grow(newLength)
      (def-method realm proto "grow" 1 (this args)
        ;; RequireInternalSlot(O, [[ArrayBufferMaxByteLength]]) BEFORE the
        ;; shared check: a fixed SAB and a plain object both fail here; a
        ;; resizable (non-shared) ArrayBuffer passes here and fails the next.
        (unless (and (js-object-p this)
                     (any-array-buffer-p this)
                     (getf (js-object-internal this) :max-byte-length))
          (js-throw (make-native-error "TypeError" "receiver is not a growable buffer")))
        (unless (shared-array-buffer-p this)
          (js-throw (make-native-error "TypeError" "not a SharedArrayBuffer")))
        (let ((new-len (to-integer-or-infinity (arg 0 args)))
              (cur (length (ab-bytes this)))
              (maxlen (sab-max-byte-length this)))
          ;; only growing is allowed: [current, maxByteLength]
          (when (or (< new-len cur) (= new-len *inf*) (> new-len maxlen))
            (js-throw (make-native-error "RangeError" "Invalid SharedArrayBuffer grow length")))
          (let* ((n (truncate new-len)) (old (ab-bytes this))
                 (out (make-byte-vector n)))
            (dotimes (i cur) (setf (aref out i) (aref old i)))
            (setf (ab-bytes this) out))
          *undefined*))
      ;; slice(start, end) — SpeciesConstructor(O, %SharedArrayBuffer%); the
      ;; result must be a SAB, distinct from O, and large enough. SABs cannot
      ;; be detached, so no detach re-checks.
      (def-method realm proto "slice" 2 (this args)
        (require-sab this)
        (let* ((b (ab-bytes this)) (len (length b))
               (start (clamp-rel (arg 0 args) len))
               (end (if (js-undefined-p (arg 1 args)) len (clamp-rel (arg 1 args) len)))
               (new-len (max 0 (- end start)))
               (c (species-constructor realm this ctor))
               (new (js-construct c (list (float new-len 1d0)))))
          (unless (shared-array-buffer-p new)
            (js-throw (make-native-error "TypeError"
                       "Species constructor did not return a SharedArrayBuffer")))
          (when (eq new this)
            (js-throw (make-native-error "TypeError"
                       "Species constructor returned the same SharedArrayBuffer")))
          (when (< (length (ab-bytes new)) new-len)
            (js-throw (make-native-error "TypeError"
                       "Species constructor returned a SharedArrayBuffer that is too small")))
          (let ((src (ab-bytes this)) (dst (ab-bytes new)))
            (dotimes (i new-len)
              (when (< (+ start i) (length src))
                (setf (aref dst i) (aref src (+ start i))))))
          new)))
    ;; @@toStringTag
    (put proto (symbol-tostringtag realm) "SharedArrayBuffer"
         :enumerable nil :writable nil :configurable t)
    (define-global realm "SharedArrayBuffer" ctor)
    ;; Global constructor binding must be non-enumerable.
    (def-value (realm-global realm) "SharedArrayBuffer" ctor)))

(register-builtin-installer 'install-sharedarraybuffer)
