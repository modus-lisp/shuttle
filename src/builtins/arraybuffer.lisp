;;;; builtins/arraybuffer.lisp — ArrayBuffer (byte store, slice, byteLength, isView).
;;;; Backing store: a CL (simple-array (unsigned-byte 8) (*)) in js-object-primitive.
;;;; See array-iteration.lisp for the convention + available helpers.
(in-package #:shuttle)

;;; ---- backing-store accessors (shared with typedarray.lisp / dataview.lisp) ----
(defun ab-bytes (o)
  "The (unsigned-byte 8) vector backing an ArrayBuffer, or NIL if detached."
  (and (js-object-p o) (js-object-primitive o)))
(defun (setf ab-bytes) (v o) (setf (js-object-primitive o) v))

(defun array-buffer-p (o)
  (and (js-object-p o) (getf (js-object-internal o) :array-buffer)))
(defun ab-detached-p (o)
  (and (array-buffer-p o) (null (js-object-primitive o))))

(defun make-byte-vector (n)
  (make-array n :element-type '(unsigned-byte 8) :initial-element 0))

(defvar *arraybuffer-proto* nil)
(defparameter +max-byte-length+ (* 1 1024 1024 1024)) ; 1 GiB allocation ceiling

(defun make-array-buffer (bytes &optional (proto *arraybuffer-proto*) max-byte-length)
  "Wrap a byte vector as a new ArrayBuffer object.
   MAX-BYTE-LENGTH non-nil marks the buffer resizable."
  (let ((o (make-object :proto proto :class "ArrayBuffer")))
    (setf (getf (js-object-internal o) :array-buffer) t)
    (when max-byte-length
      (setf (getf (js-object-internal o) :max-byte-length) max-byte-length))
    (setf (js-object-primitive o) bytes)
    o))

(defun ab-resizable-p (o) (and (array-buffer-p o) (getf (js-object-internal o) :max-byte-length)))
(defun ab-max-byte-length (o) (getf (js-object-internal o) :max-byte-length))

(defun guard-alloc (n)
  "Throw RangeError rather than exhaust the host heap for absurd sizes."
  (when (> n +max-byte-length+)
    (js-throw (make-native-error "RangeError" "Array buffer allocation failed")))
  n)

(defun ab-proto-from-newtarget (nt default-proto)
  "GetPrototypeFromConstructor: nt.prototype if an object, else DEFAULT-PROTO."
  (if (js-object-p nt)
      (let ((p (js-get nt "prototype")))
        (if (js-object-p p) p default-proto))
      default-proto))

(defun install-arraybuffer (realm)
  (let* ((op (realm-object-proto realm))
         (proto (make-object :proto op :class "ArrayBuffer"))
         (ctor (native-function realm "ArrayBuffer"
                 (lambda (this args) (declare (ignore this args))
                   (js-throw (make-native-error "TypeError"
                              "Constructor ArrayBuffer requires 'new'")))
                 1)))
    (setf *arraybuffer-proto* proto)
    (setf (js-object-construct ctor)
          (lambda (args nt)
            (let* ((len (to-index (arg 0 args)))
                   (maxlen (get-max-byte-length-option (arg 1 args))))
              (when (and maxlen (> len maxlen))
                (js-throw (make-native-error "RangeError" "length exceeds maxByteLength")))
              ;; OrdinaryCreateFromConstructor reads nt.prototype (may throw) BEFORE
              ;; CreateByteDataBlock allocates / range-checks the size.
              (let ((rproto (ab-proto-from-newtarget nt proto)))
                (when maxlen (guard-alloc maxlen))
                (guard-alloc len)
                (make-array-buffer (make-byte-vector len) rproto maxlen)))))
    (def-value ctor "prototype" proto :writable nil :configurable nil)
    (def-value proto "constructor" ctor)
    ;; static isView(arg) — true iff arg is a TypedArray or DataView
    (def-method realm ctor "isView" 1 (this args)
      (let ((v (arg 0 args)))
        (js-bool (and (js-object-p v)
                      (or (getf (js-object-internal v) :typed-array)
                          (getf (js-object-internal v) :data-view))))))
    ;; get ArrayBuffer[@@species]  → this
    (let ((species (well-known-species realm)))
      (when species
        (put-accessor ctor species
                      :get (native-function realm "get [Symbol.species]"
                             (lambda (this args) (declare (ignore args)) this) 0)
                      :enumerable nil :configurable t)))
    ;; ---- prototype ----
    (def-getter realm proto "byteLength"
      (lambda (this args) (declare (ignore args))
        (unless (array-buffer-p this)
          (js-throw (make-native-error "TypeError" "not an ArrayBuffer")))
        (let ((b (ab-bytes this))) (float (if b (length b) 0) 1d0))))
    (def-method realm proto "slice" 2 (this args)
      (unless (array-buffer-p this)
        (js-throw (make-native-error "TypeError" "not an ArrayBuffer")))
      (when (ab-detached-p this)
        (js-throw (make-native-error "TypeError" "Cannot slice a detached ArrayBuffer")))
      (let* ((b (ab-bytes this)) (len (length b))
             (start (clamp-rel (arg 0 args) len))
             (end (if (js-undefined-p (arg 1 args)) len (clamp-rel (arg 1 args) len)))
             (new-len (max 0 (- end start)))
             (out (make-byte-vector new-len)))
        ;; re-check detachment after coercion side effects
        (when (ab-detached-p this)
          (js-throw (make-native-error "TypeError" "Cannot slice a detached ArrayBuffer")))
        (let ((src (ab-bytes this)))
          (dotimes (i new-len)
            (when (< (+ start i) (length src))
              (setf (aref out i) (aref src (+ start i))))))
        (make-array-buffer out proto)))
    ;; get detached
    (def-getter realm proto "detached"
      (lambda (this args) (declare (ignore args))
        (unless (array-buffer-p this)
          (js-throw (make-native-error "TypeError" "not an ArrayBuffer")))
        (js-bool (ab-detached-p this))))
    ;; get resizable
    (def-getter realm proto "resizable"
      (lambda (this args) (declare (ignore args))
        (unless (array-buffer-p this)
          (js-throw (make-native-error "TypeError" "not an ArrayBuffer")))
        (js-bool (ab-resizable-p this))))
    ;; get maxByteLength
    (def-getter realm proto "maxByteLength"
      (lambda (this args) (declare (ignore args))
        (unless (array-buffer-p this)
          (js-throw (make-native-error "TypeError" "not an ArrayBuffer")))
        (cond ((ab-detached-p this) 0d0)
              ((ab-resizable-p this) (float (ab-max-byte-length this) 1d0))
              (t (float (length (ab-bytes this)) 1d0)))))
    ;; resize(newLength)
    (def-method realm proto "resize" 1 (this args)
      (unless (ab-resizable-p this)
        (js-throw (make-native-error "TypeError" "ArrayBuffer is not resizable")))
      ;; ToIntegerOrInfinity(newLength) runs BEFORE the (single) detach check
      ;; (spec 25.1.6.x steps 3-4); its coercion is observable even on an already
      ;; detached buffer.
      (let ((new-len (to-integer-or-infinity (arg 0 args)))
            (maxlen (ab-max-byte-length this)))
        (when (ab-detached-p this)
          (js-throw (make-native-error "TypeError" "ArrayBuffer is detached")))
        (when (or (< new-len 0) (= new-len *inf*) (> new-len maxlen))
          (js-throw (make-native-error "RangeError" "Invalid ArrayBuffer resize length")))
        (let* ((n (truncate new-len)) (old (ab-bytes this))
               (out (make-byte-vector n)))
          (dotimes (i (min n (length old))) (setf (aref out i) (aref old i)))
          (setf (ab-bytes this) out)
          *undefined*)))
    ;; transfer / transferToFixedLength — ArrayBufferCopyAndDetach. Both copy the
    ;; contents and detach the source. transfer() preserves resizability (a
    ;; resizable source yields a resizable dest with the same maxByteLength);
    ;; transferToFixedLength always yields a fixed-length dest.
    (flet ((do-transfer (this args preserve)
             (unless (array-buffer-p this)
               (js-throw (make-native-error "TypeError" "not an ArrayBuffer")))
             (when (ab-detached-p this)
               (js-throw (make-native-error "TypeError" "ArrayBuffer is detached")))
             (let* ((old (ab-bytes this))
                    (new-len (if (js-undefined-p (arg 0 args)) (length old)
                                 (let ((n (to-integer-or-infinity (arg 0 args))))
                                   (when (or (< n 0) (= n *inf*))
                                     (js-throw (make-native-error "RangeError" "Invalid length")))
                                   (truncate n))))
                    ;; preserve resizability: a resizable source keeps its maxByteLength.
                    (maxlen (and preserve (ab-resizable-p this) (ab-max-byte-length this))))
               (when maxlen (guard-alloc maxlen))
               (guard-alloc new-len)
               (when (ab-detached-p this)
                 (js-throw (make-native-error "TypeError" "ArrayBuffer is detached")))
               (let* ((src (ab-bytes this))
                      (copy (min new-len (length src)))
                      (out (make-byte-vector new-len)))
                 (dotimes (i copy) (setf (aref out i) (aref src i)))
                 (ab-detach this)
                 (make-array-buffer out proto maxlen)))))
      (def-method realm proto "transfer" 0 (this args) (do-transfer this args t))
      (def-method realm proto "transferToFixedLength" 0 (this args) (do-transfer this args nil)))
    ;; @@toStringTag
    (put proto (symbol-tostringtag realm) "ArrayBuffer"
         :enumerable nil :writable nil :configurable t)
    (define-global realm "ArrayBuffer" ctor)
    ;; Global constructor bindings must be non-enumerable (define-global leaves the
    ;; global-object property enumerable); fix the attributes here.
    (def-value (realm-global realm) "ArrayBuffer" ctor)
    ;; ---- $262 host hooks: detachArrayBuffer (used pervasively by TA tests) ----
    (install-262-hooks realm)))

(defun get-max-byte-length-option (options)
  "GetArrayBufferMaxByteLengthOption: nil if options is not an object or
   maxByteLength is undefined; else ToIndex(options.maxByteLength)."
  (if (js-object-p options)
      (let ((m (js-get options "maxByteLength")))
        (if (js-undefined-p m) nil (to-index m)))
      nil))

(defun clamp-rel (v len)
  "Clamp a relative index (negative counts from end) to [0, len]."
  (let ((i (to-integer-or-infinity v)))
    (cond ((= i *-inf*) 0)
          ((< i 0) (max 0 (+ len (truncate i))))
          ((= i *inf*) len)
          (t (min len (truncate i))))))

(defun to-index (v)
  "ToIndex: ToIntegerOrInfinity, then require [0, 2^53-1], else RangeError."
  (let ((n (to-integer-or-infinity v)))
    (when (or (< n 0) (> n 9007199254740991d0))
      (js-throw (make-native-error "RangeError" "Invalid typed array length")))
    (truncate n)))

(defun well-known-species (realm)
  (let ((sym (ignore-errors (js-get (js-get (realm-global realm) "Symbol") "species"))))
    (and (js-symbol-p sym) sym)))

(defun ab-detach (o)
  "Detach an ArrayBuffer: drop its backing store (used by $262.detachArrayBuffer)."
  (when (array-buffer-p o) (setf (js-object-primitive o) nil))
  *undefined*)

(defun install-262-hooks (realm)
  "Provide a minimal $262 with detachArrayBuffer (test262's $DETACHBUFFER needs it).
   Only installs if $262 is not already present."
  (unless (js-truthy* (js-has (realm-global realm) "$262"))
    (let ((host (make-object :proto (realm-object-proto realm))))
      (def-method realm host "detachArrayBuffer" 1 (this args)
        (ab-detach (arg 0 args)))
      (def-value host "global" (realm-global realm))
      (define-global realm "$262" host))))

(register-builtin-installer 'install-arraybuffer)
