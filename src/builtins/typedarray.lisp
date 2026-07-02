;;;; builtins/typedarray.lisp — %TypedArray% abstract superclass + the concrete
;;;; integer/float constructors, plus integer-indexed exotic get/set and the
;;;; prototype method family. Backing store is the ArrayBuffer's byte vector
;;;; See array-iteration.lisp for the convention + available helpers.
(in-package #:shuttle)

;;; ===========================================================================
;;; Element-type descriptors
;;; ===========================================================================
(defstruct (ta-type (:constructor make-ta-type))
  name size signed float clamped bigint
  ;; encode: (element-value) -> unsigned integer of SIZE bytes ; decode: (uint) -> element-value
  ;; For number types the element value is a JS double; for bigint types it is a CL integer.
  encode decode)

(defun clamp-to-uint8 (x)
  "ToUint8Clamp: round-half-to-even, clamp to [0,255]. X is a double."
  (cond ((js-nan-p x) 0)
        ((<= x 0d0) 0)
        ((>= x 255d0) 255)
        (t (let* ((f (ffloor x)) (frac (- x f)))
             (cond ((< frac 0.5d0) (truncate f))
                   ((> frac 0.5d0) (truncate (+ f 1)))
                   ;; exactly .5 → round to even
                   (t (let ((fi (truncate f))) (if (evenp fi) fi (1+ fi)))))))))

(defun int-modular (x bits)
  "ToIntN/ToUintN modular reduction; returns the unsigned bit pattern (uint)."
  (if (or (js-nan-p x) (= (abs x) *inf*)) 0
      (mod (truncate x) (ash 1 bits))))

(defun float32-bits (d)
  "IEEE-754 single-precision bit pattern (unsigned 32-bit) of double D."
  (with-js-floats
    (sb-kernel:single-float-bits (coerce d 'single-float))))
(defun bits-float32 (u)
  (let ((s (sb-kernel:make-single-float (if (>= u #x80000000) (- u #x100000000) u))))
    (float s 1d0)))
(defun float64-bits (d)
  (with-js-floats
    (let ((hi (sb-kernel:double-float-high-bits d))
          (lo (sb-kernel:double-float-low-bits d)))
      (logior (ash (logand hi #xFFFFFFFF) 32) (logand lo #xFFFFFFFF)))))
(defun bits-float64 (u)
  (let* ((hi (ldb (byte 32 32) u)) (lo (ldb (byte 32 0) u)))
    (sb-kernel:make-double-float (if (>= hi #x80000000) (- hi #x100000000) hi) lo)))

(defparameter *ta-types* nil) ; alist name -> ta-type

(defun build-ta-types ()
  (list
   (make-ta-type :name "Int8Array" :size 1 :signed t
     :encode (lambda (x) (int-modular x 8))
     :decode (lambda (u) (float (if (>= u #x80) (- u #x100) u) 1d0)))
   (make-ta-type :name "Uint8Array" :size 1
     :encode (lambda (x) (int-modular x 8))
     :decode (lambda (u) (float u 1d0)))
   (make-ta-type :name "Uint8ClampedArray" :size 1 :clamped t
     :encode (lambda (x) (clamp-to-uint8 x))
     :decode (lambda (u) (float u 1d0)))
   (make-ta-type :name "Int16Array" :size 2 :signed t
     :encode (lambda (x) (int-modular x 16))
     :decode (lambda (u) (float (if (>= u #x8000) (- u #x10000) u) 1d0)))
   (make-ta-type :name "Uint16Array" :size 2
     :encode (lambda (x) (int-modular x 16))
     :decode (lambda (u) (float u 1d0)))
   (make-ta-type :name "Int32Array" :size 4 :signed t
     :encode (lambda (x) (int-modular x 32))
     :decode (lambda (u) (float (if (>= u #x80000000) (- u #x100000000) u) 1d0)))
   (make-ta-type :name "Uint32Array" :size 4
     :encode (lambda (x) (int-modular x 32))
     :decode (lambda (u) (float u 1d0)))
   (make-ta-type :name "Float32Array" :size 4 :float t
     :encode (lambda (x) (float32-bits x))
     :decode (lambda (u) (bits-float32 u)))
   (make-ta-type :name "Float64Array" :size 8 :float t
     :encode (lambda (x) (float64-bits x))
     :decode (lambda (u) (bits-float64 u)))
   ;; ---- 64-bit BigInt element types (elements are CL integers, i.e. bigints) ----
   (make-ta-type :name "BigInt64Array" :size 8 :signed t :bigint t
     ;; encode: a bigint -> its 64-bit two's-complement bit pattern (uint64)
     :encode (lambda (x) (ldb (byte 64 0) x))
     :decode (lambda (u) (if (>= u #x8000000000000000) (- u #x10000000000000000) u)))
   (make-ta-type :name "BigUint64Array" :size 8 :bigint t
     :encode (lambda (x) (ldb (byte 64 0) x))
     :decode (lambda (u) u))))

;;; ===========================================================================
;;; TypedArray instance internals (stored in the :internal plist)
;;;   :typed-array T  :ta-type <ta-type>  :ta-buffer <ArrayBuffer>
;;;   :ta-offset <byte offset>  :ta-length <element count>
;;; ===========================================================================
(defun typed-array-p (o)
  (and (js-object-p o) (getf (js-object-internal o) :typed-array)))
(defun ta-type-of (o) (getf (js-object-internal o) :ta-type))
(defun ta-buffer (o) (getf (js-object-internal o) :ta-buffer))
(defun ta-track-p (o)
  "A length-tracking view: no explicit length over a resizable buffer."
  (getf (js-object-internal o) :ta-track))
(defun ta-raw-offset (o) (getf (js-object-internal o) :ta-offset))
(defun ta-raw-length (o) (getf (js-object-internal o) :ta-length))
(defun ta-detached-p (o) (ab-detached-p (ta-buffer o)))

(defun ta-out-of-bounds-p (o)
  "IsTypedArrayOutOfBounds: the view no longer fits in the current buffer.
   Detached counts as out of bounds."
  (let ((buf (ta-buffer o)))
    (or (ab-detached-p buf)
        (let ((buflen (length (ab-bytes buf)))
              (offset (ta-raw-offset o)))
          (cond
            ((ta-track-p o) (> offset buflen))    ; auto-length: only OOB if offset past end
            (t (> (+ offset (* (ta-raw-length o) (ta-type-size (ta-type-of o))))
                  buflen)))))))

(defun ta-elt-length (o)
  "Current element length of O against the CURRENT buffer size.
   0 if out of bounds; auto-length views recompute; fixed views keep their length."
  (cond
    ((ta-out-of-bounds-p o) 0)
    ((ta-track-p o)
     (let ((buf (ta-buffer o)))
       (floor (- (length (ab-bytes buf)) (ta-raw-offset o))
              (ta-type-size (ta-type-of o)))))
    (t (ta-raw-length o))))

(defun ta-byte-offset (o)
  "Current byteOffset: 0 if out of bounds, else the stored offset."
  (if (ta-out-of-bounds-p o) 0 (ta-raw-offset o)))

(defun ta-bytes (o) (ab-bytes (ta-buffer o)))

(defun ta-read (o i)
  "Read element I of typed array O as a JS double."
  (let* ((ty (ta-type-of o)) (size (ta-type-size ty))
         (base (+ (ta-byte-offset o) (* i size)))
         (bytes (ta-bytes o)) (u 0))
    (dotimes (b size)                    ; little-endian
      (setf u (logior u (ash (aref bytes (+ base b)) (* 8 b)))))
    (funcall (ta-type-decode ty) u)))

(defun ta-read-or-undef (o i)
  "Read element I via [[Get]] semantics: undefined if the index is now invalid
   (e.g. buffer detached mid-operation)."
  (if (ta-valid-index-p o (float i 1d0)) (ta-read o i) *undefined*))

(defun ta-write (o i val)
  "Write JS double VAL into element I of typed array O (already coerced number)."
  (let* ((ty (ta-type-of o)) (size (ta-type-size ty))
         (base (+ (ta-byte-offset o) (* i size)))
         (bytes (ta-bytes o))
         (u (funcall (ta-type-encode ty) val)))
    (dotimes (b size)
      (setf (aref bytes (+ base b)) (logand (ash u (* -8 b)) #xFF)))
    val))

(defun ta-coerce-element (o val)
  "Coerce a JS value to the element type of typed array O: ToBigInt for the
   bigint element types (throws TypeError on a Number), ToNumber otherwise (which
   itself throws TypeError on a BigInt). Returns the coerced element value."
  (if (ta-type-bigint (ta-type-of o)) (to-bigint val) (to-number val)))

(defun ta-coerce-element-ty (ty val)
  "Like TA-COERCE-ELEMENT but keyed on a ta-type directly (used at construction
   time before the instance exists)."
  (if (ta-type-bigint ty) (to-bigint val) (to-number val)))

;;; ---- canonical numeric index detection ----
(defun canonical-numeric-index (key)
  "If KEY is a canonical numeric index, return its numeric value (double), else NIL.
   Accepts a CL double key directly (VM passes numeric indices as doubles) and a
   canonical numeric-index string (ToString(ToNumber(key)) === key)."
  (cond
    ((floatp key) key)                   ; VM member access with a numeric key
    ((stringp key)
     (cond ((string= key "-0") -0d0)
           (t (let ((n (ignore-errors (string-to-number-strict key))))
                (and n (string= (number-to-string n) key) n)))))
    (t nil)))

(defun string-to-number-strict (s)
  "ToNumber for a would-be numeric key. Returns double or NIL for non-numeric."
  (cond ((string= s "Infinity") *inf*)
        ((string= s "-Infinity") *-inf*)
        ((string= s "NaN") *nan*)
        (t (let ((v (string-to-number s)))
             ;; string-to-number returns 0d0 for "" and non-numerics; guard those
             (if (and (zerop v) (not (member s '("0" "0.0" "-0" "+0") :test #'string=))
                      (not (every (lambda (c) (member c '(#\0 #\. #\Space))) s)))
                 (if (string= (number-to-string v) s) v nil)
                 v)))))

(defun ta-valid-index-p (o n)
  "IsValidIntegerIndex: N (a double) is an in-bounds integer index of O."
  (and (floatp n) (not (js-nan-p n)) (not (ta-out-of-bounds-p o))
       (not (js-negative-zero-p n))
       (= n (ftruncate n))
       (<= 0 n) (< n (ta-elt-length o))))

;;; ===========================================================================
;;; Integer-indexed exotic internal methods (installed via :internal plist)
;;; ===========================================================================
(defun ta-internal-get (o key receiver)
  (let ((idx (canonical-numeric-index key)))
    (if idx
        (if (ta-valid-index-p o idx) (ta-read o (truncate idx)) *undefined*)
        (ordinary-get o key (or receiver o)))))

(defun ta-internal-set (o key v receiver)
  ;; IntegerIndexedSet (10.4.5.5):
  ;;   canonical numeric index P:
  ;;     if SameValue(O, Receiver): IntegerIndexedElementSet; return true.
  ;;     if not a valid integer index: return true (drop write).
  ;;   otherwise OrdinarySet(O, P, V, Receiver).
  (let ((idx (canonical-numeric-index key)))
    (cond
      ((and idx (or (null receiver) (eq o receiver)))
       ;; ToNumber/ToBigInt runs even for out-of-bounds (observable side effects,
       ;; and the wrong primitive type throws TypeError before any range check).
       (let ((num (ta-coerce-element o v)))
         (when (ta-valid-index-p o idx) (ta-write o (truncate idx) num)))
       *true*)
      (idx
       ;; Receiver differs from O. If the index is not valid on O, the write is
       ;; silently dropped (return true). If it IS valid, O.[[GetOwnProperty]]
       ;; yields a (data) descriptor, so OrdinarySetWithOwnDescriptor writes to
       ;; Receiver via its OWN [[DefineOwnProperty]] — never O's prototype setter.
       (if (ta-valid-index-p o idx)
           (ta-set-on-receiver (or receiver o) (prop-key key) v)
           *true*))
      (t (ordinary-set o key v (or receiver o))))))

(defun ta-set-on-receiver (receiver k v)
  "OrdinarySetWithOwnDescriptor with a DATA ownDesc (from O's exotic
   [[GetOwnProperty]]): write V into RECEIVER via its own [[GetOwnProperty]] /
   [[DefineOwnProperty]] (so a typed-array receiver coerces + stores properly)."
  (unless (js-object-p receiver) (return-from ta-set-on-receiver *false*))
  (let ((existing (js-get-own-property receiver k)))
    (cond
      ((null existing)
       (js-bool (js-define-own-property receiver k
                  (list :value v :writable t :enumerable t :configurable t))))
      ((prop-accessor existing) *false*)
      ((not (prop-writable existing)) *false*)
      (t (js-bool (js-define-own-property receiver k (list :value v)))))))

(defun ta-internal-has (o key)
  ;; The :has trap contract is a CL boolean (like ORDINARY-HAS), NOT a JS boolean:
  ;; the `in` operator wraps the result in JS-BOOL, and *false* is non-nil in CL.
  (let ((idx (canonical-numeric-index key)))
    (if idx
        (and (ta-valid-index-p o idx) t)
        ;; OrdinaryHasProperty: own prop or (robustly) walk the prototype chain.
        (let ((k (prop-key key)))
          (and (or (nth-value 1 (gethash k (js-object-props o)))
                   (let ((p (js-object-proto o)))
                     (and (js-object-p p) (js-truthy* (js-has p k)))))
               t)))))

(defun ta-internal-delete (o key)
  ;; :delete trap returns a JS boolean (the `delete` opcode pushes it as the
  ;; expression value; ORDINARY-DELETE likewise returns *true*/*false*).
  (let ((idx (canonical-numeric-index key)))
    (if idx (js-bool (not (ta-valid-index-p o idx))) (ordinary-delete o key))))

(defun ta-internal-get-own (o key)
  (let ((idx (canonical-numeric-index key)))
    (if idx
        (when (ta-valid-index-p o idx)
          (make-prop :value (ta-read o (truncate idx))
                     :writable t :enumerable t :configurable t))
        (gethash (prop-key key) (js-object-props o)))))

(defun ta-internal-define-own (o key desc)
  (let ((idx (canonical-numeric-index key)))
    (if idx
        (cond ((not (ta-valid-index-p o idx)) nil)
              ((and (present-p desc :configurable) (not (getf desc :configurable))) nil)
              ((and (present-p desc :enumerable) (not (getf desc :enumerable))) nil)
              ((getf desc :accessor) nil)
              ((and (present-p desc :writable) (not (getf desc :writable))) nil)
              (t (when (present-p desc :value)
                   ;; ToNumber/ToBigInt may detach; re-validate before writing
                   ;; (write is a no-op if the buffer is now detached / index
                   ;; invalid), but the define still succeeds.
                   (let ((num (ta-coerce-element o (getf desc :value))))
                     (when (ta-valid-index-p o idx) (ta-write o (truncate idx) num))))
                 t))
        (js-define-own-property-ordinary o (prop-key key) desc))))

(defun js-define-own-property-ordinary (o k desc)
  "Ordinary [[DefineOwnProperty]] bypassing the internal trap (for the else branch)."
  (let ((saved (js-object-internal o)))
    (unwind-protect
         (progn (setf (js-object-internal o) nil)
                (js-define-own-property o k desc))
      (setf (js-object-internal o) saved))))

(defun ta-internal-own-keys (o)
  "Integer indices [0,len) ascending as strings, then ordinary string/symbol keys."
  (let ((out '()))
    (unless (ta-detached-p o)
      (dotimes (i (ta-elt-length o)) (push (princ-to-string i) out)))
    (setf out (nreverse out))
    (let ((strs '()) (syms '()))
      (dolist (k (%own-keys-in-order o))
        (cond ((js-symbol-p k) (push k syms))
              ((not (canonical-numeric-index k)) (push k strs))))
      (nconc out (nreverse strs) (nreverse syms)))))

(defun ta-install-traps (o)
  (setf (getf (js-object-internal o) :get) #'ta-internal-get
        (getf (js-object-internal o) :set) #'ta-internal-set
        (getf (js-object-internal o) :has) #'ta-internal-has
        (getf (js-object-internal o) :delete) #'ta-internal-delete
        (getf (js-object-internal o) :get-own-property) #'ta-internal-get-own
        (getf (js-object-internal o) :define-own-property) #'ta-internal-define-own
        (getf (js-object-internal o) :own-keys) #'ta-internal-own-keys)
  o)

;;; ===========================================================================
;;; Construction
;;; ===========================================================================
(defvar *typedarray-proto* nil)
(defvar *ta-proto-by-name* nil)  ; hash name -> concrete prototype

(defun make-typed-array (ty buffer offset length proto &optional track)
  (let ((o (make-object :proto proto :class (ta-type-name ty))))
    (setf (getf (js-object-internal o) :typed-array) t
          (getf (js-object-internal o) :ta-type) ty
          (getf (js-object-internal o) :ta-buffer) buffer
          (getf (js-object-internal o) :ta-offset) offset
          (getf (js-object-internal o) :ta-length) length
          (getf (js-object-internal o) :ta-track) track)
    (ta-install-traps o)
    o))

(defun ta-from-length (ty len proto)
  (let* ((size (ta-type-size ty))
         (bytes (guard-alloc (* len size)))
         (buf (make-array-buffer (make-byte-vector bytes))))
    (make-typed-array ty buf 0 len proto)))

(defun ta-from-buffer (ty buffer byte-offset length-arg proto)
  (unless (array-buffer-p buffer)
    (js-throw (make-native-error "TypeError" "First argument must be an ArrayBuffer")))
  (let* ((size (ta-type-size ty))
         (offset (to-index byte-offset)))
    (unless (zerop (mod offset size))
      (js-throw (make-native-error "RangeError" "byteOffset not aligned")))
    (when (ab-detached-p buffer)
      (js-throw (make-native-error "TypeError" "buffer is detached")))
    (let ((buflen (length (ab-bytes buffer))))
      (if (js-undefined-p length-arg)
          (if (ab-resizable-p buffer)
              ;; length-tracking view over a resizable buffer: length auto-updates.
              (progn
                (when (> offset buflen)
                  (js-throw (make-native-error "RangeError" "byteOffset out of range")))
                (make-typed-array ty buffer offset (truncate (- buflen offset) size) proto t))
              (progn
                (unless (zerop (mod buflen size))
                  (js-throw (make-native-error "RangeError" "buffer length not a multiple of element size")))
                (when (> offset buflen)
                  (js-throw (make-native-error "RangeError" "byteOffset out of range")))
                (make-typed-array ty buffer offset (truncate (- buflen offset) size) proto)))
          (let* ((newlen (to-index length-arg))
                 (bytes-needed (* newlen size)))
            (when (> (+ offset bytes-needed) buflen)
              (js-throw (make-native-error "RangeError" "length out of range")))
            (make-typed-array ty buffer offset newlen proto))))))

(defun ta-from-typedarray (ty src proto)
  ;; A source that is detached OR a fixed-length view over a shrunk resizable
  ;; buffer (now out of bounds) throws TypeError.
  (when (ta-out-of-bounds-p src)
    (js-throw (make-native-error "TypeError" "source is out of bounds or detached")))
  ;; The content types must match: a bigint array can only be built from a bigint
  ;; array, and a number array from a number array (spec InitializeTypedArrayFromTypedArray).
  (unless (eq (and (ta-type-bigint ty) t)
              (and (ta-type-bigint (ta-type-of src)) t))
    (js-throw (make-native-error "TypeError"
               "Cannot mix BigInt and non-BigInt typed arrays")))
  (let* ((len (ta-elt-length src))
         (o (ta-from-length ty len proto)))
    (dotimes (i len) (ta-write o i (ta-read src i)))
    o))

(defun ta-from-arraylike (ty src proto)
  (let* ((len (to-int-index (js-get src "length")))
         (o (ta-from-length ty len proto)))
    (dotimes (i len)
      (ta-write o i (ta-coerce-element-ty ty (js-get src (princ-to-string i)))))
    o))

(defun ta-from-iterable (ty src proto)
  "Construct from an iterable via its @@iterator, else fall back to array-like.
   If @@iterator is present but not callable, throw TypeError (spec: GetMethod)."
  (let ((itm (and *symbol-iterator* (js-object-p src) (js-get src *symbol-iterator*))))
    (when (and itm (not (js-null-or-undef itm)) (not (js-callable-p itm)))
      (js-throw (make-native-error "TypeError" "@@iterator is not callable"))))
  (if (and *symbol-iterator* (js-object-p src)
           (js-callable-p (js-get src *symbol-iterator*)))
      (let ((vals '()) (it (get-iterator src)))
        (loop (let ((r (iterator-step it)))
                (when (js-truthy (js-get r "done")) (return))
                (push (js-get r "value") vals)))
        (let* ((lst (nreverse vals)) (len (length lst))
               (o (ta-from-length ty len proto)) (i 0))
          (dolist (v lst) (ta-write o i (ta-coerce-element-ty ty v)) (incf i))
          o))
      (ta-from-arraylike ty src proto)))

;;; ===========================================================================
;;; Installer
;;; ===========================================================================
(defun install-typedarray (realm)
  (setf *ta-types* (build-ta-types)
        *ta-proto-by-name* (make-hash-table :test 'equal))
  (let* ((op (realm-object-proto realm))
         (fp (realm-function-proto realm))
         ;; %TypedArray% abstract constructor + its prototype
         (ta-proto (make-object :proto op :class "TypedArray"))
         (ta-ctor (native-function realm "TypedArray"
                    (lambda (this args) (declare (ignore this args))
                      (js-throw (make-native-error "TypeError"
                                 "Abstract class TypedArray not directly constructable")))
                    0)))
    (setf *typedarray-proto* ta-proto)
    (setf (js-object-construct ta-ctor)
          (lambda (args nt) (declare (ignore args nt))
            (js-throw (make-native-error "TypeError"
                       "Abstract class TypedArray not directly constructable"))))
    (def-value ta-ctor "prototype" ta-proto :writable nil :configurable nil)
    (def-value ta-proto "constructor" ta-ctor)
    (install-ta-proto-methods realm ta-proto)
    (install-ta-statics realm ta-ctor)
    ;; @@toStringTag getter on %TypedArray%.prototype
    (put-accessor ta-proto (symbol-tostringtag realm)
                  :get (native-function realm "get [Symbol.toStringTag]"
                         (lambda (this args) (declare (ignore args))
                           (if (typed-array-p this)
                               (ta-type-name (ta-type-of this)) *undefined*)) 0)
                  :enumerable nil :configurable t)
    (define-global realm "TypedArray" ta-ctor) ; not spec-global, but harmless; overwritten below? no.
    ;; Actually %TypedArray% is NOT a global — remove it.
    (js-delete (realm-global realm) "TypedArray")
    (env-remove-binding realm "TypedArray")
    ;; ---- concrete constructors ----
    (dolist (ty *ta-types*)
      (let* ((name (ta-type-name ty)) (size (ta-type-size ty))
             (proto (make-object :proto ta-proto :class name))
             (ctor (native-function realm name
                     (lambda (this args) (declare (ignore this args))
                       (js-throw (make-native-error "TypeError"
                                  (format nil "Constructor ~a requires 'new'" name))))
                     3)))
        (setf (gethash name *ta-proto-by-name*) proto)
        (setf (js-object-proto ctor) ta-ctor) ; Int8Array.__proto__ === %TypedArray%
        (setf (js-object-construct ctor)
              (let ((ty ty) (proto proto))
                (lambda (args nt)
                  (let ((a0 (arg 0 args)))
                    (cond
                      ((not (js-object-p a0))    ; length or undefined
                       ;; ToIndex(length) is observable (throws TypeError on a Symbol)
                       ;; and per test262 runs BEFORE GetPrototypeFromConstructor reads
                       ;; NewTarget.prototype, so coerce the length first.
                       (let ((len (if (js-undefined-p a0) 0 (to-index a0))))
                         (ta-from-length ty len (ab-proto-from-newtarget nt proto))))
                      ((array-buffer-p a0)
                       (ta-from-buffer ty a0 (arg 1 args) (arg 2 args)
                                       (ab-proto-from-newtarget nt proto)))
                      ((typed-array-p a0)
                       (ta-from-typedarray ty a0 (ab-proto-from-newtarget nt proto)))
                      (t (ta-from-iterable ty a0 (ab-proto-from-newtarget nt proto))))))))
        (def-value ctor "prototype" proto :writable nil :configurable nil)
        (def-value proto "constructor" ctor)
        (def-value ctor "BYTES_PER_ELEMENT" (float size 1d0) :writable nil :configurable nil)
        (def-value proto "BYTES_PER_ELEMENT" (float size 1d0) :writable nil :configurable nil)
        (define-global realm name ctor)
        ;; Global constructor binding must be non-enumerable.
        (def-value (realm-global realm) name ctor)))))

(defun env-remove-binding (realm name)
  (remhash name (env-vars (realm-global-env realm))))

;;; ---------------------------------------------------------------------------
;;; %TypedArray%.prototype getters + methods
;;; ---------------------------------------------------------------------------
(defmacro with-ta ((var this) &body body)
  `(let ((,var ,this))
     (unless (typed-array-p ,var)
       (js-throw (make-native-error "TypeError" "not a TypedArray")))
     ,@body))

(defmacro with-ta-v ((var this) &body body)
  "Like WITH-TA but also runs ValidateTypedArray (throws when detached or the
   view is out of bounds w.r.t. the current resizable-buffer size)."
  `(let ((,var ,this))
     (unless (typed-array-p ,var)
       (js-throw (make-native-error "TypeError" "not a TypedArray")))
     (when (ta-out-of-bounds-p ,var)
       (js-throw (make-native-error "TypeError" "TypedArray is out of bounds or backed by a detached ArrayBuffer")))
     ,@body))

(defun ta-length-checked (o)
  (ta-elt-length o))                    ; ta-elt-length already yields 0 when OOB/detached

(defun ta-species-proto (o name)
  "Prototype for a new same-type array created by slice/subarray/map/filter."
  (declare (ignore name))
  (gethash (ta-type-name (ta-type-of o)) *ta-proto-by-name*))

(defun install-ta-proto-methods (realm tp)
  ;; ---- accessor getters ----
  (def-getter realm tp "length"
    (lambda (this args) (declare (ignore args))
      (with-ta (o this) (float (ta-length-checked o) 1d0))))
  (def-getter realm tp "byteLength"
    (lambda (this args) (declare (ignore args))
      (with-ta (o this)
        (if (ta-out-of-bounds-p o) 0d0
            (float (* (ta-elt-length o) (ta-type-size (ta-type-of o))) 1d0)))))
  (def-getter realm tp "byteOffset"
    (lambda (this args) (declare (ignore args))
      (with-ta (o this) (float (ta-byte-offset o) 1d0))))
  (def-getter realm tp "buffer"
    (lambda (this args) (declare (ignore args))
      (with-ta (o this) (ta-buffer o))))
  ;; ---- element access helpers reused below ----
  (flet ((len (o) (ta-length-checked o)))
    (declare (ignorable #'len))
    ;; at(index)
    (def-method realm tp "at" 1 (this args)
      (with-ta-v (o this)
        (let* ((l (len o)) (rel (to-integer-or-infinity (arg 0 args)))
               (k (cond ((= rel *inf*) l) ((= rel *-inf*) -1)
                        ((>= rel 0) (truncate rel)) (t (+ l (truncate rel))))))
          ;; ToIntegerOrInfinity may have resized/detached: read via [[Get]] so an
          ;; index now invalid (view shrank/out of bounds) yields undefined.
          (if (and (>= k 0) (< k l)) (ta-read-or-undef o k) *undefined*))))
    ;; fill(value, start, end)
    (def-method realm tp "fill" 1 (this args)
      (with-ta-v (o this)
        (let* ((l (len o))
               (v (ta-coerce-element o (arg 0 args)))
               (start (clamp-idx (arg 1 args) l 0))
               (end (if (js-undefined-p (arg 2 args)) l (clamp-idx (arg 2 args) l l))))
          ;; Coercions may have resized the buffer: re-validate, then clamp the
          ;; range to the CURRENT length (a length-tracking view may have shrunk).
          (when (ta-out-of-bounds-p o)
            (js-throw (make-native-error "TypeError" "TypedArray is out of bounds")))
          (let ((cur (len o)))
            (setf start (min start cur) end (min end cur)))
          (loop for i from start below end do (ta-write o i v))
          o)))
    ;; copyWithin(target, start, end)
    (def-method realm tp "copyWithin" 2 (this args)
      (with-ta-v (o this)
        (let* ((l (len o))
               (to (clamp-idx (arg 0 args) l 0))
               (from (clamp-idx (arg 1 args) l 0))
               (end (if (js-undefined-p (arg 2 args)) l (clamp-idx (arg 2 args) l l)))
               (count (min (- end from) (- l to))))
          (when (> count 0)
            ;; The index coercions above may have resized/detached the buffer.
            (when (ta-out-of-bounds-p o)
              (js-throw (make-native-error "TypeError" "TypedArray is out of bounds")))
            ;; Re-clamp against the CURRENT length (a length-tracking view may
            ;; have shrunk); drop any indices now past the end.
            (let ((cur (len o)))
              (setf count (max 0 (min count (- cur to) (- cur from)))))
            (let ((tmp (make-array count)))
              (dotimes (i count) (setf (aref tmp i) (ta-read o (+ from i))))
              (dotimes (i count) (ta-write o (+ to i) (aref tmp i)))))
          o)))
    ;; indexOf / lastIndexOf / includes
    (def-method realm tp "indexOf" 1 (this args)
      (with-ta-v (o this)
        (block done
          (let* ((l (len o)) (target (arg 0 args)))
            (when (zerop l) (return-from done -1d0))
            (let ((start (if (>= (length args) 2)
                            (let ((n (to-integer-or-infinity (arg 1 args))))
                              (cond ((= n *inf*) (return-from done -1d0))
                                    ((= n *-inf*) 0)
                                    ((< n 0) (max 0 (+ l (truncate n))))
                                    (t (truncate n))))
                            0)))
            (loop for i from start below l
                  when (and (ta-valid-index-p o (float i 1d0))
                            (js-strict-equal (ta-read o i) target))
                  do (return-from done (float i 1d0)))
            -1d0)))))
    (def-method realm tp "lastIndexOf" 1 (this args)
      (with-ta-v (o this)
        (block done
          (let* ((l (len o)) (target (arg 0 args)))
            (when (zerop l) (return-from done -1d0))
            (let ((start (if (>= (length args) 2)
                            (let ((n (to-integer-or-infinity (arg 1 args))))
                              (cond ((= n *inf*) (1- l))
                                    ((= n *-inf*) (return-from done -1d0))
                                    ((< n 0) (+ l (truncate n)))
                                    (t (min (truncate n) (1- l)))))
                            (1- l))))
            (loop for i from start downto 0
                  when (and (ta-valid-index-p o (float i 1d0))
                            (js-strict-equal (ta-read o i) target))
                  do (return-from done (float i 1d0)))
            -1d0)))))
    (def-method realm tp "includes" 1 (this args)
      (with-ta-v (o this)
        (block done
          (let* ((l (len o)) (target (arg 0 args)))
            (when (zerop l) (return-from done *false*)) ; length checked before ToInteger(fromIndex)
            (let ((start (let ((n (to-integer-or-infinity (arg 1 args))))
                           (cond ((= n *-inf*) 0)
                                 ((= n *inf*) l)
                                 ((< n 0) (max 0 (+ l (truncate n))))
                                 (t (truncate n))))))
              ;; NOTE: len is captured BEFORE ToIntegerOrInfinity; the loop reads via
              ;; Get(), which yields undefined for a now-detached/out-of-bounds index.
              (js-bool (loop for i from start below l
                             thereis (same-value-zero (ta-read-or-undef o i) target))))))))
    ;; join
    (def-method realm tp "join" 1 (this args)
      (with-ta-v (o this)
        ;; len is read BEFORE ToString(separator), which may detach the buffer.
        (let* ((l (len o))
               (sep (if (js-undefined-p (arg 0 args)) "," (to-string (arg 0 args)))))
          (with-output-to-string (s)
            (dotimes (i l) (when (plusp i) (write-string sep s))
              (let ((v (ta-read-or-undef o i))) (unless (js-null-or-undef v) (write-string (to-string v) s))))))))
    ;; reverse (in place)
    (def-method realm tp "reverse" 0 (this args)
      (with-ta-v (o this)
        (let ((l (len o)))
          (dotimes (i (floor l 2))
            (let ((a (ta-read o i)) (b (ta-read o (- l 1 i))))
              (ta-write o i b) (ta-write o (- l 1 i) a))))
        o))
    ;; forEach / map / filter / some / every / find* / reduce*
    (macrolet ((cb (name) `(let ((f (arg 0 args)))
                             (unless (js-callable-p f) (js-throw (make-native-error "TypeError" ,name)))
                             f)))
      ;; NOTE: these iterate a captured length; each element is read via [[Get]]
      ;; (ta-read-or-undef), so a callback that detaches the buffer yields undefined
      ;; for later indices rather than crashing.
      (def-method realm tp "forEach" 1 (this args)
        (with-ta-v (o this)
          (let ((f (cb "not callable")) (ta (arg 1 args)) (l (len o)))
            (dotimes (i l) (js-call f ta (list (ta-read-or-undef o i) (float i 1d0) o)))
            *undefined*)))
      (def-method realm tp "map" 1 (this args)
        (with-ta-v (o this)
          (let* ((f (cb "not callable")) (ta (arg 1 args)) (l (len o))
                 (out (ta-from-length (ta-type-of o) l (ta-species-proto o nil))))
            (dotimes (i l) (ta-write out i (ta-coerce-element out (js-call f ta (list (ta-read-or-undef o i) (float i 1d0) o)))))
            out)))
      (def-method realm tp "filter" 1 (this args)
        (with-ta-v (o this)
          (let ((f (cb "not callable")) (ta (arg 1 args)) (l (len o)) (kept '()))
            (dotimes (i l)
              (let ((v (ta-read-or-undef o i)))
                (when (js-truthy (js-call f ta (list v (float i 1d0) o))) (push v kept))))
            (let* ((vals (nreverse kept)) (out (ta-from-length (ta-type-of o) (length vals) (ta-species-proto o nil))) (i 0))
              ;; Values are read from O via [[Get]] (same element type as OUT), but a
              ;; resizable-buffer shrink mid-iteration can yield undefined for an
              ;; out-of-bounds index; coerce so those become NaN/0 rather than crash.
              (dolist (v vals)
                (ta-write out i (if (js-undefined-p v) (ta-coerce-element out v) v))
                (incf i))
              out))))
      (def-method realm tp "some" 1 (this args)
        (with-ta-v (o this)
          (let ((f (cb "not callable")) (ta (arg 1 args)) (l (len o)))
            (js-bool (dotimes (i l nil)
                       (when (js-truthy (js-call f ta (list (ta-read-or-undef o i) (float i 1d0) o))) (return t)))))))
      (def-method realm tp "every" 1 (this args)
        (with-ta-v (o this)
          (let ((f (cb "not callable")) (ta (arg 1 args)) (l (len o)))
            (js-bool (dotimes (i l t)
                       (unless (js-truthy (js-call f ta (list (ta-read-or-undef o i) (float i 1d0) o))) (return nil)))))))
      (def-method realm tp "find" 1 (this args)
        (with-ta-v (o this)
          (block done (let ((f (cb "not callable")) (ta (arg 1 args)) (l (len o)))
            (dotimes (i l) (let ((v (ta-read-or-undef o i)))
                             (when (js-truthy (js-call f ta (list v (float i 1d0) o))) (return-from done v))))
            *undefined*))))
      (def-method realm tp "findIndex" 1 (this args)
        (with-ta-v (o this)
          (block done (let ((f (cb "not callable")) (ta (arg 1 args)) (l (len o)))
            (dotimes (i l) (when (js-truthy (js-call f ta (list (ta-read-or-undef o i) (float i 1d0) o))) (return-from done (float i 1d0))))
            -1d0))))
      (def-method realm tp "findLast" 1 (this args)
        (with-ta-v (o this)
          (block done (let ((f (cb "not callable")) (ta (arg 1 args)) (l (len o)))
            (loop for i from (1- l) downto 0 do (let ((v (ta-read-or-undef o i)))
              (when (js-truthy (js-call f ta (list v (float i 1d0) o))) (return-from done v))))
            *undefined*))))
      (def-method realm tp "findLastIndex" 1 (this args)
        (with-ta-v (o this)
          (block done (let ((f (cb "not callable")) (ta (arg 1 args)) (l (len o)))
            (loop for i from (1- l) downto 0 do
              (when (js-truthy (js-call f ta (list (ta-read-or-undef o i) (float i 1d0) o))) (return-from done (float i 1d0))))
            -1d0))))
      (def-method realm tp "reduce" 1 (this args)
        (with-ta-v (o this)
          (let ((f (cb "not callable")) (l (len o)) (acc (arg 1 args)) (has (>= (length args) 2)) (i 0))
            (unless has (when (zerop l) (js-throw (make-native-error "TypeError" "Reduce of empty array with no initial value")))
              (setf acc (ta-read-or-undef o 0) i 1))
            (loop while (< i l) do (setf acc (js-call f *undefined* (list acc (ta-read-or-undef o i) (float i 1d0) o))) (incf i))
            acc)))
      (def-method realm tp "reduceRight" 1 (this args)
        (with-ta-v (o this)
          (let ((f (cb "not callable")) (l (len o)) (acc (arg 1 args)) (has (>= (length args) 2)) (i (1- (len o))))
            (unless has (when (zerop l) (js-throw (make-native-error "TypeError" "Reduce of empty array with no initial value")))
              (setf acc (ta-read-or-undef o (1- l)) i (- l 2)))
            (loop while (>= i 0) do (setf acc (js-call f *undefined* (list acc (ta-read-or-undef o i) (float i 1d0) o))) (decf i))
            acc))))
    ;; slice(begin, end)
    (def-method realm tp "slice" 2 (this args)
      (with-ta-v (o this)
        (let* ((l (len o)) (start (clamp-idx (arg 0 args) l 0))
               (end (if (js-undefined-p (arg 1 args)) l (clamp-idx (arg 1 args) l l)))
               (count (max 0 (- end start)))
               (out (ta-from-length (ta-type-of o) count (ta-species-proto o nil))))
          (when (> count 0)
            ;; The index coercions may have detached/shrunk the buffer.
            (when (ta-out-of-bounds-p o)
              (js-throw (make-native-error "TypeError" "TypedArray is out of bounds or backed by a detached ArrayBuffer")))
            ;; A length-tracking view may have shrunk: copy only the elements that
            ;; still exist; the remaining OUT elements stay zero-filled.
            (let ((cur (len o)))
              (dotimes (i count)
                (when (< (+ start i) cur)
                  (ta-write out i (ta-read o (+ start i)))))))
          out)))
    ;; subarray(begin, end) — shares the SAME buffer.
    ;; srcLength is the CURRENT length (0 if the buffer is detached); both begin
    ;; and end are coerced (observably) against it. The new view is constructed
    ;; through the buffer path, which re-checks detachment and throws TypeError.
    (def-method realm tp "subarray" 2 (this args)
      (with-ta (o this)
        ;; srcLength is the CURRENT element length (0 when the view is out of bounds).
        ;; startIndex/endIndex are clamped against it; beginByteOffset is computed
        ;; from the RAW stored byteOffset (spec step 13), NOT the OOB-adjusted one.
        (let* ((l (ta-elt-length o))
               (start (clamp-idx (arg 0 args) l 0))
               (end-arg (arg 1 args))
               (size (ta-type-size (ta-type-of o)))
               (byte-offset (+ (ta-raw-offset o) (* start size))))
          (if (and (ta-track-p o) (js-undefined-p end-arg))
              ;; auto-length source + end undefined → result is length-tracking too.
              (ta-from-buffer (ta-type-of o) (ta-buffer o)
                              (float byte-offset 1d0) *undefined*
                              (ta-species-proto o nil))
              (let* ((end (if (js-undefined-p end-arg) l (clamp-idx end-arg l l)))
                     (count (max 0 (- end start))))
                (ta-from-buffer (ta-type-of o) (ta-buffer o)
                                (float byte-offset 1d0) (float count 1d0)
                                (ta-species-proto o nil)))))))
    ;; set(source, offset)
    (def-method realm tp "set" 1 (this args)
      (with-ta (o this)
        (let* ((src (arg 0 args))
               ;; ToIntegerOrInfinity(offset) may run user code that detaches O.
               (offset (to-integer-or-infinity (arg 1 args))))
          (when (< offset 0) (js-throw (make-native-error "RangeError" "offset out of range")))
          ;; Re-validate O after coercion side effects: a detached buffer OR a
          ;; fixed-length view now out of bounds (resizable buffer shrank) throws
          ;; BEFORE the source's length/element getters are touched.
          (when (ta-out-of-bounds-p o)
            (js-throw (make-native-error "TypeError" "TypedArray is out of bounds or backed by a detached ArrayBuffer")))
          (let ((targetlen (ta-elt-length o)))
            (if (typed-array-p src)
                (progn
                  ;; The source's out-of-bounds state (detached OR a fixed-length
                  ;; view over a shrunk resizable buffer) throws TypeError.
                  (when (ta-out-of-bounds-p src)
                    (js-throw (make-native-error "TypeError" "source is out of bounds or backed by a detached ArrayBuffer")))
                  ;; Content types must match (SetTypedArrayFromTypedArray).
                  (unless (eq (and (ta-type-bigint (ta-type-of o)) t)
                              (and (ta-type-bigint (ta-type-of src)) t))
                    (js-throw (make-native-error "TypeError"
                               "Cannot mix BigInt and non-BigInt typed arrays")))
                  (let ((slen (ta-elt-length src)))
                    ;; offset can be +Infinity here: any positive slen overflows the target.
                    (when (or (= offset *inf*) (> (+ offset slen) targetlen))
                      (js-throw (make-native-error "RangeError" "source array is too large")))
                    (let ((off (truncate offset)) (tmp (make-array slen)))
                      ;; snapshot the source first (handles overlap + type mismatch)
                      (dotimes (i slen) (setf (aref tmp i) (ta-read src i)))
                      (dotimes (i slen) (ta-write o (+ off i) (aref tmp i))))))
                ;; Array-like source: index via SRC directly (VM member access boxes
                ;; string/number primitives — a ToObject wrapper here would lose
                ;; indexed character access).
                (let ((slen (to-int-index (js-get src "length"))))
                  (when (or (= offset *inf*) (> (+ offset slen) targetlen))
                    (js-throw (make-native-error "RangeError" "source array is too large")))
                  (let ((off (truncate offset)))
                    (dotimes (i slen)
                      (let ((num (ta-coerce-element o (js-get src (princ-to-string i)))))
                        (when (ta-valid-index-p o (float (+ off i) 1d0))
                          (ta-write o (+ off i) num))))))))
          *undefined*)))
    ;; sort(comparefn)
    (def-method realm tp "sort" 1 (this args)
      (with-ta-v (o this)
        (let ((cmp (arg 0 args)) (l (len o)))
          (unless (or (js-undefined-p cmp) (js-callable-p cmp))
            (js-throw (make-native-error "TypeError" "comparefn must be a function")))
          (let ((vals (make-array l)))
            (dotimes (i l) (setf (aref vals i) (ta-read o i)))
            (setf vals (stable-sort vals
                        (if (js-callable-p cmp)
                            (lambda (a b) (< (let ((r (to-number (js-call cmp *undefined* (list a b))))) (if (js-nan-p r) 0d0 r)) 0))
                            #'ta-default-less)))
            ;; The comparator may have detached the buffer; writeback is then a no-op.
            (unless (ta-detached-p o)
              (dotimes (i (min l (ta-length-checked o))) (ta-write o i (aref vals i)))))
          o)))
    (def-method realm tp "toSorted" 1 (this args)
      (with-ta-v (o this)
        (let ((cmp (arg 0 args)) (l (len o)))
          (unless (or (js-undefined-p cmp) (js-callable-p cmp))
            (js-throw (make-native-error "TypeError" "comparefn must be a function")))
          (let ((out (ta-from-length (ta-type-of o) l (ta-species-proto o nil))) (vals (make-array l)))
            (dotimes (i l) (setf (aref vals i) (ta-read o i)))
            (setf vals (stable-sort vals (if (js-callable-p cmp)
                        (lambda (a b) (< (let ((r (to-number (js-call cmp *undefined* (list a b))))) (if (js-nan-p r) 0d0 r)) 0))
                        #'ta-default-less)))
            (dotimes (i l) (ta-write out i (aref vals i)))
            out))))
    (def-method realm tp "toReversed" 0 (this args)
      (with-ta-v (o this)
        (let* ((l (len o)) (out (ta-from-length (ta-type-of o) l (ta-species-proto o nil))))
          (dotimes (i l) (ta-write out i (ta-read o (- l 1 i))))
          out)))
    (def-method realm tp "with" 2 (this args)
      (with-ta-v (o this)
        (let* ((l (len o))
               (rel (to-integer-or-infinity (arg 0 args)))
               ;; actualIndex; keep it as a rational so Infinity doesn't reach truncate.
               (k (cond ((= rel *inf*) l)          ; guaranteed out of range
                        ((= rel *-inf*) -1)        ; guaranteed out of range
                        ((>= rel 0) (truncate rel))
                        (t (+ l (truncate rel)))))
               ;; ToNumber/ToBigInt(value) runs BEFORE the final validity check (spec 23.2.3.36).
               (v (ta-coerce-element o (arg 1 args))))
          ;; IsValidIntegerIndex is evaluated against the CURRENT length.
          (when (or (< k 0) (>= k (ta-length-checked o)))
            (js-throw (make-native-error "RangeError" "index out of range")))
          (let ((out (ta-from-length (ta-type-of o) l (ta-species-proto o nil))))
            (dotimes (i l) (ta-write out i (if (= i k) v (ta-read-or-undef o i))))
            out))))
    ;; toString → the SAME function object as Array.prototype.toString (spec 23.2.3.31)
    (let ((array-tostring (js-get (realm-array-proto realm) "toString")))
      (if (js-callable-p array-tostring)
          (put tp "toString" array-tostring :enumerable nil :writable t :configurable t)
          (def-method realm tp "toString" 0 (this args)
            (let ((j (js-get this "join"))) (if (js-callable-p j) (js-call j this '()) "[object TypedArray]")))))
    (def-method realm tp "toLocaleString" 0 (this args)
      (with-ta-v (o this)
        (let ((l (len o)))
          (with-output-to-string (s)
            (dotimes (i l) (when (plusp i) (write-string "," s))
              ;; A user toLocaleString may shrink the buffer mid-loop; read via
              ;; [[Get]] so a now-out-of-bounds index yields undefined.
              (let ((v (ta-read-or-undef o i)))
                (unless (js-null-or-undef v)
                  ;; spec: call each element's toLocaleString and ToString the result
                  (let ((f (js-get v "toLocaleString")))
                    (write-string (to-string (if (js-callable-p f) (js-call f v '()) v)) s)))))))))
    ;; iterators: keys / values / entries / @@iterator
    (def-method realm tp "keys" 0 (this args)
      (with-ta-v (o this) (make-ta-iterator realm o :key)))
    (def-method realm tp "values" 0 (this args)
      (with-ta-v (o this) (make-ta-iterator realm o :value)))
    (def-method realm tp "entries" 0 (this args)
      (with-ta-v (o this) (make-ta-iterator realm o :entry)))
    ;; %TypedArray%.prototype[@@iterator] is the SAME function object as .values
    (when *symbol-iterator*
      (let ((values-fn (js-get tp "values")))
        (put tp *symbol-iterator* values-fn
             :enumerable nil :writable t :configurable t)))))

(defun ta-default-less (a b)
  "Default TypedArray numeric sort comparator (ascending; NaN last; -0 before +0).
   A and B are element values: JS doubles for the Number arrays, or CL integers
   (bigints) for the BigInt arrays. Bigints have no NaN / no signed zero, so plain
   ascending order applies."
  (cond ((and (integerp a) (integerp b)) (< a b))     ; bigint elements
        ((and (js-nan-p a) (js-nan-p b)) nil)
        ((js-nan-p a) nil) ((js-nan-p b) t)
        ((and (zerop a) (zerop b)) (and (js-negative-zero-p a) (not (js-negative-zero-p b))))
        (t (< a b))))

(defun clamp-idx (v len default)
  "Clamp a relative index to [0,len] (negative from end)."
  (if (js-undefined-p v) default
      (let ((n (to-integer-or-infinity v)))
        (cond ((= n *-inf*) 0) ((= n *inf*) len)
              ((< n 0) (max 0 (+ len (truncate n))))
              (t (min len (truncate n)))))))

(defun make-ta-iterator (realm o kind)
  ;; TypedArray iterators are Array Iterators — they share %ArrayIteratorPrototype%
  ;; (which carries next/@@iterator/@@toStringTag).
  (let ((i 0) (done nil)
        (it (make-object :proto (or *array-iterator-prototype* (realm-object-proto realm))
                         :class "Array Iterator")))
    (def-method realm it "next" 0 (this args)
      (let ((res (make-object :proto (realm-object-proto realm))))
        ;; Once exhausted the iterator stays exhausted, even if the backing
        ;; resizable buffer later grows the typed array back in-bounds.
        (when (not done)
          ;; A fixed-length view that has gone out of bounds (buffer shrank) makes
          ;; the iterator step throw a TypeError.
          (when (ta-out-of-bounds-p o)
            (js-throw (make-native-error "TypeError"
                       "TypedArray is out of bounds or backed by a detached ArrayBuffer"))))
        (let ((l (ta-length-checked o)))
          (if (and (not done) (< i l))
              (progn (put res "value"
                          (ecase kind (:key (float i 1d0)) (:value (ta-read o i))
                            (:entry (make-array-object (list (float i 1d0) (ta-read o i))))))
                     (put res "done" *false*) (incf i))
              (progn (setf done t) (put res "value" *undefined*) (put res "done" *true*))))
        res))
    (unless *array-iterator-prototype*
      (when *symbol-iterator*
        (put it *symbol-iterator* (native-function realm "[Symbol.iterator]" (lambda (this args) (declare (ignore args)) this) 0) :enumerable nil)))
    it))

;;; ---------------------------------------------------------------------------
;;; %TypedArray% statics: from, of
;;; ---------------------------------------------------------------------------
(defun install-ta-statics (realm ta-ctor)
  ;; %TypedArray%.of — this is the constructor
  (def-method realm ta-ctor "of" 0 (this args)
    (unless (and (js-object-p this) (js-object-construct this))
      (js-throw (make-native-error "TypeError" "this is not a constructor")))
    (let* ((len (length args)) (o (js-construct this (list (float len 1d0)))) (i 0))
      (dolist (v args) (js-set o (princ-to-string i) v) (incf i))
      o))
  (def-method realm ta-ctor "from" 1 (this args)
    (unless (and (js-object-p this) (js-object-construct this))
      (js-throw (make-native-error "TypeError" "this is not a constructor")))
    (let ((src (arg 0 args)) (mapf (arg 1 args)) (vals '()))
      (unless (or (js-undefined-p mapf) (js-callable-p mapf))
        (js-throw (make-native-error "TypeError" "mapfn is not callable")))
      (if (and *symbol-iterator* (js-object-p src) (js-callable-p (js-get src *symbol-iterator*)))
          (let ((it (get-iterator src)))
            (loop (let ((r (iterator-step it)))
                    (when (js-truthy (js-get r "done")) (return))
                    (push (js-get r "value") vals))))
          (let* ((so (to-object src)) (l (to-int-index (js-get so "length"))))
            (dotimes (i l) (push (js-get so (princ-to-string i)) vals))))
      (let* ((lst (nreverse vals)) (len (length lst))
             (o (js-construct this (list (float len 1d0)))) (i 0))
        (dolist (v lst)
          (js-set o (princ-to-string i)
                  (if (js-callable-p mapf) (js-call mapf *undefined* (list v (float i 1d0))) v))
          (incf i))
        o)))
  ;; get %TypedArray%[@@species] → this
  (let ((species (well-known-species realm)))
    (when species
      (put-accessor ta-ctor species
                    :get (native-function realm "get [Symbol.species]"
                           (lambda (this args) (declare (ignore args)) this) 0)
                    :enumerable nil :configurable t))))

(register-builtin-installer 'install-typedarray)
