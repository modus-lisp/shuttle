;;;; builtins/dataview.lisp — DataView (getInt8..setFloat64, byteLength/byteOffset/
;;;; buffer). Reads/writes the backing ArrayBuffer with a per-call endianness flag.
(in-package #:shuttle)

(defun data-view-p (o)
  (and (js-object-p o) (getf (js-object-internal o) :data-view)))
(defun dv-buffer (o) (getf (js-object-internal o) :dv-buffer))
(defun dv-byte-offset (o) (getf (js-object-internal o) :dv-offset))
(defun dv-byte-length (o) (getf (js-object-internal o) :dv-length))
(defun dv-detached-p (o) (ab-detached-p (dv-buffer o)))

(defvar *dataview-proto* nil)

;;; ---- element codecs (little/big endian aware) ----
(defun dv-read-uint (o byte-index size)
  "Read SIZE bytes as an unsigned integer; LITTLE governs byte order."
  (let ((bytes (ab-bytes (dv-buffer o)))
        (base (+ (dv-byte-offset o) byte-index)))
    (values bytes base)))

(defun read-bytes-uint (bytes base size little)
  (let ((u 0))
    (if little
        (dotimes (b size) (setf u (logior u (ash (aref bytes (+ base b)) (* 8 b)))))
        (dotimes (b size) (setf u (logior (ash u 8) (aref bytes (+ base b))))))
    u))

(defun write-bytes-uint (bytes base size little u)
  (if little
      (dotimes (b size) (setf (aref bytes (+ base b)) (logand (ash u (* -8 b)) #xFF)))
      (dotimes (b size) (setf (aref bytes (+ base (- size 1 b))) (logand (ash u (* -8 b)) #xFF)))))

(defstruct (dv-kind (:constructor make-dv-kind)) name size signed float)

(defparameter *dv-kinds*
  (list (make-dv-kind :name "Int8"  :size 1 :signed t)
        (make-dv-kind :name "Uint8" :size 1)
        (make-dv-kind :name "Int16" :size 2 :signed t)
        (make-dv-kind :name "Uint16":size 2)
        (make-dv-kind :name "Int32" :size 4 :signed t)
        (make-dv-kind :name "Uint32":size 4)
        (make-dv-kind :name "Float32":size 4 :float t)
        (make-dv-kind :name "Float64":size 8 :float t)))

(defun dv-decode (u kind)
  (let ((size (dv-kind-size kind)))
    (cond
      ((dv-kind-float kind)
       (if (= size 4) (bits-float32 u) (bits-float64 u)))
      ((dv-kind-signed kind)
       (let ((bits (* 8 size)))
         (float (if (>= u (ash 1 (1- bits))) (- u (ash 1 bits)) u) 1d0)))
      (t (float u 1d0)))))

(defun dv-encode (val kind)
  (let ((size (dv-kind-size kind)))
    (cond
      ((dv-kind-float kind)
       (if (= size 4) (float32-bits val) (float64-bits val)))
      (t (int-modular val (* 8 size))))))

(defun install-dataview (realm)
  (let* ((op (realm-object-proto realm))
         (proto (make-object :proto op :class "DataView"))
         (ctor (native-function realm "DataView"
                 (lambda (this args) (declare (ignore this args))
                   (js-throw (make-native-error "TypeError" "Constructor DataView requires 'new'")))
                 1)))
    (setf *dataview-proto* proto)
    (setf (js-object-construct ctor)
          (lambda (args nt)
            (let ((buffer (arg 0 args)))
              (unless (array-buffer-p buffer)
                (js-throw (make-native-error "TypeError" "First argument must be an ArrayBuffer")))
              (let* ((offset (to-index (arg 1 args))))
                (when (ab-detached-p buffer)
                  (js-throw (make-native-error "TypeError" "buffer is detached")))
                (let ((buflen (length (ab-bytes buffer))))
                  (when (> offset buflen)
                    (js-throw (make-native-error "RangeError" "byteOffset out of range")))
                  (let ((view-len
                          (if (js-undefined-p (arg 2 args))
                              (- buflen offset)
                              (let ((l (to-index (arg 2 args))))
                                (when (> (+ offset l) buflen)
                                  (js-throw (make-native-error "RangeError" "length out of range")))
                                l))))
                    ;; OrdinaryCreateFromConstructor reads nt.prototype (may run user
                    ;; code that detaches the buffer) BEFORE the final detach re-check.
                    (let ((rproto (proto-from-newtarget nt proto)))
                      (when (ab-detached-p buffer)
                        (js-throw (make-native-error "TypeError" "buffer is detached")))
                    (let ((o (make-object :proto rproto :class "DataView")))
                      (setf (getf (js-object-internal o) :data-view) t
                            (getf (js-object-internal o) :dv-buffer) buffer
                            (getf (js-object-internal o) :dv-offset) offset
                            (getf (js-object-internal o) :dv-length) view-len)
                      o))))))))
    (def-value ctor "prototype" proto :writable nil :configurable nil)
    (def-value proto "constructor" ctor)
    ;; ---- getters ----
    (def-getter realm proto "buffer"
      (lambda (this args) (declare (ignore args))
        (unless (data-view-p this) (js-throw (make-native-error "TypeError" "not a DataView")))
        (dv-buffer this)))
    (def-getter realm proto "byteLength"
      (lambda (this args) (declare (ignore args))
        (unless (data-view-p this) (js-throw (make-native-error "TypeError" "not a DataView")))
        (when (dv-detached-p this) (js-throw (make-native-error "TypeError" "buffer is detached")))
        (float (dv-byte-length this) 1d0)))
    (def-getter realm proto "byteOffset"
      (lambda (this args) (declare (ignore args))
        (unless (data-view-p this) (js-throw (make-native-error "TypeError" "not a DataView")))
        (when (dv-detached-p this) (js-throw (make-native-error "TypeError" "buffer is detached")))
        (float (dv-byte-offset this) 1d0)))
    ;; ---- get*/set* methods ----
    (dolist (kind *dv-kinds*)
      (let* ((k kind) (size (dv-kind-size kind))
             (gname (concatenate 'string "get" (dv-kind-name kind)))
             (sname (concatenate 'string "set" (dv-kind-name kind))))
        (def-method realm proto gname 1 (this args)
          (unless (data-view-p this) (js-throw (make-native-error "TypeError" "not a DataView")))
          (let* ((idx (to-index (arg 0 args)))
                 ;; Int8/Uint8 ignore the endianness arg (size 1)
                 (little (if (= size 1) t (js-truthy (arg 1 args)))))
            (when (dv-detached-p this) (js-throw (make-native-error "TypeError" "buffer is detached")))
            (when (> (+ idx size) (dv-byte-length this))
              (js-throw (make-native-error "RangeError" "Offset is outside the bounds of the DataView")))
            (let ((bytes (ab-bytes (dv-buffer this)))
                  (base (+ (dv-byte-offset this) idx)))
              (dv-decode (read-bytes-uint bytes base size little) k))))
        (def-method realm proto sname 2 (this args)
          (unless (data-view-p this) (js-throw (make-native-error "TypeError" "not a DataView")))
          (let* ((idx (to-index (arg 0 args)))
                 (num (to-number (arg 1 args)))
                 (little (if (= size 1) t (js-truthy (arg 2 args)))))
            (when (dv-detached-p this) (js-throw (make-native-error "TypeError" "buffer is detached")))
            (when (> (+ idx size) (dv-byte-length this))
              (js-throw (make-native-error "RangeError" "Offset is outside the bounds of the DataView")))
            (let ((bytes (ab-bytes (dv-buffer this)))
                  (base (+ (dv-byte-offset this) idx)))
              (write-bytes-uint bytes base size little (dv-encode num k)))
            *undefined*))))
    ;; @@toStringTag
    (put proto (symbol-tostringtag realm) "DataView" :enumerable nil :writable nil :configurable t)
    (define-global realm "DataView" ctor)
    ;; Global constructor binding must be non-enumerable.
    (def-value (realm-global realm) "DataView" ctor)))

(register-builtin-installer 'install-dataview)
