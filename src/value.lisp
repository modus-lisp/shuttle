;;;; value.lisp — JS value model + the object internal-method protocol.
;;;;
;;;; JS values are CL values: numbers = double-float, strings = CL string
;;;; (UTF-16-code-unit semantics are a TODO — see README), booleans/undefined/
;;;; null = singletons, objects = js-object. Every object's behavior is its
;;;; internal methods ([[Get]]/[[Set]]/[[Call]]/…); ordinary objects use the
;;;; defaults here, while HOST objects (weft's DOM) and exotics/Proxy override
;;;; them via the INTERNAL slot. That one factoring is both spec-correct and the
;;;; seam a consumer hangs bindings (and weft's reflow hook) on.
(in-package #:shuttle)

(define-condition shuttle-error (error)
  ((value :initarg :value :reader shuttle-error-value))
  (:report (lambda (c s) (format s "Uncaught ~a" (ignore-errors (to-string (shuttle-error-value c)))))))
(defun js-throw (value) (error 'shuttle-error :value (if (stringp value) value value)))

;;; ---- singletons ----
(defstruct (js-singleton (:print-object (lambda (o s) (format s "#<js ~a>" (js-singleton-name o))))) name)
(defparameter *undefined* (make-js-singleton :name "undefined"))
(defparameter *null*      (make-js-singleton :name "null"))
(defparameter *true*      (make-js-singleton :name "true"))
(defparameter *false*     (make-js-singleton :name "false"))
(declaim (inline js-bool js-undefined-p))
(defun js-bool (x) (if x *true* *false*))
(defun js-undefined-p (x) (eq x *undefined*))

;;; ---- IEEE-754 specials (JS never traps on float ops) ----
(defmacro with-js-floats (&body body)
  `(sb-int:with-float-traps-masked (:invalid :overflow :divide-by-zero) ,@body))
(defparameter *inf*  sb-ext:double-float-positive-infinity)
(defparameter *-inf* sb-ext:double-float-negative-infinity)
(defparameter *nan*  (with-js-floats (- *inf* *inf*)))
(declaim (inline js-nan-p))
(defun js-nan-p (x) (and (floatp x) (/= x x)))

;;; ---- objects + property descriptors ----
(defstruct (prop (:constructor make-prop))
  value get set (writable t) (enumerable t) (configurable t) (accessor nil))

(defstruct (js-object (:constructor %make-object))
  (props (make-hash-table :test 'equal))
  (proto *null*)            ; [[Prototype]]
  (extensible t)
  (class "Object")          ; loosely [[Class]] / internal kind
  (internal nil)            ; plist of internal-method overrides (host objects)
  (call nil)                ; [[Call]]      : (this args-list) -> value
  (construct nil))          ; [[Construct]] : (args-list new-target) -> object

(defun make-object (&key (proto *null*) (class "Object") call construct internal)
  (%make-object :proto proto :class class :call call :construct construct :internal internal))

(declaim (inline prop-key))
(defun prop-key (k) (if (stringp k) k (to-string k)))

;;; ---- internal-method dispatch (override hook, then ordinary) ----
(macrolet ((defop (name trap ordinary args)
             (let ((call (remove-if (lambda (s) (member s '(&optional &rest &key))) args)))
               `(defun ,name (o ,@args)
                  (if (js-object-p o)
                      (let ((tr (and (js-object-internal o) (getf (js-object-internal o) ,trap))))
                        (if tr (funcall tr o ,@call) (,ordinary o ,@call)))
                      (,ordinary o ,@call))))))
  (defop js-get    :get    ordinary-get    (key &optional receiver))
  (defop js-set    :set    ordinary-set    (key v &optional receiver))
  (defop js-has    :has    ordinary-has    (key))
  (defop js-delete :delete ordinary-delete (key))
  (defop js-own-keys :own-keys ordinary-own-keys ()))

(defun ordinary-get (o key &optional (receiver o))
  (if (js-object-p o)
      (let ((d (gethash (prop-key key) (js-object-props o))))
        (cond (d (if (prop-accessor d)
                     (if (prop-get d) (js-call (prop-get d) receiver '()) *undefined*)
                     (prop-value d)))
              ((js-object-p (js-object-proto o)) (js-get (js-object-proto o) key receiver))
              (t *undefined*)))
      *undefined*))

(defun ordinary-set (o key v &optional (receiver o))
  (declare (ignore receiver))
  (let* ((k (prop-key key)) (d (gethash k (js-object-props o))))
    (cond ((and d (prop-accessor d)) (when (prop-set d) (js-call (prop-set d) o (list v))) *true*)
          ((and d (not (prop-writable d))) *false*)
          (d (setf (prop-value d) v) *true*)
          ((js-object-extensible o) (setf (gethash k (js-object-props o)) (make-prop :value v)) *true*)
          (t *false*))))

(defun ordinary-has (o key)
  (let ((k (prop-key key)))
    (or (nth-value 1 (gethash k (js-object-props o)))
        (and (js-object-p (js-object-proto o)) (eq *true* (js-has (js-object-proto o) k))))))
(defun ordinary-delete (o key) (remhash (prop-key key) (js-object-props o)) *true*)
(defun ordinary-own-keys (o)
  (loop for k being the hash-keys of (js-object-props o) collect k))

(defun put (o key value &key (enumerable t) (writable t) (configurable t))
  "Define an own data property (internal helper for building intrinsics)."
  (setf (gethash (prop-key key) (js-object-props o))
        (make-prop :value value :enumerable enumerable :writable writable :configurable configurable))
  o)

;;; ---- [[Call]] / [[Construct]] ----
(defun js-callable-p (f) (and (js-object-p f) (js-object-call f)))
(defun js-call (f this args)
  (unless (js-callable-p f) (js-throw (format nil "~a is not a function" (to-string f))))
  (funcall (js-object-call f) this args))
(defun js-construct (f args &optional (new-target f))
  (unless (and (js-object-p f) (js-object-construct f))
    (js-throw (format nil "~a is not a constructor" (to-string f))))
  (funcall (js-object-construct f) args new-target))

;;; ===========================================================================
;;; Abstract operations (spec coercions)
;;; ===========================================================================
(defun js-truthy (v)
  (cond ((eq v *true*) t) ((member v (list *false* *undefined* *null*)) nil)
        ((stringp v) (plusp (length v)))
        ((floatp v) (not (or (zerop v) (js-nan-p v))))
        (t t)))
(defun to-boolean (v) (js-bool (js-truthy v)))

(defun to-primitive (v &optional hint)
  (if (js-object-p v)
      (let ((order (if (eq hint :string) '("toString" "valueOf") '("valueOf" "toString"))))
        (dolist (m order (js-throw "Cannot convert object to primitive value"))
          (let ((fn (js-get v m)))
            (when (js-callable-p fn)
              (let ((r (js-call fn v '()))) (unless (js-object-p r) (return r)))))))
      v))

(defun to-number (v)
  (cond ((floatp v) v)
        ((eq v *true*) 1d0) ((eq v *false*) 0d0)
        ((eq v *null*) 0d0) ((eq v *undefined*) *nan*)
        ((stringp v) (string-to-number v))
        ((js-object-p v) (to-number (to-primitive v :number)))
        (t *nan*)))

(defun string-to-number (s)
  (let ((s (string-trim '(#\Space #\Tab #\Newline #\Return #\Page) s)))
    (cond ((string= s "") 0d0)
          ((string= s "Infinity") *inf*) ((string= s "+Infinity") *inf*)
          ((string= s "-Infinity") *-inf*)
          (t (or (ignore-errors
                   (let ((*read-default-float-format* 'double-float))
                     (multiple-value-bind (v n) (read-from-string s nil nil)
                       (and (realp v) (= n (length s)) (float v 1d0)))))
                 *nan*)))))

(defun number-to-string (n)
  (cond ((js-nan-p n) "NaN") ((= n *inf*) "Infinity") ((= n *-inf*) "-Infinity")
        ((zerop n) "0")
        ((= n (with-js-floats (ftruncate n))) (format nil "~d" (truncate n)))
        (t (let ((*read-default-float-format* 'double-float)) ; crude; shortest-roundtrip dtoa = TODO
             (string-right-trim "." (format nil "~f" n))))))

(defun to-string (v)
  (cond ((stringp v) v) ((floatp v) (number-to-string v))
        ((eq v *undefined*) "undefined") ((eq v *null*) "null")
        ((eq v *true*) "true") ((eq v *false*) "false")
        ((js-object-p v) (to-string (to-primitive v :string)))
        (t (princ-to-string v))))

(defun js-typeof (v)
  (cond ((eq v *undefined*) "undefined")
        ((or (eq v *true*) (eq v *false*)) "boolean")
        ((floatp v) "number") ((stringp v) "string")
        ((eq v *null*) "object")
        ((js-callable-p v) "function")
        ((js-object-p v) "object") (t "object")))

(defun js-strict-equal (a b)
  (cond ((and (floatp a) (floatp b)) (and (not (js-nan-p a)) (not (js-nan-p b)) (= a b)))
        ((and (stringp a) (stringp b)) (string= a b))
        (t (eq a b))))

(defun js-equal (a b)             ; loose == (the common cases)
  (cond ((eq (js-null-or-undef a) (js-null-or-undef b)) (and (js-null-or-undef a) t))
        ((js-strict-equal a b) t)
        ((and (floatp a) (stringp b)) (js-strict-equal a (to-number b)))
        ((and (stringp a) (floatp b)) (js-strict-equal (to-number a) b))
        ((or (eq a *true*) (eq a *false*)) (js-equal (to-number a) b))
        ((or (eq b *true*) (eq b *false*)) (js-equal a (to-number b)))
        ((and (js-object-p a) (not (js-object-p b)) (not (js-null-or-undef b))) (js-equal (to-primitive a) b))
        ((and (js-object-p b) (not (js-object-p a)) (not (js-null-or-undef a))) (js-equal a (to-primitive b)))
        (t nil)))
(defun js-null-or-undef (x) (or (eq x *null*) (eq x *undefined*)))

(defun js-add (a b)
  (let ((pa (to-primitive a)) (pb (to-primitive b)))
    (if (or (stringp pa) (stringp pb))
        (concatenate 'string (to-string pa) (to-string pb))
        (with-js-floats (+ (to-number pa) (to-number pb))))))
