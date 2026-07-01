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

;;; ---- symbols (a distinct primitive value type) ----
(defstruct (js-symbol (:constructor %make-js-symbol) (:print-object (lambda (o s) (format s "#<js Symbol ~a>" (js-symbol-desc o)))))
  desc)                                   ; description (a CL string or nil)
(defun make-js-symbol (&optional desc) (%make-js-symbol :desc (and (not (eq desc *undefined*)) desc)))

;;; ---- objects + property descriptors ----
(defstruct (prop (:constructor make-prop))
  value get set (writable t) (enumerable t) (configurable t) (accessor nil))

(defstruct (js-object (:constructor %make-object))
  (props (make-hash-table :test 'equal))
  (key-order '())           ; own keys in insertion order (reversed); ordinary-own-keys re-sorts
  (proto *null*)            ; [[Prototype]]
  (extensible t)
  (class "Object")          ; loosely [[Class]] / internal kind
  (internal nil)            ; plist of internal-method overrides (host objects)
  (primitive nil)           ; [[NumberData]]/[[StringData]]/[[BooleanData]]/[[SymbolData]] for wrappers
  (call nil)                ; [[Call]]      : (this args-list) -> value
  (construct nil))          ; [[Construct]] : (args-list new-target) -> object

(declaim (inline %key-touch %key-forget %own-keys-in-order))
(defun %key-touch (o k)
  "Record K as an own key of O (idempotent, preserves first-insertion order)."
  (unless (member k (js-object-key-order o) :test #'equal)
    (push k (js-object-key-order o))))
(defun %key-forget (o k)
  (setf (js-object-key-order o) (delete k (js-object-key-order o) :test #'equal)))
(defun %own-keys-in-order (o) (reverse (js-object-key-order o)))  ; insertion order

(defun make-object (&key (proto *null*) (class "Object") call construct internal)
  (%make-object :proto proto :class class :call call :construct construct :internal internal))

(declaim (inline prop-key))
(defun prop-key (k)
  "Coerce a value to a property key: strings and symbols pass through (symbols
   compare by EQ in the EQUAL-tested props table); everything else -> ToString."
  (cond ((stringp k) k) ((js-symbol-p k) k) (t (to-property-key k))))

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

(defun ordinary-get (o key &optional receiver)
  (unless receiver (setf receiver o))
  (cond
    ((js-object-p o)
     (let ((d (gethash (prop-key key) (js-object-props o))))
       (cond (d (if (prop-accessor d)
                    (if (prop-get d) (js-call (prop-get d) receiver '()) *undefined*)
                    (prop-value d)))
             ((js-object-p (js-object-proto o)) (js-get (js-object-proto o) key receiver))
             (t *undefined*))))
    ;; primitive property access: string index/length inline, else box → proto
    ((js-null-or-undef o)
     (js-throw (make-native-error "TypeError"
                                  (format nil "Cannot read properties of ~a (reading '~a')"
                                          (if (eq o *null*) "null" "undefined")
                                          (if (js-symbol-p key) (to-symbol-string key) (to-string key))))))
    (t (primitive-get o key (if (eq receiver o) o receiver)))))

(defun primitive-get (o key receiver)
  "[[Get]] on a primitive value: strings expose length + integer indices without
   allocating a wrapper; otherwise dispatch to the primitive's prototype."
  (declare (ignore receiver))
  (when (stringp o)
    (let ((k (prop-key key)))
      (cond ((and (stringp k) (string= k "length")) (return-from primitive-get (float (length o) 1d0)))
            ((and (stringp k) (array-index-string-p k))
             (let ((i (parse-integer k)))
               (return-from primitive-get
                 (if (< i (length o)) (string (char o i)) *undefined*)))))))
  (let ((proto (primitive-proto o)))
    (if (js-object-p proto) (js-get proto key o) *undefined*)))

(defun primitive-proto (v)
  "The prototype an unboxed primitive dispatches to (from the current realm)."
  (when (boundp '*current-realm*)
    (let ((r (symbol-value '*current-realm*)))
      (cond ((stringp v) (realm-string-proto r))
            ((floatp v) (realm-number-proto r))
            ((or (eq v *true*) (eq v *false*)) (realm-boolean-proto r))
            ((js-symbol-p v) (realm-symbol-proto r))
            (t *null*)))))

(defun js-array-p (o) (and (js-object-p o) (string= (js-object-class o) "Array")))
(defun to-uint32 (v)
  (let ((n (to-number v)))
    (if (or (js-nan-p n) (= n *inf*) (= n *-inf*)) 0 (mod (truncate n) #x100000000))))
(defun array-length (o)
  (let ((ld (gethash "length" (js-object-props o)))) (if ld (truncate (prop-value ld)) 0)))

(defun array-set-length (o v)
  "Array exotic [[Set]] \"length\": coerce to uint32 (RangeError on mismatch);
   when shrinking, delete indices >= new length (highest first, honoring
   non-configurable), then store the new length."
  (let* ((num (to-number v)) (newlen (to-uint32 v)))
    (unless (= newlen num) (js-throw (make-native-error "RangeError" "Invalid array length")))
    (let ((ld (gethash "length" (js-object-props o))))
      (when (and ld (not (prop-writable ld))) (return-from array-set-length *false*))
      (let ((oldlen (if ld (truncate (prop-value ld)) 0)))
        (when (< newlen oldlen)
          (loop for i from (1- oldlen) downto newlen
                for k = (princ-to-string i)
                for d = (gethash k (js-object-props o))
                when d do
                  (if (prop-configurable d)
                      (progn (remhash k (js-object-props o)) (%key-forget o k))
                      (progn (when ld (setf (prop-value ld) (float (1+ i) 1d0)))
                             (return-from array-set-length *false*)))))
        (if ld (setf (prop-value ld) (float newlen 1d0))
            (put o "length" (float newlen 1d0) :enumerable nil))
        *true*))))

(defun ordinary-set (o key v &optional receiver)
  ;; OrdinarySet with the receiver walk: an own data prop on RECEIVER is written;
  ;; an inherited accessor's setter is called with RECEIVER as this.
  (unless receiver (setf receiver o))
  (unless (js-object-p o)
    (when (js-null-or-undef o)
      (js-throw (make-native-error "TypeError" "Cannot set properties of null/undefined")))
    ;; setting on a primitive: walk its proto for an inherited setter, else no-op
    (let ((proto (primitive-proto o)))
      (return-from ordinary-set (if (js-object-p proto) (js-set proto key v o) *false*))))
  ;; ---- Array exotic [[Set]]: length maintenance ----
  (when (and (js-array-p o) (eq o receiver))
    (let ((k (prop-key key)))
      (when (stringp k)
        (cond ((string= k "length") (return-from ordinary-set (array-set-length o v)))
              ((array-index-string-p k)
               (let* ((idx (parse-integer k)) (len (array-length o))
                      (ld (gethash "length" (js-object-props o))))
                 (when (and ld (not (prop-writable ld)) (>= idx len))
                   (return-from ordinary-set *false*))
                 (let ((res (%create-data-on-receiver o k v)))
                   (when (and (eq res *true*) ld (>= idx len))
                     (setf (prop-value ld) (float (1+ idx) 1d0)))
                   (return-from ordinary-set res))))))))
  (let* ((k (prop-key key)) (d (gethash k (js-object-props o))))
    (cond
      ((and d (prop-accessor d))
       (if (prop-set d) (progn (js-call (prop-set d) receiver (list v)) *true*) *false*))
      ((and d (not (prop-writable d))) *false*)
      (d (if (eq o receiver)
             (progn (setf (prop-value d) v) *true*)
             (%create-data-on-receiver receiver k v)))
      ((js-object-p (js-object-proto o)) (js-set (js-object-proto o) key v receiver))
      ((eq o receiver) (%create-data-on-receiver receiver k v))
      (t (%create-data-on-receiver receiver k v)))))

(defun %create-data-on-receiver (receiver k v)
  (if (js-object-p receiver)
      (let ((ex (gethash k (js-object-props receiver))))
        (cond ((and ex (prop-accessor ex)) *false*)
              ((and ex (not (prop-writable ex))) *false*)
              (ex (setf (prop-value ex) v) *true*)
              ((js-object-extensible receiver)
               (setf (gethash k (js-object-props receiver)) (make-prop :value v))
               (%key-touch receiver k) *true*)
              (t *false*)))
      *false*))

(defun ordinary-has (o key)
  (let ((k (prop-key key)))
    (or (nth-value 1 (gethash k (js-object-props o)))
        (and (js-object-p (js-object-proto o)) (js-truthy* (js-has (js-object-proto o) k))))))
(defun ordinary-delete (o key)
  (let* ((k (prop-key key)) (d (gethash k (js-object-props o))))
    (cond ((null d) *true*)
          ((prop-configurable d) (remhash k (js-object-props o)) (%key-forget o k) *true*)
          (t *false*))))
(defun ordinary-own-keys (o)
  ;; Spec order: integer indices ascending, then string keys in insertion order,
  ;; then symbol keys in insertion order.
  (let ((order (%own-keys-in-order o)) (ints '()) (strs '()) (syms '()))
    (dolist (k order)
      (cond ((js-symbol-p k) (push k syms))
            ((array-index-string-p k) (push k ints))
            (t (push k strs))))
    (nconc (sort (nreverse ints) #'< :key (lambda (s) (parse-integer s)))
           (nreverse strs) (nreverse syms))))

(defun array-index-string-p (k)
  "True iff K is a canonical array index string (0 .. 2^32-2)."
  (and (stringp k) (plusp (length k))
       (or (string= k "0")
           (and (char/= (char k 0) #\0)
                (every #'digit-char-p k)
                (ignore-errors (< (parse-integer k) #xFFFFFFFF))))))

(defun put (o key value &key (enumerable t) (writable t) (configurable t))
  "Define an own data property (internal helper for building intrinsics)."
  (let ((k (prop-key key)))
    (setf (gethash k (js-object-props o))
          (make-prop :value value :enumerable enumerable :writable writable :configurable configurable))
    (%key-touch o k))
  o)

(defun put-accessor (o key &key get set (enumerable t) (configurable t))
  "Define an own accessor property (internal helper for building intrinsics)."
  (let ((k (prop-key key)))
    (setf (gethash k (js-object-props o))
          (make-prop :accessor t :get get :set set :enumerable enumerable :configurable configurable))
    (%key-touch o k))
  o)

;;; ---- [[GetOwnProperty]] / [[DefineOwnProperty]] (spec descriptor ops) ----
(defun js-get-own-property (o key)
  "Return the own PROP descriptor for KEY, or NIL. Honors host GET-OWN traps."
  (when (js-object-p o)
    (let ((tr (and (js-object-internal o) (getf (js-object-internal o) :get-own-property))))
      (if tr (funcall tr o (prop-key key))
          (gethash (prop-key key) (js-object-props o))))))

(defun js-define-own-property (o key desc)
  "[[DefineOwnProperty]]. DESC is a PROP-like plist of the FIELDS THAT ARE
   PRESENT (:value/:get/:set/:writable/:enumerable/:configurable/:accessor).
   Returns T on success, NIL on rejection (caller decides throw vs silent)."
  (let ((tr (and (js-object-internal o) (getf (js-object-internal o) :define-own-property))))
    (when tr (return-from js-define-own-property (funcall tr o (prop-key key) desc))))
  (let* ((k (prop-key key)) (cur (gethash k (js-object-props o)))
         (accessor (if (present-p desc :accessor) (getf desc :accessor)
                       (or (present-p desc :get) (present-p desc :set)))))
    (cond
      ;; new property
      ((null cur)
       (unless (js-object-extensible o) (return-from js-define-own-property nil))
       (let ((p (if accessor
                    (make-prop :accessor t
                               :get (if (present-p desc :get) (getf desc :get) *undefined*)
                               :set (if (present-p desc :set) (getf desc :set) *undefined*)
                               :enumerable (and (present-p desc :enumerable) (getf desc :enumerable))
                               :configurable (and (present-p desc :configurable) (getf desc :configurable)))
                    (make-prop :value (if (present-p desc :value) (getf desc :value) *undefined*)
                               :writable (and (present-p desc :writable) (getf desc :writable))
                               :enumerable (and (present-p desc :enumerable) (getf desc :enumerable))
                               :configurable (and (present-p desc :configurable) (getf desc :configurable))))))
         (setf (gethash k (js-object-props o)) p) (%key-touch o k) t))
      ;; existing property — validate against configurable
      (t
       (let ((cfg (prop-configurable cur)))
         ;; reject illegal changes on a non-configurable property
         (when (not cfg)
           (when (and (present-p desc :configurable) (getf desc :configurable))
             (return-from js-define-own-property nil))
           (when (and (present-p desc :enumerable)
                      (not (eq (and (getf desc :enumerable) t) (prop-enumerable cur))))
             (return-from js-define-own-property nil))
           (when (and (present-p desc :accessor) (not (eq accessor (prop-accessor cur))))
             (return-from js-define-own-property nil))
           (if (prop-accessor cur)
               (progn
                 (when (and (present-p desc :get) (not (eq (getf desc :get) (or (prop-get cur) *undefined*))))
                   (return-from js-define-own-property nil))
                 (when (and (present-p desc :set) (not (eq (getf desc :set) (or (prop-set cur) *undefined*))))
                   (return-from js-define-own-property nil)))
               (progn
                 (when (not (prop-writable cur))
                   (when (and (present-p desc :writable) (getf desc :writable))
                     (return-from js-define-own-property nil))
                   (when (and (present-p desc :value)
                              (not (same-value (getf desc :value) (prop-value cur))))
                     (return-from js-define-own-property nil))))))
         ;; apply
         (when (present-p desc :accessor)
           (if accessor
               (setf (prop-accessor cur) t (prop-value cur) *undefined*
                     (prop-writable cur) t
                     (prop-get cur) (if (present-p desc :get) (getf desc :get) (prop-get cur))
                     (prop-set cur) (if (present-p desc :set) (getf desc :set) (prop-set cur)))
               (setf (prop-accessor cur) nil (prop-get cur) nil (prop-set cur) nil
                     (prop-value cur) (if (present-p desc :value) (getf desc :value) *undefined*)
                     (prop-writable cur) (and (present-p desc :writable) (getf desc :writable)))))
         (when (present-p desc :get) (setf (prop-get cur) (getf desc :get) (prop-accessor cur) t))
         (when (present-p desc :set) (setf (prop-set cur) (getf desc :set) (prop-accessor cur) t))
         (when (present-p desc :value) (setf (prop-value cur) (getf desc :value)))
         (when (present-p desc :writable) (setf (prop-writable cur) (and (getf desc :writable) t)))
         (when (present-p desc :enumerable) (setf (prop-enumerable cur) (and (getf desc :enumerable) t)))
         (when (present-p desc :configurable) (setf (prop-configurable cur) (and (getf desc :configurable) t)))
         t)))))

(defparameter +absent+ '#:absent)
(defun present-p (plist key) (not (eq (getf plist key +absent+) +absent+)))

;;; ---- [[Call]] / [[Construct]] ----
(defun js-callable-p (f) (and (js-object-p f) (js-object-call f)))
(defparameter *max-depth* 900) (defvar *depth* 0)   ; bound JS recursion before the CL stack overflows
(defun js-call (f this args)
  (unless (js-callable-p f) (js-throw (make-native-error "TypeError" (format nil "~a is not a function" (to-string f)))))
  (let ((*depth* (1+ *depth*)))
    (when (> *depth* *max-depth*) (js-throw (make-native-error "RangeError" "Maximum call stack size exceeded")))
    (funcall (js-object-call f) this args)))
(defun js-construct (f args &optional (new-target f))
  (unless (and (js-object-p f) (js-object-construct f))
    (js-throw (make-native-error "TypeError" (format nil "~a is not a constructor" (to-string f)))))
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

(defvar *symbol-to-primitive* nil)   ; the @@toPrimitive well-known symbol (set at realm build)
(defun to-primitive (v &optional hint)
  (if (js-object-p v)
      (progn
        ;; @@toPrimitive exotic hook, if present
        (when *symbol-to-primitive*
          (let ((exotic (js-get v *symbol-to-primitive*)))
            (when (js-callable-p exotic)
              (let ((r (js-call exotic v (list (case hint (:string "string") (:number "number") (t "default"))))))
                (if (js-object-p r)
                    (js-throw (make-native-error "TypeError" "Cannot convert object to primitive value"))
                    (return-from to-primitive r))))))
        (let ((order (if (eq hint :string) '("toString" "valueOf") '("valueOf" "toString"))))
          (dolist (m order (js-throw (make-native-error "TypeError" "Cannot convert object to primitive value")))
            (let ((fn (js-get v m)))
              (when (js-callable-p fn)
                (let ((r (js-call fn v '()))) (unless (js-object-p r) (return r))))))))
      v))

(defun to-number (v)
  (cond ((floatp v) v)
        ((eq v *true*) 1d0) ((eq v *false*) 0d0)
        ((eq v *null*) 0d0) ((eq v *undefined*) *nan*)
        ((stringp v) (string-to-number v))
        ((js-symbol-p v) (js-throw (make-native-error "TypeError" "Cannot convert a Symbol value to a number")))
        ((js-object-p v) (to-number (to-primitive v :number)))
        (t *nan*)))

(defparameter +js-ws+ '(#\Space #\Tab #\Newline #\Return #\Page #\Vt #\No-Break_Space #\Line_Separator #\Paragraph_Separator #\U+FEFF))
(defun string-to-number (s)
  (let ((s (string-trim +js-ws+ s)))
    (cond ((string= s "") 0d0)
          ((or (string= s "Infinity") (string= s "+Infinity")) *inf*)
          ((string= s "-Infinity") *-inf*)
          ;; radix literals (no sign allowed per StringNumericLiteral)
          ((and (>= (length s) 2) (char= (char s 0) #\0) (member (char s 1) '(#\x #\X)))
           (or (ignore-errors (float (parse-integer s :start 2 :radix 16) 1d0)) *nan*))
          ((and (>= (length s) 2) (char= (char s 0) #\0) (member (char s 1) '(#\o #\O)))
           (or (ignore-errors (float (parse-integer s :start 2 :radix 8) 1d0)) *nan*))
          ((and (>= (length s) 2) (char= (char s 0) #\0) (member (char s 1) '(#\b #\B)))
           (or (ignore-errors (float (parse-integer s :start 2 :radix 2) 1d0)) *nan*))
          (t (or (parse-js-decimal s) *nan*)))))

(defun parse-js-decimal (s)
  "Parse a JS decimal StringNumericLiteral (optional sign, digits, '.', exponent).
   Returns a double-float or NIL. Rejects trailing junk; '' handled by caller."
  (let ((n (length s)) (i 0) (sign 1d0) (seen-digit nil))
    (when (and (< i n) (member (char s i) '(#\+ #\-)))
      (when (char= (char s i) #\-) (setf sign -1d0)) (incf i))
    (let ((mant-start i))
      (loop while (and (< i n) (digit-char-p (char s i))) do (incf i) (setf seen-digit t))
      (when (and (< i n) (char= (char s i) #\.))
        (incf i)
        (loop while (and (< i n) (digit-char-p (char s i))) do (incf i) (setf seen-digit t)))
      (unless seen-digit (return-from parse-js-decimal nil))
      (progn mant-start)
      (progn
        (when (and (< i n) (member (char s i) '(#\e #\E)))
          (incf i)
          (when (and (< i n) (member (char s i) '(#\+ #\-))) (incf i))
          (let ((exp-digit nil))
            (loop while (and (< i n) (digit-char-p (char s i))) do (incf i) (setf exp-digit t))
            (unless exp-digit (return-from parse-js-decimal nil))))
        (unless (= i n) (return-from parse-js-decimal nil))
        (let ((*read-default-float-format* 'double-float))
          (ignore-errors
            (with-js-floats
              (* sign (float (let ((body (subseq s (if (char= (char s 0) #\+) 1 (if (char= (char s 0) #\-) 1 0)))))
                               (read-from-string (if (char= (char body 0) #\.) (concatenate 'string "0" body) body)))
                             1d0)))))))))

(defun number-to-string (n)
  (cond ((js-nan-p n) "NaN") ((= n *inf*) "Infinity") ((= n *-inf*) "-Infinity")
        ((zerop n) "0")                                    ; both +0 and -0 -> "0"
        ((minusp n) (concatenate 'string "-" (number-to-string (- n))))
        ((= n (with-js-floats (ftruncate n)))
         (if (< n 1d21) (format nil "~d" (truncate n)) (dtoa-exponential n)))
        (t (dtoa n))))

(defun dtoa (n)
  "Shortest round-tripping decimal for a positive finite non-integer double,
   in ECMAScript Number::toString format (fixed vs exponential by magnitude)."
  ;; SBCL's float printer already emits a shortest round-tripping representation.
  (let* ((s (let ((*read-default-float-format* 'double-float)) (prin1-to-string n))))
    ;; s looks like "12.34" or "1.234e10" or "1.0e-5"; normalise to JS.
    (let* ((epos (position #\e s))
           (mant (if epos (subseq s 0 epos) s))
           (exp (if epos (parse-integer s :start (1+ epos)) 0)))
      ;; strip a trailing ".0"
      (when (and (> (length mant) 1) (string= mant ".0" :start1 (- (length mant) 2)))
        (setf mant (subseq mant 0 (- (length mant) 2))))
      (js-format-decimal mant exp))))

(defun dtoa-exponential (n)
  (let ((s (let ((*read-default-float-format* 'double-float)) (prin1-to-string n))))
    (let* ((epos (position #\e s))
           (mant (if epos (subseq s 0 epos) s))
           (exp (if epos (parse-integer s :start (1+ epos)) 0)))
      (js-format-decimal mant exp))))

(defun js-format-decimal (mant exp)
  "Assemble a JS number string from a decimal mantissa string MANT (may contain a
   '.') and base-10 EXP. Chooses fixed vs 'e' notation like ECMAScript does."
  ;; collect significant digits and the position of the decimal point
  (let* ((dot (position #\. mant))
         (digits (remove #\. mant))
         (int-len (if dot dot (length mant)))
         ;; k = number of significant digits, n = exponent so value = digits * 10^(n-k)
         (trimmed (string-right-trim "0" digits)))
    (when (string= trimmed "") (setf trimmed "0"))
    ;; leading zeros -> adjust
    (let* ((lead (or (position-if (lambda (c) (char/= c #\0)) trimmed) 0))
           (sig (subseq trimmed lead))
           (k (length sig))
           (n (+ (- int-len lead) exp)))
      (when (string= sig "") (return-from js-format-decimal "0"))
      (cond
        ((<= k n 21)                     ; integer, pad with zeros
         (concatenate 'string sig (make-string (- n k) :initial-element #\0)))
        ((< 0 n 21)                      ; digits with a decimal point inside
         (concatenate 'string (subseq sig 0 n) "." (subseq sig n)))
        ((< -6 n 1)                      ; 0.00…digits
         (concatenate 'string "0." (make-string (- n) :initial-element #\0) sig))
        (t                               ; exponential
         (let ((e (1- n)))
           (concatenate 'string (subseq sig 0 1)
                        (if (> k 1) (concatenate 'string "." (subseq sig 1)) "")
                        "e" (if (minusp e) "-" "+") (format nil "~d" (abs e)))))))))

(defun to-string (v)
  (cond ((stringp v) v) ((floatp v) (number-to-string v))
        ((eq v *undefined*) "undefined") ((eq v *null*) "null")
        ((eq v *true*) "true") ((eq v *false*) "false")
        ((js-symbol-p v) (js-throw (make-native-error "TypeError" "Cannot convert a Symbol value to a string")))
        ((js-object-p v) (to-string (to-primitive v :string)))
        (t (princ-to-string v))))

(defun js-typeof (v)
  (cond ((eq v *undefined*) "undefined")
        ((or (eq v *true*) (eq v *false*)) "boolean")
        ((floatp v) "number") ((stringp v) "string")
        ((js-symbol-p v) "symbol")
        ((eq v *null*) "object")
        ((js-callable-p v) "function")
        ((js-object-p v) "object") (t "object")))

(defun js-strict-equal (a b)
  (cond ((and (floatp a) (floatp b)) (and (not (js-nan-p a)) (not (js-nan-p b)) (= a b)))
        ((and (stringp a) (stringp b)) (string= a b))
        (t (eq a b))))

(defun js-equal (a b)             ; loose == (the common cases)
  (cond ((or (js-null-or-undef a) (js-null-or-undef b))   ; null/undefined only equal each other
         (and (js-null-or-undef a) (js-null-or-undef b) t))
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

;;; ===========================================================================
;;; More abstract operations (the kernel the built-in library builds on)
;;; ===========================================================================
(declaim (inline js-negative-zero-p))
(defun js-negative-zero-p (x) (and (floatp x) (zerop x) (minusp (float-sign x))))

(defun same-value (a b)
  "SameValue: like ===, but NaN==NaN and +0 != -0."
  (cond ((and (floatp a) (floatp b))
         (cond ((and (js-nan-p a) (js-nan-p b)) t)
               ((and (zerop a) (zerop b)) (eq (js-negative-zero-p a) (js-negative-zero-p b)))
               (t (= a b))))
        ((and (stringp a) (stringp b)) (string= a b))
        (t (eq a b))))

(defun same-value-zero (a b)
  "SameValueZero: like SameValue but +0 == -0 (used by includes/Set/Map)."
  (cond ((and (floatp a) (floatp b))
         (cond ((and (js-nan-p a) (js-nan-p b)) t) (t (= a b))))
        ((and (stringp a) (stringp b)) (string= a b))
        (t (eq a b))))

(defun to-symbol-string (sym)
  "String(Symbol) -> \"Symbol(desc)\" (used by String() and description access)."
  (format nil "Symbol(~a)" (or (js-symbol-desc sym) "")))

(defun to-property-key (v)
  "ToPropertyKey: symbols pass through; everything else -> ToString.
   (Objects with Symbol.toPrimitive/toString are coerced via to-primitive.)"
  (cond ((js-symbol-p v) v)
        ((stringp v) v)
        ((js-object-p v) (let ((p (to-primitive v :string))) (if (js-symbol-p p) p (to-string p))))
        (t (to-string v))))

(defun require-object-coercible (v &optional what)
  "RequireObjectCoercible: null/undefined -> TypeError, else pass through."
  (when (js-null-or-undef v)
    (js-throw (make-native-error "TypeError"
                                 (format nil "~a is ~a" (or what "value") (if (eq v *null*) "null" "undefined")))))
  v)

(defun to-integer-or-infinity (v)
  "ToIntegerOrInfinity: NaN->0, +/-Inf kept, else truncate toward zero (a double)."
  (let ((n (to-number v)))
    (cond ((js-nan-p n) 0d0)
          ((or (= n *inf*) (= n *-inf*)) n)
          (t (with-js-floats (ftruncate n))))))

(defun to-length (v)
  "ToLength: clamp ToIntegerOrInfinity to [0, 2^53-1]."
  (let ((n (to-integer-or-infinity v)))
    (cond ((<= n 0) 0d0)
          ((> n 9007199254740991d0) 9007199254740991d0)
          (t n))))

(defun to-int-index (v)
  "A CL integer index from a JS value (for element access / loops)."
  (let ((n (to-integer-or-infinity v)))
    (if (or (= n *inf*) (= n *-inf*)) 0 (truncate n))))

(defun make-native-error (name message)
  "Build a native Error object of the given constructor name in the current realm.
   Used by CL-side abstract ops that must throw the right JS error type."
  (if (boundp '*current-realm*)
      (let* ((realm (symbol-value '*current-realm*))
             (ctor (ignore-errors (js-get (realm-global realm) name))))
        (if (and ctor (js-object-p ctor) (js-object-construct ctor))
            (js-construct ctor (list message))
            message))
      message))

;;; ToObject: primitives box into their wrapper; the realm supplies the protos.
(defun to-object (v)
  (cond ((js-object-p v) v)
        ((js-null-or-undef v)
         (js-throw (make-native-error "TypeError" "Cannot convert undefined or null to object")))
        (t (box-primitive v))))
;; BOX-PRIMITIVE is defined in vm.lisp once realm protos are available.
