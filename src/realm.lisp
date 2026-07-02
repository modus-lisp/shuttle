;;;; realm.lisp — the consumer API (the seam weft builds DOM bindings on):
;;;; make-realm, eval-script, define-global, make-host-object, native-function,
;;;; invoke. Plus a minimal set of intrinsics (the full built-in library is the
;;;; src/builtins/, one test262-pinned file per group).
(in-package #:shuttle)

(defun native-function (realm name fn &optional (len 0))
  "Wrap a CL function (THIS ARGS-list) -> JS value as a callable JS object.
   .name and .length follow built-in conventions: non-writable, non-enumerable,
   configurable (what test262's verifyCallableProperty checks)."
  (let ((*current-realm* realm))
    (let ((o (make-object :proto (%fn-proto) :class "Function")))
      (setf (js-object-call o) fn)
      (put o "length" (float len 1d0) :enumerable nil :writable nil :configurable t)
      (put o "name" (if (stringp name) name (to-string name)) :enumerable nil :writable nil :configurable t)
      o)))

(defun make-realm ()
  "Create a fresh realm (per-document global environment + intrinsics)."
  (let* ((obj-proto (make-object :proto *null*))
         (fn-proto  (make-object :proto obj-proto :class "Function"))
         (arr-proto (make-object :proto obj-proto :class "Array"))
         (str-proto (make-object :proto obj-proto :class "String"))
         (num-proto (make-object :proto obj-proto :class "Number"))
         (bool-proto (make-object :proto obj-proto :class "Boolean"))
         (sym-proto (make-object :proto obj-proto :class "Symbol"))
         (realm (%make-realm :object-proto obj-proto :function-proto fn-proto :array-proto arr-proto
                             :string-proto str-proto :number-proto num-proto
                             :boolean-proto bool-proto :symbol-proto sym-proto
                             :symbol-registry (make-hash-table :test 'equal))))
    (let ((*current-realm* realm))
      (setf (realm-global realm) (make-object :proto obj-proto)
            (realm-global-env realm) (new-env nil))
      (install-intrinsics realm)
      (define-global realm "globalThis" (realm-global realm))
      realm)))

(defun define-global (realm name value)
  ;; Built-in globals (Object, Array, eval, parseInt, …) are non-enumerable,
  ;; writable, configurable per spec (unlike global `var` bindings).
  (env-declare (realm-global-env realm) name value)
  (put (realm-global realm) name value :enumerable nil)
  value)

(defun eval-script (realm source)
  "Compile and run SOURCE against REALM; return the completion value."
  (let ((*current-realm* realm))
    (with-js-floats (run (compile-toplevel source) (realm-global-env realm) (realm-global realm)))))

(defun invoke (realm fn this args)
  "Call a JS function from the host (event handlers, timers)."
  (let ((*current-realm* realm)) (with-js-floats (js-call fn this args))))

(defun make-host-object (realm &key get set has delete own-keys call (proto :object))
  "A JS object whose internal methods are CL closures — the binding primitive.
   weft backs document/element/style with these and hangs reflow on the SET trap.
   Trap signatures: get (o key receiver), set (o key v receiver), has (o key),
   delete (o key), own-keys (o), call (this args)."
  (let ((*current-realm* realm) (internal '()))
    (when get (setf (getf internal :get) get))
    (when set (setf (getf internal :set) set))
    (when has (setf (getf internal :has) has))
    (when delete (setf (getf internal :delete) delete))
    (when own-keys (setf (getf internal :own-keys) own-keys))
    (make-object :proto (if (eq proto :object) (%obj-proto) proto) :internal internal :call call)))


;;; ===========================================================================
;;; The def-method / def-builtin convention (for the built-in library)
;;; ===========================================================================
;;; A spec built-in method has the property attributes verifyProperty expects:
;;;   { writable:true, enumerable:false, configurable:true },
;;; and its function object has non-writable/non-enumerable/configurable
;;; .name (the property key) and .length (the declared arg count).
;;;
;;; ONE obvious way to add a method, used everywhere below and in src/builtins/:
;;;
;;;   (def-method REALM PROTO "name" LEN (this args) BODY...)
;;;
;;; defines PROTO.name = a native function of LENGTH LEN whose body receives
;;; THIS (the receiver) and ARGS (a CL list). Use (arg N args) to read the Nth
;;; argument defaulting to undefined. def-value adds a non-enumerable data
;;; property; def-getter an accessor. Constructors: see err-ctor / make-ctor.

(defmacro def-method (realm target name len (this args) &body body)
  "Define TARGET.name as a non-enumerable, writable, configurable native method."
  `(put ,target ,name (native-function ,realm ,name (lambda (,this ,args)
                                                      (declare (ignorable ,this ,args))
                                                      ,@body) ,len)
        :enumerable nil :writable t :configurable t))

(defmacro def-value (target name value &key (writable t) (configurable t))
  `(put ,target ,name ,value :enumerable nil :writable ,writable :configurable ,configurable))

(defun def-getter (realm target name getter &key (configurable t))
  (put-accessor target name :get (native-function realm (concatenate 'string "get " name) getter 0)
                :enumerable nil :configurable configurable))

;;; ---- installer registry ---------------------------------------------------
;;; Each src/builtins/*.lisp file owns one method group and ends with
;;;   (register-builtin-installer 'install-<group>)
;;; where install-<group> is (realm) -> installs its methods (pulling protos via
;;; realm accessors). install-intrinsics runs them all AFTER the kernel. Workers
;;; edit only their own file + add it to the .asd — install-intrinsics is never
;;; touched, so files stay independent.
(defvar *builtin-installers* '())
(defun register-builtin-installer (sym) (pushnew sym *builtin-installers*))

(declaim (inline arg js-truthy*))
(defun arg (n args) (let ((c (nthcdr n args))) (if c (car c) *undefined*)))
(defun js-truthy* (v)
  "Truthiness for a value that may be a CL boolean (js-has result) or a JS value."
  (cond ((eq v t) t) ((null v) nil) (t (js-truthy v))))

;;; ===========================================================================
;;; install-intrinsics — the built-in library kernel
;;; ===========================================================================
(defun install-intrinsics (realm)
  (let ((op (realm-object-proto realm)) (fp (realm-function-proto realm))
        (ap (realm-array-proto realm)) (sp (realm-string-proto realm))
        (np (realm-number-proto realm)) (bp (realm-boolean-proto realm))
        (symp (realm-symbol-proto realm)))
    ;; ---- well-known symbols FIRST (protos/methods reference them) ----
    (install-symbols realm symp)
    ;; ---- Function.prototype ----
    (install-function-proto realm fp)
    ;; ---- Object.prototype + Object constructor ----
    (install-object realm op)
    ;; ---- Error hierarchy ----
    (install-errors realm)
    ;; ---- Array.prototype (kernel methods only; the rest live in src/builtins/) ----
    (install-array realm ap)
    ;; ---- wrapper constructors + their prototypes ----
    (install-boolean realm bp)
    (install-number realm np)
    (install-string realm sp)
    ;; ---- Math ----
    (install-math realm)
    ;; ---- globals: NaN/Infinity/undefined + parseInt/parseFloat/isNaN/isFinite ----
    (install-global-values realm)
    ;; ---- Reflect + Function constructor (needed by verifyProperty/isConstructor) ----
    (install-reflect realm)
    (install-function-ctor realm fp)
    ;; ---- console + eval ----
    (install-console-eval realm)
    ;; ---- built-in method groups (src/builtins/*) ----
    (dolist (sym (reverse *builtin-installers*)) (funcall sym realm))
    realm))

;;; ---------------------------------------------------------------------------
;;; Symbols
;;; ---------------------------------------------------------------------------
(defun install-symbols (realm symp)
  (let* ((sym-iterator (make-js-symbol "Symbol.iterator"))
         (sym-toprim   (make-js-symbol "Symbol.toPrimitive"))
         (sym-hasinst  (make-js-symbol "Symbol.hasInstance"))
         (sym-tostag   (make-js-symbol "Symbol.toStringTag"))
         (sym-asyncit  (make-js-symbol "Symbol.asyncIterator"))
         (ctor (native-function realm "Symbol"
                 (lambda (this args) (declare (ignore this))
                   (let ((d (arg 0 args)))
                     (make-js-symbol (if (js-undefined-p d) nil (to-string d))))))))
    (setf *symbol-iterator* sym-iterator *symbol-to-primitive* sym-toprim)
    ;; Symbol() is NOT a constructor
    (def-value ctor "prototype" symp :writable nil :configurable nil)
    (def-value symp "constructor" ctor)
    (def-value ctor "iterator" sym-iterator :writable nil :configurable nil)
    (def-value ctor "toPrimitive" sym-toprim :writable nil :configurable nil)
    (def-value ctor "hasInstance" sym-hasinst :writable nil :configurable nil)
    (def-value ctor "toStringTag" sym-tostag :writable nil :configurable nil)
    (def-value ctor "asyncIterator" sym-asyncit :writable nil :configurable nil)
    (def-method realm ctor "for" 1 (this args)
      (let ((key (to-string (arg 0 args))) (reg (realm-symbol-registry realm)))
        (or (gethash key reg) (setf (gethash key reg) (make-js-symbol key)))))
    (def-method realm ctor "keyFor" 1 (this args)
      (let ((s (arg 0 args)))
        (unless (js-symbol-p s) (js-throw (make-native-error "TypeError" "not a symbol")))
        (block found
          (maphash (lambda (k v) (when (eq v s) (return-from found k)))
                   (realm-symbol-registry realm))
          *undefined*)))
    ;; Symbol.prototype
    (def-method realm symp "toString" 0 (this args)
      (to-symbol-string (this-symbol this)))
    (def-method realm symp "valueOf" 0 (this args) (this-symbol this))
    (def-getter realm symp "description"
      (lambda (this args) (declare (ignore args))
        (let ((s (this-symbol this))) (or (js-symbol-desc s) *undefined*))))
    (put symp *symbol-to-primitive*
         (native-function realm "[Symbol.toPrimitive]"
           (lambda (this args) (declare (ignore args)) (this-symbol this)) 1)
         :enumerable nil :writable nil :configurable t)
    (define-global realm "Symbol" ctor)))

(defun this-symbol (this)
  (cond ((js-symbol-p this) this)
        ((and (js-object-p this) (js-symbol-p (js-object-primitive this))) (js-object-primitive this))
        (t (js-throw (make-native-error "TypeError" "Symbol.prototype method called on non-symbol")))))

;;; ---------------------------------------------------------------------------
;;; Function.prototype (call/apply/bind/toString)
;;; ---------------------------------------------------------------------------
(defun install-function-proto (realm fp)
  (def-method realm fp "call" 1 (this args)
    (js-call this (arg 0 args) (rest args)))
  (def-method realm fp "apply" 2 (this args)
    (let ((ta (arg 0 args)) (arr (arg 1 args)))
      (js-call this ta (array-like-to-list arr))))
  (def-method realm fp "bind" 1 (this args)
    (let ((target this) (bound-this (arg 0 args)) (bound-args (rest args)))
      (unless (js-callable-p target) (js-throw (make-native-error "TypeError" "Bind must be called on a function")))
      (let* ((tlen (to-number (js-get target "length")))
             (blen (max 0d0 (- (if (js-nan-p tlen) 0d0 tlen) (length bound-args))))
             (f (native-function realm
                  (concatenate 'string "bound " (let ((n (js-get target "name"))) (if (stringp n) n "")))
                  (lambda (ignored-this call-args) (declare (ignore ignored-this))
                    (js-call target bound-this (append bound-args call-args)))
                  0)))
        (put f "length" blen :enumerable nil :writable nil :configurable t)
        (when (js-object-construct target)
          (setf (js-object-construct f)
                (lambda (call-args nt) (declare (ignore nt))
                  (js-construct target (append bound-args call-args)))))
        f)))
  (def-method realm fp "toString" 0 (this args)
    (concatenate 'string "function " (let ((n (and (js-object-p this) (js-get this "name")))) (if (stringp n) n "")) "() { [native code] }")))

(defun array-like-to-list (arr)
  (if (js-null-or-undef arr) '()
      (let ((len (to-int-index (js-get arr "length"))) (lst '()))
        (dotimes (i len) (push (js-get arr (princ-to-string i)) lst))
        (nreverse lst))))

;;; ---------------------------------------------------------------------------
;;; Object.prototype + Object constructor
;;; ---------------------------------------------------------------------------
(defun install-object (realm op)
  (def-method realm op "hasOwnProperty" 1 (this args)
    (js-bool (and (js-get-own-property (to-object this) (to-property-key (arg 0 args))) t)))
  (def-method realm op "isPrototypeOf" 1 (this args)
    (let ((v (arg 0 args)))
      (if (js-object-p v)
          (let ((o (to-object this)))
            (js-bool (loop for p = (js-object-proto v) then (js-object-proto p)
                           while (js-object-p p) thereis (eq p o))))
          *false*)))
  (def-method realm op "propertyIsEnumerable" 1 (this args)
    (let ((d (js-get-own-property (to-object this) (to-property-key (arg 0 args)))))
      (js-bool (and d (prop-enumerable d)))))
  (def-method realm op "valueOf" 0 (this args) (to-object this))
  (def-method realm op "toLocaleString" 0 (this args) (js-call (js-get this "toString") this '()))
  (def-method realm op "toString" 0 (this args)
    (cond ((eq this *undefined*) "[object Undefined]")
          ((eq this *null*) "[object Null]")
          (t (let* ((o (to-object this))
                    (tag (let ((tg (and (boundp '*symbol-to-primitive*)
                                        (js-get o (symbol-tostringtag realm)))))
                           (if (stringp tg) tg (builtin-tag o)))))
               (concatenate 'string "[object " tag "]")))))
  ;; Object constructor
  (let ((octor (native-function realm "Object"
                 (lambda (this args) (declare (ignore this))
                   (let ((v (arg 0 args)))
                     (if (js-null-or-undef v) (make-object :proto op) (to-object v)))
                   ) 1)))
    (setf (js-object-construct octor)
          (lambda (args nt) (declare (ignore nt))
            (let ((v (arg 0 args))) (if (js-null-or-undef v) (make-object :proto op) (to-object v)))))
    (def-value octor "prototype" op :writable nil :configurable nil)
    (def-value op "constructor" octor)
    (install-object-statics realm octor op)
    (define-global realm "Object" octor)))

(defun symbol-tostringtag (realm)
  (let ((s (ignore-errors (js-get (js-get (realm-global realm) "Symbol") "toStringTag"))))
    (if (js-symbol-p s) s "Symbol.toStringTag")))

(defun builtin-tag (o)
  (let ((c (js-object-class o)))
    (cond ((string= c "Array") "Array")
          ((js-object-call o) "Function")
          ((member c '("Error") :test #'string=) "Error")
          ((string= c "Arguments") "Arguments")
          ((member c '("String" "Number" "Boolean" "Date" "RegExp") :test #'string=) c)
          (t "Object"))))

(defun to-property-descriptor (obj)
  "ToPropertyDescriptor: read a JS descriptor object into a PROP-fields plist
   (only present fields included)."
  (unless (js-object-p obj) (js-throw (make-native-error "TypeError" "Property description must be an object")))
  (let ((d '()))
    (when (js-truthy* (js-has obj "enumerable")) (setf (getf d :enumerable) (js-truthy (js-get obj "enumerable"))))
    (when (js-truthy* (js-has obj "configurable")) (setf (getf d :configurable) (js-truthy (js-get obj "configurable"))))
    (when (js-truthy* (js-has obj "value")) (setf (getf d :value) (js-get obj "value")))
    (when (js-truthy* (js-has obj "writable")) (setf (getf d :writable) (js-truthy (js-get obj "writable"))))
    (when (js-truthy* (js-has obj "get"))
      (let ((g (js-get obj "get")))
        (unless (or (js-undefined-p g) (js-callable-p g)) (js-throw (make-native-error "TypeError" "Getter must be a function")))
        (setf (getf d :accessor) t (getf d :get) g)))
    (when (js-truthy* (js-has obj "set"))
      (let ((s (js-get obj "set")))
        (unless (or (js-undefined-p s) (js-callable-p s)) (js-throw (make-native-error "TypeError" "Setter must be a function")))
        (setf (getf d :accessor) t (getf d :set) s)))
    (when (and (or (present-p d :get) (present-p d :set)) (or (present-p d :value) (present-p d :writable)))
      (js-throw (make-native-error "TypeError" "Invalid property descriptor")))
    d))

(defun from-property-descriptor (realm d)
  "Build a JS descriptor object from a PROP struct (or nil -> undefined)."
  (if (null d) *undefined*
      (let ((o (make-object :proto (realm-object-proto realm))))
        (if (prop-accessor d)
            (progn (put o "get" (or (prop-get d) *undefined*))
                   (put o "set" (or (prop-set d) *undefined*)))
            (progn (put o "value" (prop-value d))
                   (put o "writable" (js-bool (prop-writable d)))))
        (put o "enumerable" (js-bool (prop-enumerable d)))
        (put o "configurable" (js-bool (prop-configurable d)))
        o)))

(defun install-object-statics (realm octor op)
  (macrolet ((need-obj (v) `(unless (js-object-p ,v) (js-throw (make-native-error "TypeError" "not an object")))))
    (def-method realm octor "defineProperty" 3 (this args)
      (let ((o (arg 0 args)))
        (need-obj o)
        (let ((key (to-property-key (arg 1 args))) (desc (to-property-descriptor (arg 2 args))))
          (unless (js-define-own-property o key desc)
            (js-throw (make-native-error "TypeError" "Cannot define property")))
          o)))
    (def-method realm octor "defineProperties" 2 (this args)
      (let ((o (arg 0 args)) (props (arg 1 args)))
        (need-obj o) (let ((po (to-object props)))
          (dolist (k (js-own-keys po))
            (let ((d (js-get-own-property po k)))
              (when (and d (prop-enumerable d))
                (unless (js-define-own-property o k (to-property-descriptor (js-get po k)))
                  (js-throw (make-native-error "TypeError" "Cannot define property")))))))
        o))
    (def-method realm octor "getOwnPropertyDescriptor" 2 (this args)
      (from-property-descriptor realm (js-get-own-property (to-object (arg 0 args)) (to-property-key (arg 1 args)))))
    (def-method realm octor "getOwnPropertyNames" 1 (this args)
      (make-array-object (remove-if-not #'stringp (js-own-keys (to-object (arg 0 args))))))
    (def-method realm octor "getOwnPropertySymbols" 1 (this args)
      (make-array-object (remove-if-not #'js-symbol-p (js-own-keys (to-object (arg 0 args))))))
    (def-method realm octor "getPrototypeOf" 1 (this args)
      (let* ((o (to-object (arg 0 args))) (p (js-get-proto o)))
        (or (and (js-object-p p) p) *null*)))
    (def-method realm octor "setPrototypeOf" 2 (this args)
      (let ((o (arg 0 args)) (p (arg 1 args)))
        (require-object-coercible o)
        (unless (or (js-object-p p) (eq p *null*)) (js-throw (make-native-error "TypeError" "prototype must be object or null")))
        (when (js-object-p o)
          (unless (js-set-proto o p)
            (js-throw (make-native-error "TypeError" "Object.setPrototypeOf: could not set prototype"))))
        o))
    (def-method realm octor "create" 2 (this args)
      (let ((p (arg 0 args)) (props (arg 1 args)))
        (unless (or (js-object-p p) (eq p *null*)) (js-throw (make-native-error "TypeError" "Object prototype may only be an Object or null")))
        (let ((o (make-object :proto p)))
          (unless (js-undefined-p props)
            (let ((po (to-object props)))
              (dolist (k (js-own-keys po))
                (let ((d (js-get-own-property po k)))
                  (when (and d (prop-enumerable d))
                    (js-define-own-property o k (to-property-descriptor (js-get po k))))))))
          o)))
    (def-method realm octor "keys" 1 (this args)
      (make-array-object (enumerable-own-keys (to-object (arg 0 args)) :key)))
    (def-method realm octor "values" 1 (this args)
      (make-array-object (enumerable-own-keys (to-object (arg 0 args)) :value)))
    (def-method realm octor "entries" 1 (this args)
      (let ((o (to-object (arg 0 args))))
        (make-array-object (mapcar (lambda (pair) (make-array-object pair))
                                   (enumerable-own-keys o :entry)))))
    (def-method realm octor "assign" 2 (this args)
      (let ((target (to-object (arg 0 args))))
        (dolist (src (rest args))
          (unless (js-null-or-undef src)
            (let ((so (to-object src)))
              (dolist (k (js-own-keys so))
                (let ((d (js-get-own-property so k)))
                  (when (and d (prop-enumerable d)) (js-set target k (js-get so k))))))))
        target))
    (def-method realm octor "freeze" 1 (this args)
      (let ((o (arg 0 args)))
        (when (js-object-p o)
          (setf (js-object-extensible o) nil)
          (maphash (lambda (k p) (declare (ignore k))
                     (setf (prop-configurable p) nil)
                     (unless (prop-accessor p) (setf (prop-writable p) nil)))
                   (js-object-props o)))
        o))
    (def-method realm octor "seal" 1 (this args)
      (let ((o (arg 0 args)))
        (when (js-object-p o)
          (setf (js-object-extensible o) nil)
          (maphash (lambda (k p) (declare (ignore k)) (setf (prop-configurable p) nil)) (js-object-props o)))
        o))
    (def-method realm octor "preventExtensions" 1 (this args)
      (let ((o (arg 0 args)))
        (when (js-object-p o)
          (unless (js-prevent-extensions o)
            (js-throw (make-native-error "TypeError" "Object.preventExtensions: could not prevent extensions"))))
        o))
    (def-method realm octor "isFrozen" 1 (this args)
      (let ((o (arg 0 args)))
        (if (js-object-p o)
            (js-bool (and (not (js-extensible-p o))
                          (loop for p being the hash-values of (js-object-props o)
                                always (and (not (prop-configurable p))
                                            (or (prop-accessor p) (not (prop-writable p)))))))
            *true*)))
    (def-method realm octor "isSealed" 1 (this args)
      (let ((o (arg 0 args)))
        (if (js-object-p o)
            (js-bool (and (not (js-extensible-p o))
                          (loop for p being the hash-values of (js-object-props o)
                                always (not (prop-configurable p)))))
            *true*)))
    (def-method realm octor "isExtensible" 1 (this args)
      (let ((o (arg 0 args))) (js-bool (and (js-object-p o) (js-extensible-p o)))))
    (def-method realm octor "is" 2 (this args)
      (js-bool (same-value (arg 0 args) (arg 1 args))))))

(defun enumerable-own-keys (o kind)
  "List of enumerable own STRING keys (:key), their values (:value), or (k v) pairs (:entry)."
  (loop for k in (js-own-keys o)
        for d = (and (stringp k) (js-get-own-property o k))
        when (and d (prop-enumerable d))
          collect (ecase kind (:key k) (:value (js-get o k)) (:entry (list k (js-get o k))))))

;;; ---------------------------------------------------------------------------
;;; Errors
;;; ---------------------------------------------------------------------------
(defun install-errors (realm)
  (let* ((op (realm-object-proto realm))
         (base-proto (make-object :proto op))
         (base-ctor (native-function realm "Error"
                      (lambda (this args)
                        (let ((o (if (js-object-p this) this (make-object :proto base-proto))))
                          (unless (js-undefined-p (arg 0 args))
                            (put o "message" (to-string (arg 0 args)) :enumerable nil))
                          o)) 1)))
    (def-value base-proto "name" "Error")
    (def-value base-proto "message" "")
    (def-value base-proto "constructor" base-ctor)
    (def-method realm base-proto "toString" 0 (this args)
      (let* ((name (let ((n (js-get this "name"))) (if (js-undefined-p n) "Error" (to-string n))))
             (msg (let ((m (js-get this "message"))) (if (js-undefined-p m) "" (to-string m)))))
        (cond ((string= name "") msg) ((string= msg "") name)
              (t (concatenate 'string name ": " msg)))))
    (def-value base-ctor "prototype" base-proto :writable nil :configurable nil)
    (setf (js-object-construct base-ctor)
          (lambda (args nt) (declare (ignore nt))
            (let ((o (make-object :proto base-proto :class "Error"))) (funcall (js-object-call base-ctor) o args) o)))
    (define-global realm "Error" base-ctor)
    (dolist (name '("TypeError" "RangeError" "SyntaxError" "ReferenceError" "EvalError" "URIError"))
      (let* ((proto (make-object :proto base-proto))
             (ctor (native-function realm name
                     (lambda (this args)
                       (let ((o (if (js-object-p this) this (make-object :proto proto))))
                         (unless (js-undefined-p (arg 0 args))
                           (put o "message" (to-string (arg 0 args)) :enumerable nil))
                         o)) 1)))
        (def-value proto "name" name)
        (def-value proto "message" "")
        (def-value proto "constructor" ctor)
        (def-value ctor "prototype" proto :writable nil :configurable nil)
        (setf (js-object-proto ctor) base-ctor)   ; TypeError.__proto__ === Error
        (setf (js-object-construct ctor)
              (let ((proto proto) (ctor ctor))
                (lambda (args nt) (declare (ignore nt))
                  (let ((o (make-object :proto proto :class "Error"))) (funcall (js-object-call ctor) o args) o))))
        (define-global realm name ctor)))))

;;; ---------------------------------------------------------------------------
;;; Array.prototype (kernel; src/builtins/ adds the rest)
;;; ---------------------------------------------------------------------------
(defun install-array (realm ap)
  ;; Array.prototype is itself an Array exotic object with an own "length"
  ;; (writable, non-enumerable, non-configurable), initially 0.
  (put ap "length" 0d0 :enumerable nil :writable t :configurable nil)
  (let ((actor (native-function realm "Array"
                 (lambda (this args) (declare (ignore this)) (array-construct realm args)) 1)))
    (setf (js-object-construct actor) (lambda (args nt) (array-construct realm args nt)))
    (def-value actor "prototype" ap :writable nil :configurable nil)
    (def-value ap "constructor" actor)
    (def-method realm actor "isArray" 1 (this args)
      (js-bool (and (js-object-p (arg 0 args)) (string= (js-object-class (arg 0 args)) "Array"))))
    (def-method realm actor "of" 0 (this args) (make-array-object args))
    (def-method realm actor "from" 1 (this args)
      (let ((src (arg 0 args)) (mapf (arg 1 args)) (out '()))
        (if (and (js-object-p src) *symbol-iterator* (js-callable-p (js-get src *symbol-iterator*)))
            (let ((it (get-iterator src)) (i 0))
              (loop (let ((r (iterator-step it)))
                      (when (js-truthy (js-get r "done")) (return))
                      (let ((v (js-get r "value")))
                        (push (if (js-callable-p mapf) (js-call mapf *undefined* (list v (float i 1d0))) v) out) (incf i)))))
            (when (js-object-p src)
              (let ((len (to-int-index (js-get src "length"))))
                (dotimes (i len) (let ((v (js-get src (princ-to-string i))))
                                   (push (if (js-callable-p mapf) (js-call mapf *undefined* (list v (float i 1d0))) v) out))))))
        (make-array-object (nreverse out))))
    (define-global realm "Array" actor))
  (flet ((len (this) (to-int-index (js-get this "length"))))
    (def-method realm ap "push" 1 (this args)
      (let ((l (len this)))
        (dolist (a args) (js-set this (princ-to-string l) a) (incf l))
        (js-set this "length" (float l 1d0)) (float l 1d0)))
    (def-method realm ap "pop" 0 (this args)
      (let ((l (len this)))
        (if (zerop l) (progn (js-set this "length" 0d0) *undefined*)
            (let ((v (js-get this (princ-to-string (1- l)))))
              (js-delete this (princ-to-string (1- l))) (js-set this "length" (float (1- l) 1d0)) v))))
    (def-method realm ap "join" 1 (this args)
      (let ((sep (if (js-undefined-p (arg 0 args)) "," (to-string (arg 0 args)))) (l (len this)))
        (with-output-to-string (s)
          (dotimes (i l) (when (plusp i) (write-string sep s))
            (let ((v (js-get this (princ-to-string i))))
              (unless (js-null-or-undef v) (write-string (to-string v) s)))))))
    (def-method realm ap "indexOf" 1 (this args)
      (let ((target (arg 0 args)) (l (len this)))
        (or (loop for i from 0 below l when (js-strict-equal (js-get this (princ-to-string i)) target) return (float i 1d0))
            -1d0)))
    (def-method realm ap "slice" 2 (this args)
      (let* ((l (len this)) (start (clamp-index (arg 0 args) l 0)) (end (clamp-index (arg 1 args) l l)) (out '()))
        (loop for i from start below end do (push (js-get this (princ-to-string i)) out))
        (make-array-object (nreverse out))))
    (def-method realm ap "forEach" 1 (this args)
      (let ((fn (arg 0 args)) (ta (arg 1 args)) (l (len this)))
        (dotimes (i l) (when (js-truthy* (js-has this (princ-to-string i)))
                         (js-call fn ta (list (js-get this (princ-to-string i)) (float i 1d0) this))))
        *undefined*))
    (def-method realm ap "map" 1 (this args)
      (let ((fn (arg 0 args)) (ta (arg 1 args)) (l (len this)) (out '()))
        (dotimes (i l) (push (js-call fn ta (list (js-get this (princ-to-string i)) (float i 1d0) this)) out))
        (make-array-object (nreverse out))))
    (def-method realm ap "toString" 0 (this args)
      (let ((j (js-get this "join"))) (if (js-callable-p j) (js-call j this '()) "[object Array]")))
    (when *symbol-iterator*
      (put ap *symbol-iterator*
           (native-function realm "[Symbol.iterator]"
             (lambda (this args) (declare (ignore args)) (make-array-iterator realm this)) 0)
           :enumerable nil :writable t :configurable t)
      (def-method realm ap "values" 0 (this args) (make-array-iterator realm this)))))

(defun array-construct (realm args &optional new-target)
  ;; OrdinaryCreateFromConstructor(newTarget, %Array.prototype%): a subclass'
  ;; newTarget.prototype becomes the [[Prototype]] so `Reflect.construct(Array,[],Der)`
  ;; is instanceof Der.
  (let ((proto (let ((pp (and (js-object-p new-target) (js-get new-target "prototype"))))
                 (if (js-object-p pp) pp (realm-array-proto realm)))))
    (if (and (= (length args) 1) (floatp (first args)))
        (let ((n (first args)))
          (unless (and (= n (with-js-floats (ftruncate n))) (<= 0 n #xFFFFFFFF))
            (js-throw (make-native-error "RangeError" "Invalid array length")))
          (let ((o (make-object :proto proto :class "Array")))
            (put o "length" n :enumerable nil :writable t :configurable nil) o))
        (let ((o (make-array-object args)))
          (setf (js-object-proto o) proto) o))))

(defun clamp-index (v len default)
  (if (js-undefined-p v) default
      (let ((i (to-int-index v))) (cond ((< i 0) (max 0 (+ len i))) ((> i len) len) (t i)))))

(defun ensure-iterator-proto (realm)
  "%IteratorPrototype%: the shared prototype whose only method is
   [Symbol.iterator]() { return this; }. Memoized in the realm intrinsics."
  (or (getf (realm-intrinsics realm) :iterator-proto)
      (let ((ip (make-object :proto (realm-object-proto realm))))
        (when *symbol-iterator*
          (put ip *symbol-iterator*
               (native-function realm "[Symbol.iterator]" (lambda (this args) (declare (ignore args)) this) 0)
               :enumerable nil))
        (setf (getf (realm-intrinsics realm) :iterator-proto) ip)
        ip)))

(defun ensure-array-iterator-proto (realm)
  "%ArrayIteratorPrototype%: shared prototype carrying `next` (and inheriting
   [Symbol.iterator] from %IteratorPrototype%). Instances hold only their cursor
   state, so `next` is NOT an own property of an array-iterator instance."
  (or (getf (realm-intrinsics realm) :array-iterator-proto)
      (let ((aip (make-object :proto (ensure-iterator-proto realm) :class "Array Iterator")))
        (def-method realm aip "next" 0 (this args) (declare (ignore args)) (array-iterator-next this))
        (setf (getf (realm-intrinsics realm) :array-iterator-proto) aip)
        aip)))

(defun array-iterator-next (this)
  "The %ArrayIteratorPrototype%.next step, reading the cursor state stored in the
   iterator instance's internal slots."
  (let* ((state (and (js-object-p this) (js-object-internal this)))
         (arr (getf state :array-iterator-target))
         (res (make-object :proto (%obj-proto))))
    (unless (and arr (getf state :array-iterator-p))
      (js-throw (make-native-error "TypeError" "next called on a non-ArrayIterator")))
    (let ((i (getf state :array-iterator-index))
          (len (to-int-index (js-get arr "length"))))
      (if (< i len)
          (progn (put res "value" (js-get arr (princ-to-string i))) (put res "done" *false*)
                 (setf (getf (js-object-internal this) :array-iterator-index) (1+ i)))
          (progn (put res "value" *undefined*) (put res "done" *true*)))
      res)))

(defun make-array-iterator (realm arr)
  (let ((it (make-object :proto (ensure-array-iterator-proto realm) :class "Array Iterator")))
    (setf (js-object-internal it)
          (list :array-iterator-p t :array-iterator-target arr :array-iterator-index 0))
    it))

;;; ---------------------------------------------------------------------------
;;; Boolean
;;; ---------------------------------------------------------------------------
(defun install-boolean (realm bp)
  (let ((ctor (native-function realm "Boolean"
                (lambda (this args) (declare (ignore this)) (to-boolean (arg 0 args))) 1)))
    (setf (js-object-construct ctor)
          (lambda (args nt) (declare (ignore nt))
            (let ((o (make-object :proto bp :class "Boolean"))) (setf (js-object-primitive o) (to-boolean (arg 0 args))) o)))
    (def-value ctor "prototype" bp :writable nil :configurable nil)
    (def-value bp "constructor" ctor)
    (def-method realm bp "valueOf" 0 (this args) (this-boolean this))
    (def-method realm bp "toString" 0 (this args) (if (eq (this-boolean this) *true*) "true" "false"))
    (define-global realm "Boolean" ctor)))
(defun this-boolean (this)
  (cond ((or (eq this *true*) (eq this *false*)) this)
        ((and (js-object-p this) (member (js-object-primitive this) (list *true* *false*))) (js-object-primitive this))
        (t (js-throw (make-native-error "TypeError" "not a Boolean")))))

;;; ---------------------------------------------------------------------------
;;; Number
;;; ---------------------------------------------------------------------------
(defun install-number (realm np)
  (let ((ctor (native-function realm "Number"
                (lambda (this args) (declare (ignore this))
                  (if args (number-arg-value (arg 0 args)) 0d0)) 1)))
    (setf (js-object-construct ctor)
          (lambda (args nt) (declare (ignore nt))
            (let ((o (make-object :proto np :class "Number")))
              (setf (js-object-primitive o) (if args (number-arg-value (arg 0 args)) 0d0)) o)))
    (def-value ctor "prototype" np :writable nil :configurable nil)
    (def-value np "constructor" ctor)
    (def-value ctor "MAX_SAFE_INTEGER" 9007199254740991d0 :writable nil :configurable nil)
    (def-value ctor "MIN_SAFE_INTEGER" -9007199254740991d0 :writable nil :configurable nil)
    (def-value ctor "MAX_VALUE" most-positive-double-float :writable nil :configurable nil)
    (def-value ctor "MIN_VALUE" least-positive-double-float :writable nil :configurable nil)
    (def-value ctor "EPSILON" (expt 2d0 -52) :writable nil :configurable nil)
    (def-value ctor "POSITIVE_INFINITY" *inf* :writable nil :configurable nil)
    (def-value ctor "NEGATIVE_INFINITY" *-inf* :writable nil :configurable nil)
    (def-value ctor "NaN" *nan* :writable nil :configurable nil)
    (def-method realm ctor "isNaN" 1 (this args)
      (let ((v (arg 0 args))) (js-bool (and (floatp v) (js-nan-p v)))))
    (def-method realm ctor "isFinite" 1 (this args)
      (let ((v (arg 0 args))) (js-bool (and (floatp v) (not (js-nan-p v)) (/= v *inf*) (/= v *-inf*)))))
    (def-method realm ctor "isInteger" 1 (this args)
      (let ((v (arg 0 args))) (js-bool (and (floatp v) (not (js-nan-p v)) (/= v *inf*) (/= v *-inf*)
                                            (= v (with-js-floats (ftruncate v)))))))
    (def-method realm ctor "isSafeInteger" 1 (this args)
      (let ((v (arg 0 args))) (js-bool (and (floatp v) (not (js-nan-p v)) (/= v *inf*) (/= v *-inf*)
                                            (= v (with-js-floats (ftruncate v))) (<= (abs v) 9007199254740991d0)))))
    (def-method realm ctor "parseFloat" 1 (this args) (js-parse-float (to-string (arg 0 args))))
    (def-method realm ctor "parseInt" 2 (this args) (js-parse-int (to-string (arg 0 args)) (arg 1 args)))
    (def-method realm np "valueOf" 0 (this args) (this-number this))
    (def-method realm np "toString" 1 (this args)
      (let ((n (this-number this)) (radix (arg 0 args)))
        (if (or (js-undefined-p radix) (= (to-int-index radix) 10)) (number-to-string n)
            (number-to-radix-string n (to-int-index radix)))))
    (def-method realm np "toFixed" 1 (this args)
      (let ((n (this-number this)) (digits (to-int-index (arg 0 args))))
        (if (js-nan-p n) "NaN"
            (with-js-floats (format nil "~,vf" digits n)))))
    (define-global realm "Number" ctor)))
(defun number-arg-value (v)
  "Number(v): ToNumeric, then a BigInt is converted to its Number value (unlike
   implicit ToNumber, which throws). Objects coerce via ToPrimitive(number)."
  (let ((p (if (js-object-p v) (to-primitive v :number) v)))
    (if (js-bigint-p p) (float p 1d0) (to-number p))))

(defun this-number (this)
  (cond ((floatp this) this)
        ((and (js-object-p this) (floatp (js-object-primitive this))) (js-object-primitive this))
        (t (js-throw (make-native-error "TypeError" "not a Number")))))

(defun number-to-radix-string (n radix)
  (cond ((js-nan-p n) "NaN") ((= n *inf*) "Infinity") ((= n *-inf*) "-Infinity")
        ((minusp n) (concatenate 'string "-" (number-to-radix-string (- n) radix)))
        ((= n (with-js-floats (ftruncate n)))
         (string-downcase (write-to-string (truncate n) :base radix)))
        (t ;; fractional part: emit up to ~20 digits
         (multiple-value-bind (ipart frac) (truncate n)
           (let ((s (string-downcase (write-to-string ipart :base radix))))
             (with-output-to-string (out)
               (write-string s out) (write-char #\. out)
               (let ((f frac))
                 (dotimes (i 20)
                   (setf f (* f radix))
                   (multiple-value-bind (d r) (truncate f)
                     (write-char (char "0123456789abcdefghijklmnopqrstuvwxyz" d) out)
                     (setf f r) (when (zerop f) (return)))))))))))

;;; ---------------------------------------------------------------------------
;;; String
;;; ---------------------------------------------------------------------------
(defun install-string (realm sp)
  (let ((ctor (native-function realm "String"
                (lambda (this args) (declare (ignore this))
                  (if args (let ((v (arg 0 args))) (if (js-symbol-p v) (to-symbol-string v) (to-string v))) "")) 1)))
    (setf (js-object-construct ctor)
          (lambda (args nt) (declare (ignore nt))
            (let ((o (make-object :proto sp :class "String")) (s (if args (to-string (arg 0 args)) "")))
              (setf (js-object-primitive o) s)
              ;; String exotic: each character index is an own enumerable,
              ;; non-writable, non-configurable data property.
              (dotimes (i (length s))
                (put o (princ-to-string i) (string (char s i))
                     :enumerable t :writable nil :configurable nil))
              (put o "length" (float (length s) 1d0) :enumerable nil :writable nil :configurable nil)
              o)))
    (def-value ctor "prototype" sp :writable nil :configurable nil)
    (def-value sp "constructor" ctor)
    (def-method realm ctor "fromCharCode" 1 (this args)
      (map 'string (lambda (a) (code-char (logand (to-int-index a) #xFFFF))) args))
    (def-value sp "length" 0d0 :writable nil :configurable nil)
    ;; toString/valueOf must NOT ToString(this) first — that would re-enter this
    ;; very method on a String box and recurse. They read the primitive directly.
    (def-method realm sp "toString" 0 (this args) (this-string this))
    (def-method realm sp "valueOf" 0 (this args) (this-string this))
    (macrolet ((sm (name len (s args) &body body)
                 `(def-method realm sp ,name ,len (this ,args)
                    (require-object-coercible this)
                    (let ((,s (to-string this))) (declare (ignorable ,s)) ,@body))))
      (sm "charAt" 1 (s args) (let ((i (to-int-index (arg 0 args)))) (if (< -1 i (length s)) (string (char s i)) "")))
      (sm "charCodeAt" 1 (s args) (let ((i (to-int-index (arg 0 args)))) (if (< -1 i (length s)) (float (char-code (char s i)) 1d0) *nan*)))
      (sm "codePointAt" 1 (s args) (let ((i (to-int-index (arg 0 args)))) (if (< -1 i (length s)) (float (char-code (char s i)) 1d0) *undefined*)))
      (sm "at" 1 (s args) (let ((i (to-int-index (arg 0 args)))) (when (< i 0) (incf i (length s))) (if (< -1 i (length s)) (string (char s i)) *undefined*)))
      (sm "indexOf" 1 (s args) (let ((sub (to-string (arg 0 args))) (from (max 0 (to-int-index (arg 1 args)))))
                                 (let ((p (search sub s :start2 (min from (length s))))) (if p (float p 1d0) -1d0))))
      (sm "lastIndexOf" 1 (s args) (let ((sub (to-string (arg 0 args))))
                                     (let ((p (search sub s :from-end t))) (if p (float p 1d0) -1d0))))
      (sm "includes" 1 (s args) (js-bool (search (to-string (arg 0 args)) s)))
      (sm "startsWith" 1 (s args) (let ((sub (to-string (arg 0 args))) (pos (max 0 (to-int-index (arg 1 args)))))
                                    (js-bool (and (<= (+ pos (length sub)) (length s)) (string= sub s :start2 pos :end2 (+ pos (length sub)))))))
      (sm "endsWith" 1 (s args) (let* ((sub (to-string (arg 0 args))) (end (if (js-undefined-p (arg 1 args)) (length s) (min (length s) (to-int-index (arg 1 args))))))
                                  (js-bool (and (>= end (length sub)) (string= sub s :start2 (- end (length sub)) :end2 end)))))
      (sm "slice" 2 (s args) (let* ((l (length s)) (start (clamp-index (arg 0 args) l 0)) (end (clamp-index (arg 1 args) l l)))
                               (if (< start end) (subseq s start end) "")))
      (sm "substring" 2 (s args) (let* ((l (length s))
                                        (a (min l (max 0 (if (js-undefined-p (arg 0 args)) 0 (to-int-index (arg 0 args))))))
                                        (b (min l (max 0 (if (js-undefined-p (arg 1 args)) l (to-int-index (arg 1 args)))))))
                                   (subseq s (min a b) (max a b))))
      (sm "substr" 2 (s args) (let* ((l (length s)) (start (let ((i (to-int-index (arg 0 args)))) (if (< i 0) (max 0 (+ l i)) (min i l))))
                                     (len (if (js-undefined-p (arg 1 args)) (- l start) (max 0 (min (to-int-index (arg 1 args)) (- l start))))))
                                (subseq s start (+ start len))))
      (sm "toUpperCase" 0 (s args) (declare (ignore args)) (string-upcase s))
      (sm "toLowerCase" 0 (s args) (declare (ignore args)) (string-downcase s))
      (sm "toLocaleUpperCase" 0 (s args) (declare (ignore args)) (string-upcase s))
      (sm "toLocaleLowerCase" 0 (s args) (declare (ignore args)) (string-downcase s))
      (sm "trim" 0 (s args) (declare (ignore args)) (string-trim +js-ws+ s))
      (sm "trimStart" 0 (s args) (declare (ignore args)) (string-left-trim +js-ws+ s))
      (sm "trimEnd" 0 (s args) (declare (ignore args)) (string-right-trim +js-ws+ s))
      (sm "concat" 1 (s args) (apply #'concatenate 'string s (mapcar #'to-string args)))
      (sm "repeat" 1 (s args) (let ((n (to-int-index (arg 0 args))))
                                (when (< n 0) (js-throw (make-native-error "RangeError" "Invalid count value")))
                                (with-output-to-string (o) (dotimes (i n) (write-string s o)))))
      (sm "padStart" 1 (s args) (string-pad s (arg 0 args) (arg 1 args) t))
      (sm "padEnd" 1 (s args) (string-pad s (arg 0 args) (arg 1 args) nil))
      (sm "split" 2 (s args) (string-split realm s (arg 0 args) (arg 1 args))))
    (when *symbol-iterator*
      (put sp *symbol-iterator*
           (native-function realm "[Symbol.iterator]"
             (lambda (this args) (declare (ignore args)) (make-string-iterator realm (to-string (require-object-coercible this)))) 0)
           :enumerable nil :writable t :configurable t))
    (define-global realm "String" ctor)))
(defun this-string (this)
  (cond ((stringp this) this)
        ((and (js-object-p this) (stringp (js-object-primitive this))) (js-object-primitive this))
        (t (to-string (require-object-coercible this)))))

(defun string-pad (s max-len pad-str start-p)
  (let* ((target (to-int-index max-len))
         (pad (if (js-undefined-p pad-str) " " (to-string pad-str))))
    (if (or (<= target (length s)) (zerop (length pad))) s
        (let* ((need (- target (length s)))
               (fill (with-output-to-string (o)
                       (dotimes (i need) (write-char (char pad (mod i (length pad))) o)))))
          (if start-p (concatenate 'string fill s) (concatenate 'string s fill))))))

(defun string-split (realm s sep limit)
  (let ((lim (if (js-undefined-p limit) most-positive-fixnum (to-int-index limit))))
    (cond ((zerop lim) (make-array-object '()))
          ((js-undefined-p sep) (make-array-object (list s)))
          (t (let ((seps (to-string sep)) (out '()))
               (if (string= seps "")
                   (loop for c across s while (< (length out) lim) do (push (string c) out))
                   (let ((start 0))
                     (loop (let ((p (search seps s :start2 start)))
                             (cond ((or (null p) (>= (length out) lim))
                                    (when (< (length out) lim) (push (subseq s start) out)) (return))
                                   (t (push (subseq s start p) out) (setf start (+ p (length seps)))))))))
               (make-array-object (nreverse out)))))))

(defun ensure-string-iterator-proto (realm)
  "%StringIteratorPrototype%: shared prototype carrying `next`, inheriting
   [Symbol.iterator] from %IteratorPrototype%."
  (or (getf (realm-intrinsics realm) :string-iterator-proto)
      (let ((sip (make-object :proto (ensure-iterator-proto realm) :class "String Iterator")))
        (def-method realm sip "next" 0 (this args) (declare (ignore args)) (string-iterator-next this))
        (setf (getf (realm-intrinsics realm) :string-iterator-proto) sip)
        sip)))

(defun string-iterator-next (this)
  ;; iterate by CODE POINT — a surrogate pair yields a single 2-unit substring;
  ;; a lone surrogate yields its 1-unit substring.
  (let* ((state (and (js-object-p this) (js-object-internal this)))
         (s (getf state :string-iterator-target))
         (res (make-object :proto (%obj-proto))))
    (unless (getf state :string-iterator-p)
      (js-throw (make-native-error "TypeError" "next called on a non-StringIterator")))
    (let ((i (getf state :string-iterator-index)))
      (if (< i (length s))
          (multiple-value-bind (cp units) (code-point-at s i)
            (declare (ignore cp))
            (put res "value" (subseq s i (+ i units))) (put res "done" *false*)
            (setf (getf (js-object-internal this) :string-iterator-index) (+ i units)))
          (progn (put res "value" *undefined*) (put res "done" *true*)))
      res)))

(defun make-string-iterator (realm s)
  (let ((it (make-object :proto (ensure-string-iterator-proto realm) :class "String Iterator")))
    (setf (js-object-internal it)
          (list :string-iterator-p t :string-iterator-target s :string-iterator-index 0))
    it))

;;; ---------------------------------------------------------------------------
;;; Math
;;; ---------------------------------------------------------------------------
(defun install-math (realm)
  (let ((math (make-object :proto (realm-object-proto realm))))
    (def-value math "PI" pi :writable nil :configurable nil)
    (def-value math "E" (exp 1d0) :writable nil :configurable nil)
    (def-value math "LN2" (log 2d0) :writable nil :configurable nil)
    (def-value math "LN10" (log 10d0) :writable nil :configurable nil)
    (def-value math "LOG2E" (/ 1d0 (log 2d0)) :writable nil :configurable nil)
    (def-value math "LOG10E" (/ 1d0 (log 10d0)) :writable nil :configurable nil)
    (def-value math "SQRT2" (sqrt 2d0) :writable nil :configurable nil)
    (def-value math "SQRT1_2" (sqrt 0.5d0) :writable nil :configurable nil)
    (macrolet ((m1 (name fn)
                 `(def-method realm math ,name 1 (this args)
                    (with-js-floats (let ((x (to-number (arg 0 args))))
                                      (if (js-nan-p x) *nan* (float (,fn x) 1d0)))))))
      (m1 "abs" abs) (m1 "sqrt" %sqrt) (m1 "sin" sin) (m1 "cos" cos) (m1 "tan" tan)
      (m1 "asin" asin) (m1 "acos" acos) (m1 "atan" atan)
      (m1 "exp" exp) (m1 "sign" %sign)
      (m1 "trunc" ftruncate) (m1 "cbrt" %cbrt))
    (def-method realm math "floor" 1 (this args) (with-js-floats (let ((x (to-number (arg 0 args)))) (if (or (js-nan-p x) (= (abs x) *inf*)) x (float (ffloor x) 1d0)))))
    (def-method realm math "ceil" 1 (this args) (with-js-floats (let ((x (to-number (arg 0 args)))) (if (or (js-nan-p x) (= (abs x) *inf*)) x (float (fceiling x) 1d0)))))
    (def-method realm math "round" 1 (this args) (with-js-floats (let ((x (to-number (arg 0 args)))) (if (or (js-nan-p x) (= (abs x) *inf*)) x (float (ffloor (+ x 0.5d0)) 1d0)))))
    (def-method realm math "log" 1 (this args) (with-js-floats (let ((x (to-number (arg 0 args)))) (cond ((js-nan-p x) *nan*) ((minusp x) *nan*) ((zerop x) *-inf*) (t (float (log x) 1d0))))))
    (def-method realm math "pow" 2 (this args) (with-js-floats (js-pow (to-number (arg 0 args)) (to-number (arg 1 args)))))
    (def-method realm math "atan2" 2 (this args) (with-js-floats (float (atan (to-number (arg 0 args)) (to-number (arg 1 args))) 1d0)))
    (def-method realm math "hypot" 2 (this args) (with-js-floats (float (sqrt (reduce #'+ (mapcar (lambda (a) (let ((x (to-number a))) (* x x))) args) :initial-value 0d0)) 1d0)))
    (def-method realm math "max" 2 (this args)
      (with-js-floats
        (block m (let ((r *-inf*)) (dolist (a args) (let ((x (to-number a))) (when (js-nan-p x) (return-from m *nan*)) (when (or (> x r) (and (zerop x) (zerop r) (js-negative-zero-p r))) (setf r x)))) r))))
    (def-method realm math "min" 2 (this args)
      (with-js-floats
        (block m (let ((r *inf*)) (dolist (a args) (let ((x (to-number a))) (when (js-nan-p x) (return-from m *nan*)) (when (or (< x r) (and (zerop x) (zerop r) (js-negative-zero-p x))) (setf r x)))) r))))
    (def-method realm math "random" 0 (this args) (random 1d0))
    (define-global realm "Math" math)))
(defun %sqrt (x) (if (minusp x) *nan* (sqrt x)))
(defun %cbrt (x) (if (minusp x) (- (expt (- x) 1/3)) (expt x 1/3)))
(defun %sign (x) (cond ((zerop x) x) ((plusp x) 1d0) (t -1d0)))
(defun js-pow (base exp)
  (cond ((js-nan-p exp) *nan*)
        ((zerop exp) 1d0)
        ((js-nan-p base) *nan*)
        (t (handler-case (float (expt base exp) 1d0) (error () *nan*)))))

;;; ---------------------------------------------------------------------------
;;; Global values + functions
;;; ---------------------------------------------------------------------------
(defun install-global-values (realm)
  (put (realm-global realm) "NaN" *nan* :enumerable nil :writable nil :configurable nil)
  (put (realm-global realm) "Infinity" *inf* :enumerable nil :writable nil :configurable nil)
  (put (realm-global realm) "undefined" *undefined* :enumerable nil :writable nil :configurable nil)
  (env-declare (realm-global-env realm) "NaN" *nan*)
  (env-declare (realm-global-env realm) "Infinity" *inf*)
  (env-declare (realm-global-env realm) "undefined" *undefined*)
  (define-global realm "isNaN"
    (native-function realm "isNaN" (lambda (this args) (declare (ignore this)) (js-bool (js-nan-p (to-number (arg 0 args))))) 1))
  (define-global realm "isFinite"
    (native-function realm "isFinite" (lambda (this args) (declare (ignore this))
                                        (let ((n (to-number (arg 0 args)))) (js-bool (and (not (js-nan-p n)) (/= n *inf*) (/= n *-inf*))))) 1))
  (define-global realm "parseInt"
    (native-function realm "parseInt" (lambda (this args) (declare (ignore this)) (js-parse-int (to-string (arg 0 args)) (arg 1 args))) 2))
  (define-global realm "parseFloat"
    (native-function realm "parseFloat" (lambda (this args) (declare (ignore this)) (js-parse-float (to-string (arg 0 args)))) 1)))

(defun js-parse-int (s radix)
  (let* ((str (string-left-trim +js-ws+ s)) (i 0) (n (length str)) (sign 1) (r (to-int-index radix)))
    (when (and (< i n) (member (char str i) '(#\+ #\-)))
      (when (char= (char str i) #\-) (setf sign -1)) (incf i))
    (cond ((zerop r)
           (if (and (< (+ i 1) n) (char= (char str i) #\0) (member (char str (1+ i)) '(#\x #\X)))
               (progn (setf r 16) (incf i 2)) (setf r 10)))
          ((= r 16) (when (and (< (+ i 1) n) (char= (char str i) #\0) (member (char str (1+ i)) '(#\x #\X))) (incf i 2)))
          ((or (< r 2) (> r 36)) (return-from js-parse-int *nan*)))
    (let ((start i) (val 0))
      (loop while (< i n) do (let ((d (digit-char-p (char str i) r))) (if d (progn (setf val (+ (* val r) d)) (incf i)) (return))))
      (if (= i start) *nan* (float (* sign val) 1d0)))))

(defun js-parse-float (s)
  (let* ((str (string-left-trim +js-ws+ s)))
    (cond ((and (>= (length str) 8) (string= (subseq str 0 8) "Infinity")) *inf*)
          ((and (>= (length str) 9) (string= (subseq str 0 9) "+Infinity")) *inf*)
          ((and (>= (length str) 9) (string= (subseq str 0 9) "-Infinity")) *-inf*)
          (t ;; longest valid decimal prefix
           (let ((end (float-prefix-end str)))
             (if (zerop end) *nan* (or (parse-js-decimal (subseq str 0 end)) *nan*)))))))
(defun float-prefix-end (str)
  (let ((n (length str)) (i 0) (seen-digit nil))
    (when (and (< i n) (member (char str i) '(#\+ #\-))) (incf i))
    (loop while (and (< i n) (digit-char-p (char str i))) do (incf i) (setf seen-digit t))
    (when (and (< i n) (char= (char str i) #\.)) (incf i)
      (loop while (and (< i n) (digit-char-p (char str i))) do (incf i) (setf seen-digit t)))
    (unless seen-digit (return-from float-prefix-end 0))
    (when (and (< i n) (member (char str i) '(#\e #\E)))
      (let ((j (1+ i))) (when (and (< j n) (member (char str j) '(#\+ #\-))) (incf j))
        (let ((k j)) (loop while (and (< k n) (digit-char-p (char str k))) do (incf k))
          (when (> k j) (setf i k)))))
    i))

;;; ---------------------------------------------------------------------------
;;; Reflect
;;; ---------------------------------------------------------------------------
(defun install-reflect (realm)
  (let ((reflect (make-object :proto (realm-object-proto realm))))
    (macrolet ((need-obj (v) `(unless (js-object-p ,v) (js-throw (make-native-error "TypeError" "Reflect target must be an object")))))
      (def-method realm reflect "apply" 3 (this args)
        (let ((target (arg 0 args)))
          (unless (js-callable-p target) (js-throw (make-native-error "TypeError" "target must be callable")))
          (js-call target (arg 1 args) (array-like-to-list (arg 2 args)))))
      (def-method realm reflect "construct" 2 (this args)
        (let* ((target (arg 0 args))
               (nt (if (>= (length args) 3) (arg 2 args) target)))
          (unless (and (js-object-p target) (js-object-construct target))
            (js-throw (make-native-error "TypeError" "target is not a constructor")))
          (unless (and (js-object-p nt) (js-object-construct nt))
            (js-throw (make-native-error "TypeError" "newTarget is not a constructor")))
          (js-construct target (array-like-to-list (arg 1 args)) nt)))
      (def-method realm reflect "get" 2 (this args)
        (need-obj (arg 0 args))
        (js-get (arg 0 args) (to-property-key (arg 1 args)) (if (>= (length args) 3) (arg 2 args) (arg 0 args))))
      (def-method realm reflect "set" 3 (this args)
        (need-obj (arg 0 args))
        (js-bool (js-truthy* (js-set (arg 0 args) (to-property-key (arg 1 args)) (arg 2 args)
                                     (if (>= (length args) 4) (arg 3 args) (arg 0 args))))))
      (def-method realm reflect "has" 2 (this args)
        (need-obj (arg 0 args)) (js-bool (js-truthy* (js-has (arg 0 args) (to-property-key (arg 1 args))))))
      (def-method realm reflect "deleteProperty" 2 (this args)
        (need-obj (arg 0 args)) (js-bool (js-truthy* (js-delete (arg 0 args) (to-property-key (arg 1 args))))))
      (def-method realm reflect "ownKeys" 1 (this args)
        (need-obj (arg 0 args)) (make-array-object (js-own-keys (arg 0 args))))
      (def-method realm reflect "getPrototypeOf" 1 (this args)
        (need-obj (arg 0 args))
        (let ((p (js-get-proto (arg 0 args)))) (if (js-object-p p) p *null*)))
      (def-method realm reflect "setPrototypeOf" 2 (this args)
        (need-obj (arg 0 args))
        (let ((p (arg 1 args)))
          (unless (or (js-object-p p) (eq p *null*)) (js-throw (make-native-error "TypeError" "proto must be object or null")))
          (js-bool (js-set-proto (arg 0 args) p))))
      (def-method realm reflect "isExtensible" 1 (this args)
        (need-obj (arg 0 args)) (js-bool (js-extensible-p (arg 0 args))))
      (def-method realm reflect "preventExtensions" 1 (this args)
        (need-obj (arg 0 args)) (js-bool (js-prevent-extensions (arg 0 args))))
      (def-method realm reflect "defineProperty" 3 (this args)
        (need-obj (arg 0 args))
        (js-bool (js-define-own-property (arg 0 args) (to-property-key (arg 1 args))
                                         (to-property-descriptor (arg 2 args)))))
      (def-method realm reflect "getOwnPropertyDescriptor" 2 (this args)
        (need-obj (arg 0 args))
        (from-property-descriptor realm (js-get-own-property (arg 0 args) (to-property-key (arg 1 args))))))
    (put reflect (symbol-tostringtag realm) "Reflect" :enumerable nil :writable nil :configurable t)
    (define-global realm "Reflect" reflect)))

;;; ---------------------------------------------------------------------------
;;; Function constructor (real: compiles a function from string params + body)
;;; ---------------------------------------------------------------------------
(defun install-function-ctor (realm fp)
  (flet ((build (args)
           (let* ((n (length args))
                  (body (if (zerop n) "" (to-string (car (last args)))))
                  (params (format nil "~{~a~^,~}" (mapcar #'to-string (butlast args))))
                  (src (format nil "(function anonymous(~a~%) {~%~a~%})" params body)))
             (let ((*current-realm* realm))
               (run (compile-toplevel src) (realm-global-env realm) (realm-global realm))))))
    (let ((ctor (native-function realm "Function" (lambda (this args) (declare (ignore this)) (build args)) 1)))
      (setf (js-object-construct ctor) (lambda (args nt) (declare (ignore nt)) (build args)))
      (def-value ctor "prototype" fp :writable nil :configurable nil)
      (def-value fp "constructor" ctor)
      (define-global realm "Function" ctor))))

;;; ---------------------------------------------------------------------------
;;; console + eval
;;; ---------------------------------------------------------------------------
(defun install-console-eval (realm)
  (let ((console (make-object :proto (realm-object-proto realm))))
    (def-method realm console "log" 0 (this args)
      (format t "~&~{~a~^ ~}~%" (mapcar (lambda (v) (ignore-errors (to-string v))) args)) *undefined*)
    (def-method realm console "error" 0 (this args)
      (format t "~&~{~a~^ ~}~%" (mapcar (lambda (v) (ignore-errors (to-string v))) args)) *undefined*)
    (def-method realm console "warn" 0 (this args)
      (format t "~&~{~a~^ ~}~%" (mapcar (lambda (v) (ignore-errors (to-string v))) args)) *undefined*)
    (define-global realm "console" console))
  ;; %eval%: the global eval function. A CALL through this binding is *indirect*
  ;; eval — it always evaluates in the global environment (never the caller's).
  ;; A *direct* eval (source-level `eval(x)` where `eval` is unshadowed) is
  ;; recognized by the compiler and handled by the VM's :eval-direct opcode,
  ;; which shares the caller's env/this; it only reaches this function object
  ;; for the identity check. Non-string input is returned unchanged.
  (let ((eval-fn
          (native-function realm "eval"
            (lambda (this args) (declare (ignore this))
              (let ((s (arg 0 args)))
                (if (stringp s)
                    (let ((code (handler-case (compile-toplevel s)
                                  (shuttle-error (e) (error e))
                                  (error (e)
                                    (js-throw (make-native-error "SyntaxError"
                                                (format nil "~a" (ignore-errors (princ-to-string e)))))))))
                      (with-js-floats (run code (realm-global-env realm) (realm-global realm))))
                    s))) 1)))
    (setf (getf (realm-intrinsics realm) :eval) eval-fn)
    (define-global realm "eval" eval-fn)))
