;;;; builtins/iterator.lisp — Iterator + %IteratorPrototype% helpers
;;;; (map/filter/take/drop/flatMap/reduce/toArray/forEach/some/every/find),
;;;; the Iterator constructor, and Iterator.from wrappers.
;;;;
;;;; Structure (mirrors the spec's intrinsics):
;;;;   %IteratorPrototype%              === Iterator.prototype   (proto: object-proto)
;;;;   %IteratorHelperPrototype%        (proto: Iterator.prototype)  next/return of map/filter/…
;;;;   %WrapForValidIteratorPrototype%  (proto: Iterator.prototype)  Iterator.from wrappers
;;;;
;;;; The realm's kernel builds array/string iterators with proto = object-proto;
;;;; we REDEFINE make-array-iterator/make-string-iterator below so those iterators
;;;; inherit from %IteratorPrototype% (test262 asserts
;;;;   getPrototypeOf(getPrototypeOf([][Symbol.iterator]())) === %IteratorPrototype%).
;;;; This file loads last (asd :serial t), so these redefinitions win.
(in-package #:shuttle)

;;; Symbol.dispose well-known symbol — the special var is (re)defined here so
;;; iterator.lisp (which loads before disposable.lisp) can bind @@dispose on
;;; %IteratorPrototype%.  DEFVAR is idempotent, so disposable.lisp's own defvar
;;; and its (or *symbol-dispose* ...) reuse the SAME symbol object.
(defvar *symbol-dispose* nil)

;;; The shared %IteratorPrototype% for the current realm (set at install time).
(defvar *iterator-prototype* nil)
;;; %ArrayIteratorPrototype% / %StringIteratorPrototype% — one level below
;;; %IteratorPrototype% so that getPrototypeOf(getPrototypeOf(arrIter)) === iproto.
(defvar *array-iterator-prototype* nil)
(defvar *string-iterator-prototype* nil)

;;; ---------------------------------------------------------------------------
;;; Abstract-operation helpers (spec-named)
;;; ---------------------------------------------------------------------------
(defun %iter-not-object (this)
  (unless (js-object-p this)
    (js-throw (make-native-error "TypeError" "Iterator method called on non-object"))))

(defun %get-iterator-direct (obj)
  "GetIteratorDirect(obj): obj must be an Object; read its .next once.
   Returns (values iterator next-method)."
  (%iter-not-object obj)
  (let ((next (js-get obj "next")))
    (values obj next)))

(defun %iter-close (iterator)
  "IteratorClose (normal completion): call iterator.return() if present, ignore
   its result. GetMethod: null/undefined -> no-op; else must be callable."
  (when (js-object-p iterator)
    (let ((ret (js-get iterator "return")))
      (unless (js-null-or-undef ret)
        (unless (js-callable-p ret)
          (js-throw (make-native-error "TypeError" "return is not a function")))
        (js-call ret iterator '())))))

(defmacro %iter-close-on-abrupt (iterator &body body)
  "Run BODY; if it throws (abrupt completion), IteratorClose the ITERATOR and then
   re-raise BODY's original throw. Per IfAbruptCloseIterator/IteratorClose: when the
   incoming completion is a throw, the ORIGINAL throw wins even if return() also
   throws — return()'s throw is swallowed."
  (let ((it (gensym)) (e (gensym)))
    `(let ((,it ,iterator))
       (handler-case (progn ,@body)
         (shuttle-error (,e)
           ;; IteratorClose with an abrupt (throw) incoming completion: call
           ;; return() for side effects, but discard any throw it produces so the
           ;; original completion (,e) propagates.
           (let ((ret (and (js-object-p ,it) (js-get ,it "return"))))
             (when (and ret (not (js-null-or-undef ret)) (js-callable-p ret))
               (handler-case (js-call ret ,it '())
                 (shuttle-error () nil))))
           (error ,e))))))

(defun %iter-step-value (iterator next)
  "IteratorStepValue: call NEXT with ITERATOR as this; result must be an object;
   return (values value done-p)."
  (let ((r (js-call next iterator '())))
    (unless (js-object-p r)
      (js-throw (make-native-error "TypeError" "iterator result is not an object")))
    (if (js-truthy (js-get r "done"))
        (values *undefined* t)
        (values (js-get r "value") nil))))

;;; ---------------------------------------------------------------------------
;;; make-*-iterator overrides — inherit from %IteratorPrototype%
;;; ---------------------------------------------------------------------------
(defun make-array-iterator (realm arr)
  (let ((i 0) (it (make-object :proto (or *array-iterator-prototype* (realm-object-proto realm))
                               :class "Array Iterator")))
    (def-method realm it "next" 0 (this args)
      (let ((len (to-int-index (js-get arr "length")))
            (res (make-object :proto (realm-object-proto realm))))
        (if (< i len)
            (progn (put res "value" (js-get arr (princ-to-string i))) (put res "done" *false*) (incf i))
            (progn (put res "value" *undefined*) (put res "done" *true*)))
        res))
    (when *symbol-iterator*
      (put it *symbol-iterator*
           (native-function realm "[Symbol.iterator]" (lambda (this args) (declare (ignore args)) this) 0)
           :enumerable nil))
    it))

(defun make-string-iterator (realm s)
  (let ((i 0) (it (make-object :proto (or *string-iterator-prototype* (realm-object-proto realm))
                               :class "String Iterator")))
    (def-method realm it "next" 0 (this args)
      (let ((res (make-object :proto (realm-object-proto realm))))
        (if (< i (length s))
            ;; Advance by one code point (handle surrogate pairs).
            (let* ((c (char-code (char s i)))
                   (adv (if (and (<= #xD800 c #xDBFF) (< (1+ i) (length s))
                                 (<= #xDC00 (char-code (char s (1+ i))) #xDFFF))
                            2 1)))
              (put res "value" (subseq s i (+ i adv))) (put res "done" *false*) (incf i adv))
            (progn (put res "value" *undefined*) (put res "done" *true*)))
        res))
    (when *symbol-iterator*
      (put it *symbol-iterator*
           (native-function realm "[Symbol.iterator]" (lambda (this args) (declare (ignore args)) this) 0)
           :enumerable nil))
    it))

;;; ---------------------------------------------------------------------------
;;; Lazy iterator-helper builder
;;; ---------------------------------------------------------------------------
(defmacro def-helper (realm helper-proto (&rest bindings) &key step close)
  "Create a lazy iterator-helper object with proto HELPER-PROTO.
   BINDINGS are LET* bindings for closure state (e.g. the underlying iterator).
   STEP is a form evaluated on each next() that returns (values value done-p).
   CLOSE is a form run when the helper is closed early / exhausted (calls the
   underlying .return())."
  (let ((r (gensym)) (hp (gensym)) (obj (gensym)) (donef (gensym)) (runningf (gensym))
        (this (gensym)) (args (gensym)) (v (gensym)) (d (gensym)))
    `(let* ((,r ,realm) (,hp ,helper-proto) (,donef nil) (,runningf nil) ,@bindings
            (,obj (make-object :proto ,hp :class "Iterator Helper")))
       (put ,obj "next"
            (native-function ,r "next"
              (lambda (,this ,args) (declare (ignore ,this ,args))
                ;; Generator-brand re-entrancy check: calling next() while the
                ;; helper is already running (e.g. the mapper called it) is a
                ;; TypeError (spec: GeneratorValidate state = executing).
                (when ,runningf
                  (js-throw (make-native-error "TypeError" "Iterator helper is already running")))
                (let ((res (make-object :proto (realm-object-proto ,r))))
                  (if ,donef
                      (progn (put res "value" *undefined*) (put res "done" *true*))
                      (multiple-value-bind (,v ,d)
                          (progn (setf ,runningf t)
                                 (unwind-protect
                                      (handler-case ,step
                                        (shuttle-error (e) (setf ,donef t) (error e)))
                                   (setf ,runningf nil)))
                        (if ,d
                            (progn (setf ,donef t)
                                   (put res "value" *undefined*) (put res "done" *true*))
                            (progn (put res "value" ,v) (put res "done" *false*)))))
                  res))
              0)
            :enumerable nil :writable t :configurable t)
       (put ,obj "return"
            (native-function ,r "return"
              (lambda (,this ,args) (declare (ignore ,this ,args))
                (let ((res (make-object :proto (realm-object-proto ,r))))
                  (unless ,donef
                    (setf ,donef t)
                    ,close)
                  (put res "value" *undefined*) (put res "done" *true*)
                  res))
              0)
            :enumerable nil :writable t :configurable t)
       ,obj)))

;;; ---------------------------------------------------------------------------
;;; installer
;;; ---------------------------------------------------------------------------
(defun install-iterator (realm)
  (let* ((op (realm-object-proto realm))
         (fp (realm-function-proto realm))
         (tostag (symbol-tostringtag realm))
         ;; %IteratorPrototype% === Iterator.prototype
         (iproto (make-object :proto op))
         ;; %IteratorHelperPrototype% (map/filter/… results)
         (helper-proto (make-object :proto iproto :class "Iterator Helper"))
         ;; %WrapForValidIteratorPrototype% (Iterator.from wrappers)
         (wrap-proto (make-object :proto iproto :class "Iterator"))
         ;; %ArrayIteratorPrototype% / %StringIteratorPrototype%
         (arr-it-proto (make-object :proto iproto :class "Array Iterator"))
         (str-it-proto (make-object :proto iproto :class "String Iterator")))
    (setf *iterator-prototype* iproto
          *array-iterator-prototype* arr-it-proto
          *string-iterator-prototype* str-it-proto)

    ;; ---- %IteratorPrototype% [ @@iterator ] () { return this } ----
    (when *symbol-iterator*
      (put iproto *symbol-iterator*
           (native-function realm "[Symbol.iterator]"
             (lambda (this args) (declare (ignore args)) this) 0)
           :enumerable nil :writable t :configurable t))
    ;; @@toStringTag on the array/string iterator prototypes (spec: own data prop)
    (put arr-it-proto tostag "Array Iterator" :enumerable nil :writable nil :configurable t)
    (put str-it-proto tostag "String Iterator" :enumerable nil :writable nil :configurable t)

    ;; ---- helper method definitions (all take GetIteratorDirect(this)) ----
    (labels ((callable-or-throw (f close-it)
               (unless (js-callable-p f)
                 (when close-it (%iter-close close-it))
                 (js-throw (make-native-error "TypeError" "not a function"))))
             (limit-number (limit close-it)
               ;; ToNumber -> NaN? RangeError ; ToIntegerOrInfinity ; <0? RangeError
               (let ((num (handler-case (to-number limit)
                            (shuttle-error (e) (when close-it (%iter-close close-it)) (error e)))))
                 (when (js-nan-p num)
                   (when close-it (%iter-close close-it))
                   (js-throw (make-native-error "RangeError" "limit must not be NaN")))
                 (let ((int (to-integer-or-infinity num)))
                   (when (< int 0)
                     (when close-it (%iter-close close-it))
                     (js-throw (make-native-error "RangeError" "limit must not be negative")))
                   int))))

      ;; ---- map ----
      (def-method realm iproto "map" 1 (this args)
        (%iter-not-object this)
        (let ((fn (arg 0 args)) (count 0))
          (callable-or-throw fn this)
          (multiple-value-bind (it next) (%get-iterator-direct this)
            (def-helper realm helper-proto ()
              :step (multiple-value-bind (v d) (%iter-step-value it next)
                      (if d (values *undefined* t)
                          (let ((mapped (%iter-close-on-abrupt it
                                          (js-call fn *undefined* (list v (float count 1d0))))))
                            (incf count)
                            (values mapped nil))))
              :close (%iter-close it)))))

      ;; ---- filter ----
      (def-method realm iproto "filter" 1 (this args)
        (%iter-not-object this)
        (let ((fn (arg 0 args)) (count 0))
          (callable-or-throw fn this)
          (multiple-value-bind (it next) (%get-iterator-direct this)
            (def-helper realm helper-proto ()
              :step (block step
                      (loop
                        (multiple-value-bind (v d) (%iter-step-value it next)
                          (when d (return-from step (values *undefined* t)))
                          (let ((sel (%iter-close-on-abrupt it
                                       (js-call fn *undefined* (list v (float count 1d0))))))
                            (incf count)
                            (when (js-truthy sel) (return-from step (values v nil)))))))
              :close (%iter-close it)))))

      ;; ---- take ----
      (def-method realm iproto "take" 1 (this args)
        (%iter-not-object this)
        (let* ((remaining (limit-number (arg 0 args) this)))
          (multiple-value-bind (it next) (%get-iterator-direct this)
            (def-helper realm helper-proto ()
              :step (if (<= remaining 0)
                        (progn (%iter-close it) (values *undefined* t))
                        (progn
                          (unless (= remaining *inf*) (decf remaining))
                          (multiple-value-bind (v d) (%iter-step-value it next)
                            (if d (values *undefined* t) (values v nil)))))
              :close (%iter-close it)))))

      ;; ---- drop ----
      (def-method realm iproto "drop" 1 (this args)
        (%iter-not-object this)
        (let* ((to-drop (limit-number (arg 0 args) this)) (dropped nil))
          (multiple-value-bind (it next) (%get-iterator-direct this)
            (def-helper realm helper-proto ()
              :step (progn
                      (unless dropped
                        (setf dropped t)
                        (loop while (> to-drop 0) do
                          (unless (= to-drop *inf*) (decf to-drop))
                          (multiple-value-bind (v d) (%iter-step-value it next)
                            (declare (ignore v))
                            (when d (return)))))
                      (multiple-value-bind (v d) (%iter-step-value it next)
                        (if d (values *undefined* t) (values v nil))))
              :close (%iter-close it)))))

      ;; ---- flatMap ----
      (def-method realm iproto "flatMap" 1 (this args)
        (%iter-not-object this)
        (let ((fn (arg 0 args)) (count 0)
              (inner nil) (inner-next nil))
          (callable-or-throw fn this)
          (multiple-value-bind (it next) (%get-iterator-direct this)
            (def-helper realm helper-proto ()
              :step (block step
                      (loop
                        (if inner
                            (multiple-value-bind (iv idone) (%iter-step-value inner inner-next)
                              (if idone
                                  (setf inner nil inner-next nil)
                                  (return-from step (values iv nil))))
                            (multiple-value-bind (v d) (%iter-step-value it next)
                              (when d (return-from step (values *undefined* t)))
                              (let ((mapped (%iter-close-on-abrupt it
                                              (js-call fn *undefined* (list v (float count 1d0))))))
                                (incf count)
                                ;; GetIteratorFlattenable(mapped, reject-strings)
                                (let ((innerit (%iter-close-on-abrupt it
                                                 (%get-iterator-flattenable mapped nil))))
                                  (setf inner innerit
                                        inner-next (js-get innerit "next"))))))))
              :close (progn (when inner (%iter-close inner)) (%iter-close it))))))

      ;; ---- reduce (eager) ----
      (def-method realm iproto "reduce" 1 (this args)
        (%iter-not-object this)
        (let ((fn (arg 0 args)) (has-acc (>= (length args) 2))
              (acc (arg 1 args)) (i 0))
          (callable-or-throw fn this)
          (multiple-value-bind (it next) (%get-iterator-direct this)
            (unless has-acc
              (multiple-value-bind (v d) (%iter-step-value it next)
                (when d
                  (js-throw (make-native-error "TypeError" "Reduce of empty iterator with no initial value")))
                (setf acc v has-acc t i 1)))
            (loop
              (multiple-value-bind (v d) (%iter-step-value it next)
                (when d (return acc))
                (setf acc (%iter-close-on-abrupt it
                            (js-call fn *undefined* (list acc v (float i 1d0)))))
                (incf i))))))

      ;; ---- toArray (eager) ----
      (def-method realm iproto "toArray" 0 (this args)
        (%iter-not-object this)
        (multiple-value-bind (it next) (%get-iterator-direct this)
          (let ((out '()))
            (loop
              (multiple-value-bind (v d) (%iter-step-value it next)
                (when d (return (make-array-object (nreverse out))))
                (push v out))))))

      ;; ---- forEach (eager) ----
      (def-method realm iproto "forEach" 1 (this args)
        (%iter-not-object this)
        (let ((fn (arg 0 args)) (i 0))
          (callable-or-throw fn this)
          (multiple-value-bind (it next) (%get-iterator-direct this)
            (loop
              (multiple-value-bind (v d) (%iter-step-value it next)
                (when d (return *undefined*))
                (%iter-close-on-abrupt it (js-call fn *undefined* (list v (float i 1d0))))
                (incf i))))))

      ;; ---- some (eager, short-circuits + closes) ----
      (def-method realm iproto "some" 1 (this args)
        (%iter-not-object this)
        (let ((fn (arg 0 args)) (i 0))
          (callable-or-throw fn this)
          (multiple-value-bind (it next) (%get-iterator-direct this)
            (loop
              (multiple-value-bind (v d) (%iter-step-value it next)
                (when d (return *false*))
                (when (js-truthy (%iter-close-on-abrupt it
                                   (js-call fn *undefined* (list v (float i 1d0)))))
                  (%iter-close it)
                  (return *true*))
                (incf i))))))

      ;; ---- every ----
      (def-method realm iproto "every" 1 (this args)
        (%iter-not-object this)
        (let ((fn (arg 0 args)) (i 0))
          (callable-or-throw fn this)
          (multiple-value-bind (it next) (%get-iterator-direct this)
            (loop
              (multiple-value-bind (v d) (%iter-step-value it next)
                (when d (return *true*))
                (unless (js-truthy (%iter-close-on-abrupt it
                                     (js-call fn *undefined* (list v (float i 1d0)))))
                  (%iter-close it)
                  (return *false*))
                (incf i))))))

      ;; ---- find ----
      (def-method realm iproto "find" 1 (this args)
        (%iter-not-object this)
        (let ((fn (arg 0 args)) (i 0))
          (callable-or-throw fn this)
          (multiple-value-bind (it next) (%get-iterator-direct this)
            (loop
              (multiple-value-bind (v d) (%iter-step-value it next)
                (when d (return *undefined*))
                (when (js-truthy (%iter-close-on-abrupt it
                                   (js-call fn *undefined* (list v (float i 1d0)))))
                  (%iter-close it)
                  (return v))
                (incf i)))))))

    ;; ---- %WrapForValidIteratorPrototype% shared next/return (Iterator.from) ----
    ;; Wrappers carry the underlying iterator under :wrap-iterated and its .next
    ;; method under :wrap-next. next/return are shared prototype methods that
    ;; RequireInternalSlot([[Iterated]]).
    (flet ((wrap-slot (this)
             (let ((it (and (js-object-p this) (js-object-internal this)
                            (getf (js-object-internal this) :wrap-iterated))))
               (unless it
                 (js-throw (make-native-error "TypeError"
                             "method called on incompatible receiver (not a wrapper)")))
               it)))
      (def-method realm wrap-proto "next" 0 (this args)
        (declare (ignore args))
        (let ((it (wrap-slot this))
              (next (getf (js-object-internal this) :wrap-next)))
          (js-call next it '())))
      (def-method realm wrap-proto "return" 0 (this args)
        (declare (ignore args))
        (let* ((it (wrap-slot this))
               (ret (js-get it "return")))
          (if (js-null-or-undef ret)
              (let ((res (make-object :proto (realm-object-proto realm))))
                (put res "value" *undefined*) (put res "done" *true*) res)
              (progn
                (unless (js-callable-p ret)
                  (js-throw (make-native-error "TypeError" "return is not a function")))
                (js-call ret it '()))))))

    ;; ---- Iterator.prototype[@@toStringTag] getter/setter (SetterThatIgnoresPrototypeProperties) ----
    (let ((getter (native-function realm "get [Symbol.toStringTag]"
                    (lambda (this args) (declare (ignore this args)) "Iterator") 0))
          (setter (native-function realm "set [Symbol.toStringTag]"
                    (lambda (this args)
                      (%setter-ignores-proto-props iproto tostag (arg 0 args) this)
                      *undefined*)
                    1)))
      (put-accessor iproto tostag :get getter :set setter :enumerable nil :configurable t))

    ;; ---- %IteratorPrototype% [ @@dispose ] () ----
    ;; A data method (writable, non-enumerable, configurable) named
    ;; "[Symbol.dispose]", length 0.  Calls GetMethod(this,"return") and, if
    ;; present, invokes it; always returns undefined.  We reuse (or create) the
    ;; Symbol.dispose well-known symbol so the later disposable installer shares
    ;; the SAME symbol object (and exposes it as Symbol.dispose).
    (let ((dispose-sym
            (or *symbol-dispose*
                (well-known-symbol "dispose")
                (setf *symbol-dispose* (make-js-symbol "Symbol.dispose")))))
      (setf *symbol-dispose* dispose-sym)
      (put iproto dispose-sym
           (native-function realm "[Symbol.dispose]"
             (lambda (this args) (declare (ignore args))
               (let ((ret (and (js-object-p this) (js-get this "return"))))
                 (unless (js-null-or-undef ret)
                   (unless (js-callable-p ret)
                     (js-throw (make-native-error "TypeError" "return is not a function")))
                   (js-call ret this '())))
               *undefined*)
             0)
           :enumerable nil :writable t :configurable t))

    ;; ---- Iterator.prototype.constructor getter/setter ----
    ;; (set below once ctor exists — placeholder replaced after ctor is built)

    ;; ---- the Iterator constructor ----
    (let* ((active-fn nil)
           (ctor (native-function realm "Iterator"
                   (lambda (this args) (declare (ignore this args))
                     ;; Called (not new): NewTarget is undefined -> TypeError.
                     (js-throw (make-native-error "TypeError" "Abstract class Iterator not directly constructable")))
                   0)))
      (setf active-fn ctor)
      (setf (js-object-construct ctor)
            (lambda (args nt) (declare (ignore args))
              ;; If NewTarget is undefined or the active function object, throw.
              (when (or (js-null-or-undef nt) (eq nt active-fn))
                (js-throw (make-native-error "TypeError" "Abstract class Iterator not directly constructable")))
              ;; OrdinaryCreateFromConstructor(newTarget, %Iterator.prototype%)
              (let ((proto (let ((p (and (js-object-p nt) (js-get nt "prototype"))))
                             (if (js-object-p p) p iproto))))
                (make-object :proto proto :class "Iterator"))))
      (def-value ctor "prototype" iproto :writable nil :configurable nil)

      ;; Iterator.prototype.constructor accessor (get -> ctor; set -> ignores-proto-props)
      (let ((cget (native-function realm "get constructor"
                    (lambda (this args) (declare (ignore this args)) ctor) 0))
            (cset (native-function realm "set constructor"
                    (lambda (this args)
                      (%setter-ignores-proto-props iproto "constructor" (arg 0 args) this)
                      *undefined*)
                    1)))
        (put-accessor iproto "constructor" :get cget :set cset :enumerable nil :configurable t))

      ;; ---- Iterator.from ----
      (def-method realm ctor "from" 1 (this args)
        (let* ((o (arg 0 args))
               ;; GetIteratorFlattenable(O, iterate-string-primitives)
               (rec (%get-iterator-flattenable o t))
               (it rec)
               (next (js-get rec "next")))
          ;; If it already inherits from %IteratorPrototype%, return it directly.
          (if (%inherits-from it iproto)
              it
              ;; else wrap in %WrapForValidIteratorPrototype% with [[Iterated]]/[[Next]]
              (make-object :proto wrap-proto :class "Iterator"
                           :internal (list :wrap-iterated it :wrap-next next)))))

      (define-global realm "Iterator" ctor)
      ;; define-global installs the property as enumerable; spec built-in globals
      ;; are non-enumerable (writable, configurable). Re-define on the global.
      (def-value (realm-global realm) "Iterator" ctor :writable t :configurable t))

    realm))

;;; ---------------------------------------------------------------------------
;;; small abstract-op helpers used above (defined after so they can be forward-referenced)
;;; ---------------------------------------------------------------------------
(defun %inherits-from (o proto)
  (and (js-object-p o)
       (loop for p = (js-object-proto o) then (js-object-proto p)
             while (js-object-p p) thereis (eq p proto))))

(defun %get-iterator-flattenable (obj string-handling)
  "GetIteratorFlattenable(obj, stringHandling).  Returns the iterator object
   (with a usable .next).  STRING-HANDLING t = iterate-string-primitives
   (Iterator.from), nil = reject-primitives (flatMap).
   Per spec, primitive strings are NOT boxed here: GetMethod(obj, @@iterator)
   and the @@iterator call both receive the primitive string as `this` (so a
   strict @@iterator getter observes typeof this === 'string')."
  (when (not (js-object-p obj))
    (unless (and string-handling (stringp obj))
      (js-throw (make-native-error "TypeError" "not an object"))))
  (let* ((itf (and *symbol-iterator* (js-get obj *symbol-iterator*)))
         (iterator
          (cond ((js-null-or-undef itf) obj)          ; fall back to treating obj as the iterator
                ((js-callable-p itf) (js-call itf obj '()))
                (t (js-throw (make-native-error "TypeError" "Symbol.iterator is not callable"))))))
    (unless (js-object-p iterator)
      (js-throw (make-native-error "TypeError" "iterator is not an object")))
    iterator))

(defun %setter-ignores-proto-props (home key v this)
  "SetterThatIgnoresPrototypeProperties(home, key, v, this).
   1. this must be Object.  2. If this is home -> throw (emulates non-writable
   data prop in strict mode).  3. If own desc undefined -> CreateDataProperty;
   else Set(this, key, v)."
  (unless (js-object-p this)
    (js-throw (make-native-error "TypeError" "receiver is not an object")))
  (when (eq this home)
    (js-throw (make-native-error "TypeError" "Cannot assign to read only property")))
  (let ((desc (js-get-own-property this key)))
    (if (null desc)
        (put this key v)                       ; CreateDataPropertyOrThrow
        (js-set this key v this))))            ; Set(this, key, v, true)

(register-builtin-installer 'install-iterator)
