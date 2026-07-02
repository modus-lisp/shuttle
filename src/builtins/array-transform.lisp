;;;; See array-iteration.lisp for the convention + available helpers.
;;;; Fill the (install-array-transform realm) body; do not touch other files.
(in-package #:shuttle)

(defvar *symbol-is-concat-spreadable* nil
  "The @@isConcatSpreadable well-known symbol, created when this group installs.")

(defun %js-array-p (x)
  "True if X is a JS Array object (plain-array flavor)."
  (and (js-object-p x) (string= (js-object-class x) "Array")))

(defun %concat-spreadable-p (e)
  "IsConcatSpreadable(E): non-object -> false; else @@isConcatSpreadable if
   present (coerced to boolean), otherwise IsArray(E)."
  (when (js-object-p e)
    (let ((flag (if *symbol-is-concat-spreadable*
                    (js-get e *symbol-is-concat-spreadable*)
                    *undefined*)))
      (if (js-undefined-p flag)
          (%js-array-p e)
          (js-truthy flag)))))

(defun %array-iterator-proto (realm)
  "The prototype the kernel's make-array-iterator hands out, so keys()/entries()
   share %ArrayIteratorPrototype% with values()/@@iterator (spec requirement)."
  (js-object-proto (make-array-iterator realm (make-array-object '()))))

(defun make-array-iterator-kind (realm arr kind)
  "Array iterator like make-array-iterator, but KIND selects what NEXT yields:
   :key -> index number, :value -> element, :entry -> [index, element] array.
   Once exhausted it stays done (spec: [[IteratedArrayLike]] is released)."
  (let ((i 0) (done nil)
        (it (make-object :proto (%array-iterator-proto realm) :class "Array Iterator")))
    (def-method realm it "next" 0 (this args)
      (let ((res (make-object :proto (realm-object-proto realm))))
        (if done
            (progn (put res "value" *undefined*) (put res "done" *true*))
            (let ((len (to-int-index (js-get arr "length"))))
              (if (< i len)
                  (let ((idx (float i 1d0)))
                    (put res "value"
                         (ecase kind
                           (:key idx)
                           (:value (js-get arr (princ-to-string i)))
                           (:entry (make-array-object
                                    (list idx (js-get arr (princ-to-string i)))))))
                    (put res "done" *false*)
                    (incf i))
                  (progn (setf done t)
                         (put res "value" *undefined*) (put res "done" *true*)))))
        res))
    (when *symbol-iterator*
      (put it *symbol-iterator*
           (native-function realm "[Symbol.iterator]"
             (lambda (this args) (declare (ignore args)) this) 0)
           :enumerable nil))
    it))

(defun flatten-into (source start out depth mapper-fn ta)
  "FlattenIntoArray: append flattened elements of SOURCE to list OUT (reversed
   accumulator returned). START = next target index (for mapper callback arg),
   DEPTH = remaining flatten depth. Returns (values new-out next-index)."
  (let ((len (truncate (to-length (js-get source "length"))))
        (idx start))
    (dotimes (i len)
      (let ((k (princ-to-string i)))
        (when (js-truthy* (js-has source k))
          (let ((element (js-get source k)))
            (when mapper-fn
              (setf element (js-call mapper-fn ta (list element (float i 1d0) source))))
            (if (and (> depth 0) (%js-array-p element))
                (multiple-value-bind (new-out next-idx)
                    (flatten-into element idx out (1- depth) nil *undefined*)
                  (setf out new-out idx next-idx))
                (progn (push element out) (incf idx)))))))
    (values out idx)))

(defun %array-species-check (o)
  "ArraySpeciesCreate's constructor validation (no subclassing support): if
   O.constructor is neither undefined nor a constructor (nor an object exposing a
   valid @@species), throw a TypeError.  Otherwise the default ArrayCreate path
   is used by the caller.  Only applies when IsArray(O) is true — for non-array
   receivers ArraySpeciesCreate short-circuits to ArrayCreate without reading
   the constructor at all."
  (unless (%js-array-p o) (return-from %array-species-check nil))
  (let ((c (js-get o "constructor")))
    (unless (js-undefined-p c)
      (if (js-object-p c)
          ;; C is an object: consult @@species; null/undefined -> default path.
          (let* ((sp (well-known-symbol "species"))
                 (species (if sp (js-get c sp) *undefined*)))
            (cond ((or (js-undefined-p species) (eq species *null*)) nil)
                  ((and (js-object-p species) (js-object-construct species)) nil)
                  (t (js-throw (make-native-error "TypeError"
                                                  "constructor is not a valid array species")))))
          ;; C is a primitive other than undefined: IsConstructor is false.
          (js-throw (make-native-error "TypeError"
                                       "constructor is not a valid array species"))))))

(defun install-array-transform (realm)
  (let ((ap (realm-array-proto realm)))
    ;; Create the @@isConcatSpreadable well-known symbol and expose it on the
    ;; Symbol constructor (installed earlier in the realm build).
    (let ((sym (make-js-symbol "Symbol.isConcatSpreadable")))
      (setf *symbol-is-concat-spreadable* sym)
      (let ((symbol-ctor (ignore-errors (js-get (realm-global realm) "Symbol"))))
        (when (and symbol-ctor (js-object-p symbol-ctor))
          (def-value symbol-ctor "isConcatSpreadable" sym
                     :writable nil :configurable nil))))

    ;; Array.prototype [ @@unscopables ]: a null-proto object whose keys are the
    ;; method names added after ES5 (so `with` blocks don't shadow them).  The
    ;; well-known symbol isn't otherwise created, so make + expose it on Symbol.
    (let ((unsym (or (well-known-symbol "unscopables")
                     (make-js-symbol "Symbol.unscopables"))))
      (let ((symbol-ctor (ignore-errors (js-get (realm-global realm) "Symbol"))))
        (when (and symbol-ctor (js-object-p symbol-ctor)
                   (js-undefined-p (js-get symbol-ctor "unscopables")))
          (def-value symbol-ctor "unscopables" unsym :writable nil :configurable nil)))
      (let ((ul (make-object :proto *null*)))
        (dolist (name '("at" "copyWithin" "entries" "fill" "find" "findIndex"
                        "findLast" "findLastIndex" "flat" "flatMap" "includes"
                        "keys" "toReversed" "toSorted" "toSpliced" "values"))
          (put ul name *true*))
        (put ap unsym ul :enumerable nil :writable nil :configurable t)))

    (flet ((len (this) (to-int-index (js-get this "length"))))
      (declare (ignorable #'len))

      (def-method realm ap "concat" 1 (this args)
        (let* ((o (to-object this))
               (a (progn
                    ;; ArraySpeciesCreate(O, 0): validate O.constructor (+ @@species)
                    ;; before spreading any items.
                    (%array-species-check o)
                    (make-object :proto (realm-array-proto realm) :class "Array")))
               (n 0))
          ;; items = [O, ...arguments]; O is ToObject(this value).
          (dolist (e (cons o args))
            (if (%concat-spreadable-p e)
                (let ((l (truncate (to-length (js-get e "length")))))
                  ;; n + len must not exceed 2^53-1 (checked before copying).
                  (when (> (+ n l) 9007199254740991)
                    (js-throw (make-native-error "TypeError" "concat result exceeds maximum array length")))
                  (dotimes (i l)
                    (let ((k (princ-to-string i)))
                      (when (js-truthy* (js-has e k))
                        (put a (princ-to-string n) (js-get e k))))
                    (incf n)))
                (progn
                  (when (>= n 9007199254740991)
                    (js-throw (make-native-error "TypeError" "concat result exceeds maximum array length")))
                  (put a (princ-to-string n) e) (incf n))))
          (put a "length" (float n 1d0) :enumerable nil)
          a))

      (def-method realm ap "flat" 0 (this args)
        (let* ((o (to-object this))
               (depth-arg (arg 0 args))
               (depth (if (js-undefined-p depth-arg) 1
                          (to-integer-or-infinity depth-arg))))
          (%array-species-check o)
          (make-array-object (nreverse (flatten-into o 0 '() depth nil *undefined*)))))

      (def-method realm ap "flatMap" 1 (this args)
        (let* ((o (to-object this))
               (fn (arg 0 args))
               (ta (arg 1 args)))
          (unless (js-callable-p fn)
            (js-throw (make-native-error "TypeError" "flatMap callback is not a function")))
          (%array-species-check o)
          (make-array-object (nreverse (flatten-into o 0 '() 1 fn ta)))))

      ;; Override kernel values/@@iterator so ToObject(this) coerces primitives
      ;; and throws on null/undefined.  @@iterator must be the SAME function
      ;; object as `values` (spec: %Array.prototype.values%).
      (def-method realm ap "values" 0 (this args)
        (make-array-iterator-kind realm (to-object this) :value))
      (when *symbol-iterator*
        (put ap *symbol-iterator* (js-get ap "values")
             :enumerable nil :writable t :configurable t))

      (def-method realm ap "keys" 0 (this args)
        (make-array-iterator-kind realm (to-object this) :key))

      (def-method realm ap "entries" 0 (this args)
        (make-array-iterator-kind realm (to-object this) :entry))

      ;; ---- Array.from override (kernel version ignores mapFn validation,
      ;; the this-constructor, string primitives, and @@iterator on boxed
      ;; primitives).  Spec: Array.from ( items [ , mapfn [ , thisArg ] ] ).
      (let ((actor (ignore-errors (js-get (realm-global realm) "Array"))))
        (when (and actor (js-object-p actor))
          (labels ((create-data (o k v)
                     ;; CreateDataProperty(O, P, V): DefineOwnProperty with a full
                     ;; data descriptor.  Returns T/NIL (caller throws on NIL).
                     (js-define-own-property o (prop-key k)
                                             (list :value v :writable t
                                                   :enumerable t :configurable t)))
                   (iter-close-quiet (it)
                     ;; IteratorClose on abrupt completion: call return() for side
                     ;; effects, swallow any throw it produces.
                     (let ((ret (and (js-object-p it) (js-get it "return"))))
                       (when (and ret (not (js-null-or-undef ret)) (js-callable-p ret))
                         (handler-case (js-call ret it '()) (shuttle-error () nil)))))
                   (make-result (c len)
                     ;; C = this value.  If C is a constructor, Construct(C[,len]);
                     ;; else ArrayCreate(len).
                     (if (and (js-object-p c) (js-object-construct c))
                         (js-construct c (if len (list (float len 1d0)) '()))
                         (let ((a (make-object :proto (realm-array-proto realm) :class "Array")))
                           (put a "length" (float (or len 0) 1d0)
                                :enumerable nil :writable t :configurable nil)
                           a))))
            (def-method realm actor "from" 1 (this args)
              (let* ((items (arg 0 args))
                     (mapf (arg 1 args))
                     (thisarg (arg 2 args))
                     (mapping (not (js-undefined-p mapf))))
                (when (and mapping (not (js-callable-p mapf)))
                  (js-throw (make-native-error "TypeError" "Array.from mapfn is not a function")))
                (let ((usingit (and *symbol-iterator*
                                    (let ((m (js-get (to-object items) *symbol-iterator*)))
                                      (cond ((js-null-or-undef m) nil)
                                            ((js-callable-p m) m)
                                            (t (js-throw (make-native-error "TypeError"
                                                          "@@iterator is not callable"))))))))
                  (if usingit
                      ;; Iterator path.
                      (let* ((a (make-result this nil))
                             (it (js-call usingit (to-object items) '()))
                             (k 0))
                        (unless (js-object-p it)
                          (js-throw (make-native-error "TypeError" "iterator is not an object")))
                        (loop
                          (let ((r (iterator-step it)))
                            (when (js-truthy (js-get r "done"))
                              (js-set a "length" (float k 1d0) a)
                              (return a))
                            (let ((v (js-get r "value")))
                              (handler-case
                                  (let ((mapped (if mapping
                                                    (js-call mapf thisarg (list v (float k 1d0)))
                                                    v)))
                                    (unless (create-data a (princ-to-string k) mapped)
                                      (js-throw (make-native-error "TypeError"
                                                 "cannot create result element"))))
                                (shuttle-error (e) (iter-close-quiet it) (error e)))
                              (incf k)))))
                      ;; Array-like path.
                      (let* ((o (to-object items))
                             (len (truncate (to-length (js-get o "length"))))
                             (a (make-result this len))
                             (k 0))
                        (dotimes (i len)
                          (let* ((v (js-get o (princ-to-string i)))
                                 (mapped (if mapping (js-call mapf thisarg (list v (float i 1d0))) v)))
                            (unless (create-data a (princ-to-string k) mapped)
                              (js-throw (make-native-error "TypeError" "cannot create result element"))))
                          (incf k))
                        (js-set a "length" (float len 1d0) a)
                        a))))))))

      (def-method realm ap "toLocaleString" 0 (this args)
        (let* ((o (to-object this))
               (l (truncate (to-length (js-get o "length")))))
          (with-output-to-string (s)
            (dotimes (i l)
              (when (> i 0) (write-char #\, s))
              (let ((v (js-get o (princ-to-string i))))
                (unless (js-null-or-undef v)
                  (let ((m (js-get v "toLocaleString")))
                    (if (js-callable-p m)
                        (write-string (to-string (js-call m v '())) s)
                        (js-throw (make-native-error "TypeError"
                                                     "toLocaleString is not callable")))))))))))))

(register-builtin-installer 'install-array-transform)
