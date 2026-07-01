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

(defun make-array-iterator-kind (realm arr kind)
  "Array iterator like make-array-iterator, but KIND selects what NEXT yields:
   :key -> index number, :value -> element, :entry -> [index, element] array.
   Once exhausted it stays done (spec: [[IteratedArrayLike]] is released)."
  (let ((i 0) (done nil)
        (it (make-object :proto (realm-object-proto realm) :class "Array Iterator")))
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

    (flet ((len (this) (to-int-index (js-get this "length"))))
      (declare (ignorable #'len))

      (def-method realm ap "concat" 1 (this args)
        (let ((a (make-object :proto (realm-array-proto realm) :class "Array"))
              (n 0))
          ;; items = [O, ...arguments]; O is ToObject(this value).
          (dolist (e (cons (to-object this) args))
            (if (%concat-spreadable-p e)
                (let ((l (to-length (js-get e "length"))))
                  (dotimes (i (truncate l))
                    (let ((k (princ-to-string i)))
                      (when (js-truthy* (js-has e k))
                        (put a (princ-to-string n) (js-get e k))))
                    (incf n)))
                (progn (put a (princ-to-string n) e) (incf n))))
          (put a "length" (float n 1d0) :enumerable nil)
          a))

      (def-method realm ap "flat" 0 (this args)
        (let* ((o (to-object this))
               (depth-arg (arg 0 args))
               (depth (if (js-undefined-p depth-arg) 1
                          (to-integer-or-infinity depth-arg))))
          (make-array-object (nreverse (flatten-into o 0 '() depth nil *undefined*)))))

      (def-method realm ap "flatMap" 1 (this args)
        (let* ((o (to-object this))
               (fn (arg 0 args))
               (ta (arg 1 args)))
          (unless (js-callable-p fn)
            (js-throw (make-native-error "TypeError" "flatMap callback is not a function")))
          (make-array-object (nreverse (flatten-into o 0 '() 1 fn ta)))))

      (def-method realm ap "keys" 0 (this args)
        (make-array-iterator-kind realm (to-object this) :key))

      (def-method realm ap "entries" 0 (this args)
        (make-array-iterator-kind realm (to-object this) :entry))

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
