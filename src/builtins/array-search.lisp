;;;; builtins/array-search.lisp — Array.prototype (search group).
;;;; See array-iteration.lisp for the convention + available helpers.
;;;; Fill the (install-array-search realm) body; do not touch other files.
(in-package #:shuttle)

(defun install-array-search (realm)
  (let ((ap (realm-array-proto realm)))
    (flet ((len (this) (to-int-index (js-get this "length")))
           (callable (f) (unless (js-callable-p f)
                           (js-throw (make-native-error "TypeError" "not a function")))))
      (declare (ignorable #'len #'callable))

      ;; Override kernel slice: ToObject/ToLength, Infinity clamping, holes,
      ;; and RangeError when the result length would exceed 2^32-1.
      (def-method realm ap "slice" 2 (this args)
        (let* ((o (to-object this))
               (l (truncate (to-length (js-get o "length"))))
               (rs (to-integer-or-infinity (arg 0 args)))
               (k (cond ((= rs *-inf*) 0)
                        ((< rs 0) (max (+ l (truncate rs)) 0))
                        ((= rs *inf*) l)
                        (t (min (truncate rs) l))))
               (end-arg (arg 1 args))
               (re (if (js-undefined-p end-arg) l (to-integer-or-infinity end-arg)))
               (final (cond ((= re *-inf*) 0)
                            ((< re 0) (max (+ l (truncate re)) 0))
                            ((= re *inf*) l)
                            (t (min (truncate re) l))))
               (count (max (- final k) 0)))
          ;; ArraySpeciesCreate(O, count): validate O.constructor (+ @@species).
          (%array-species-check o)
          (when (> count 4294967295)
            (js-throw (make-native-error "RangeError" "Invalid array length")))
          (let ((a (make-object :proto (realm-array-proto realm) :class "Array"))
                (n 0))
            (loop for i from k below final do
              (let ((kk (princ-to-string i)))
                (when (js-truthy* (js-has o kk))
                  (put a (princ-to-string n) (js-get o kk))))
              (incf n))
            (put a "length" (float count 1d0) :enumerable nil)
            a)))

      ;; Override kernel indexOf: full spec (ToObject/ToLength/fromIndex/holes).
      (def-method realm ap "indexOf" 1 (this args)
        (block done
          (let* ((o (to-object this))
                 (target (arg 0 args))
                 (l (truncate (to-length (js-get o "length")))))
            (when (= l 0) (return-from done -1d0))
            (let ((from (if (>= (length args) 2)
                            (let ((n (to-integer-or-infinity (arg 1 args))))
                              (cond ((= n *inf*) (return-from done -1d0))
                                    ((= n *-inf*) 0)
                                    (t (let ((k (truncate n)))
                                         (if (< k 0) (max 0 (+ l k)) k)))))
                            0)))
              (loop for i from from below l do
                (let ((kk (princ-to-string i)))
                  (when (js-truthy* (js-has o kk))
                    (when (js-strict-equal (js-get o kk) target)
                      (return-from done (float i 1d0))))))
              -1d0))))

      (def-method realm ap "lastIndexOf" 1 (this args)
        (block done
          (let* ((o (to-object this))
                 (target (arg 0 args))
                 (l (truncate (to-length (js-get o "length")))))
            (when (= l 0) (return-from done -1d0))
            ;; fromIndex defaults to length-1; negative is relative to length.
            (let ((from (if (>= (length args) 2)
                            (let ((n (to-integer-or-infinity (arg 1 args))))
                              (cond ((= n *inf*) (1- l))
                                    ((= n *-inf*) (return-from done -1d0))
                                    (t (let ((k (truncate n)))
                                         (if (< k 0) (+ l k) (min k (1- l)))))))
                            (1- l))))
              (loop for i from from downto 0 do
                (when (js-truthy* (js-has o (princ-to-string i)))
                  (when (js-strict-equal (js-get o (princ-to-string i)) target)
                    (return-from done (float i 1d0)))))
              -1d0))))

      (def-method realm ap "includes" 1 (this args)
        (block done
          (let* ((o (to-object this))
                 (target (arg 0 args))
                 (l (truncate (to-length (js-get o "length")))))
            (when (= l 0) (return-from done *false*))
            (let ((from (let ((n (to-integer-or-infinity (arg 1 args))))
                          (cond ((= n *inf*) (return-from done *false*))
                                ((= n *-inf*) 0)
                                (t (let ((k (truncate n)))
                                     (cond ((< k 0) (max 0 (+ l k)))
                                           (t k))))))))
              (loop for i from from below l do
                ;; does NOT skip holes — read via js-get (missing => undefined)
                (when (same-value-zero (js-get o (princ-to-string i)) target)
                  (return-from done *true*)))
              *false*))))

      (def-method realm ap "at" 1 (this args)
        (block done
          (let* ((o (to-object this))
                 (l (truncate (to-length (js-get o "length"))))
                 (n (to-integer-or-infinity (arg 0 args)))
                 (k (cond ((= n *inf*) l)
                          ((= n *-inf*) -1)
                          (t (truncate n))))
                 (idx (if (< k 0) (+ l k) k)))
            (when (or (< idx 0) (>= idx l)) (return-from done *undefined*))
            (js-get o (princ-to-string idx)))))

      (def-method realm ap "findLast" 1 (this args)
        (block done
          (let* ((o (to-object this)) (fn (arg 0 args)) (ta (arg 1 args))
                 (l (truncate (to-length (js-get o "length")))))
            (callable fn)
            (loop for i from (1- l) downto 0 do
              (let ((v (js-get o (princ-to-string i))))
                (when (js-truthy (js-call fn ta (list v (float i 1d0) o)))
                  (return-from done v))))
            *undefined*)))

      (def-method realm ap "findLastIndex" 1 (this args)
        (block done
          (let* ((o (to-object this)) (fn (arg 0 args)) (ta (arg 1 args))
                 (l (truncate (to-length (js-get o "length")))))
            (callable fn)
            (loop for i from (1- l) downto 0 do
              (let ((v (js-get o (princ-to-string i))))
                (when (js-truthy (js-call fn ta (list v (float i 1d0) o)))
                  (return-from done (float i 1d0)))))
            -1d0))))))

(register-builtin-installer 'install-array-search)
