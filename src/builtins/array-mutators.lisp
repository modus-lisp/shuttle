;;;; See array-iteration.lisp for the convention + available helpers.
;;;; Fill the (install-array-mutators realm) body; do not touch other files.
(in-package #:shuttle)

(defun js-set! (o key v)
  "Set(O, key, V, Throw=true): throw a TypeError if the [[Set]] returns false."
  (unless (js-truthy* (js-set o key v))
    (js-throw (make-native-error "TypeError"
                                 (format nil "Cannot assign to read only property '~a'"
                                         (if (stringp key) key (to-string key))))))
  v)

(defun js-delete! (o key)
  "DeletePropertyOrThrow: throw a TypeError if [[Delete]] returns false."
  (unless (js-truthy* (js-delete o key))
    (js-throw (make-native-error "TypeError"
                                 (format nil "Cannot delete property '~a'"
                                         (if (stringp key) key (to-string key))))))
  *true*)

(defun install-array-mutators (realm)
  (let ((ap (realm-array-proto realm)))
    (declare (ignorable ap))
    (flet ((len (this) (truncate (to-length (js-get this "length"))))
           ;; Map a ToIntegerOrInfinity double REL to a clamped CL index in
           ;; [0,l]: -Inf->0, +Inf->l, negative -> max(l+rel,0), else min(rel,l).
           (rel-clamp (rel l)
             (cond ((= rel *-inf*) 0)
                   ((= rel *inf*) l)
                   ((< rel 0) (max (+ l (truncate rel)) 0))
                   (t (min (truncate rel) l)))))
      (macrolet ((k (i) `(princ-to-string ,i)))

        ;; ------------------------------------------------------------------
        ;; Kernel overrides (ToObject/ToLength + strict Set/Delete so array-like
        ;; receivers, huge lengths and frozen targets behave per spec):
        ;; push/pop/join/toString.  Plus shift/unshift/reverse/splice/fill/
        ;; copyWithin/sort.
        ;; ------------------------------------------------------------------

        (def-method realm ap "push" 1 (this args)
          (let* ((o (to-object this))
                 (l (len o))
                 (argc (length args)))
            (when (> (+ l argc) 9007199254740991)
              (js-throw (make-native-error "TypeError" "push exceeds maximum array length")))
            (dolist (a args) (js-set! o (k l) a) (incf l))
            (js-set! o "length" (float l 1d0))
            (float l 1d0)))

        (def-method realm ap "pop" 0 (this args)
          (declare (ignore args))
          (let* ((o (to-object this))
                 (l (len o)))
            (if (zerop l)
                (progn (js-set! o "length" 0d0) *undefined*)
                (let* ((idx (1- l)) (v (js-get o (k idx))))
                  (js-delete! o (k idx))
                  (js-set! o "length" (float idx 1d0))
                  v))))

        (def-method realm ap "join" 1 (this args)
          (let* ((o (to-object this))
                 (l (len o))
                 (sep (if (js-undefined-p (arg 0 args)) "," (to-string (arg 0 args)))))
            (with-output-to-string (s)
              (dotimes (i l)
                (when (plusp i) (write-string sep s))
                (let ((v (js-get o (k i))))
                  (unless (js-null-or-undef v) (write-string (to-string v) s)))))))

        (let ((%obj-to-string (js-get (realm-object-proto realm) "toString")))
          (def-method realm ap "toString" 0 (this args)
            (declare (ignore args))
            (let* ((o (to-object this))
                   (fn (js-get o "join")))
              (if (js-callable-p fn)
                  (js-call fn o '())
                  ;; step 3: intrinsic %Object.prototype.toString% (captured, so a
                  ;; later `delete Object.prototype.toString` doesn't affect us).
                  (js-call %obj-to-string o '())))))

        ;; reverse — in place, returns the array.
        (def-method realm ap "reverse" 0 (this args)
          (let* ((this (to-object this))
                 (l (len this))
                 (mid (floor l 2)))
            (dotimes (lower mid)
              ;; Spec order: HasProperty(lower), Get(lower), HasProperty(upper),
              ;; Get(upper) — accessors may mutate the array between steps.
              (let* ((upper (- (- l lower) 1))
                     (lk (k lower)) (uk (k upper))
                     (lex (js-truthy* (js-has this lk)))
                     (lv (and lex (js-get this lk)))
                     (uex (js-truthy* (js-has this uk)))
                     (uv (and uex (js-get this uk))))
                (cond
                  ((and lex uex) (js-set! this lk uv) (js-set! this uk lv))
                  ((and (not lex) uex) (js-set! this lk uv) (js-delete! this uk))
                  ((and lex (not uex)) (js-delete! this lk) (js-set! this uk lv))
                  (t nil))))
            this))

        ;; shift — remove & return first element, shift tail down.
        (def-method realm ap "shift" 0 (this args)
          (block done
            (let* ((this (to-object this))
                   (l (len this)))
              (when (zerop l)
                (js-set! this "length" 0d0)
                (return-from done *undefined*))
              (let ((first (js-get this "0")))
                (loop for i from 1 below l do
                  (let ((from (k i)) (to (k (1- i))))
                    (if (js-truthy* (js-has this from))
                        (js-set! this to (js-get this from))
                        (js-delete! this to))))
                (js-delete! this (k (1- l)))
                (js-set! this "length" (float (1- l) 1d0))
                first))))

        ;; unshift — prepend items, shifting existing elements up.
        (def-method realm ap "unshift" 1 (this args)
          (let* ((this (to-object this))
                 (l (len this))
                 (argc (length args)))
            (when (> (+ l argc) 9007199254740991)
              (js-throw (make-native-error "TypeError" "unshift exceeds maximum array length")))
            (when (> argc 0)
              (loop for i from (1- l) downto 0 do
                (let ((from (k i)) (to (k (+ i argc))))
                  (if (js-truthy* (js-has this from))
                      (js-set! this to (js-get this from))
                      (js-delete! this to))))
              (loop for j from 0 below argc do
                (js-set! this (k j) (arg j args))))
            (let ((newlen (float (+ l argc) 1d0)))
              (js-set! this "length" newlen)
              newlen)))

        ;; splice(start, deleteCount, ...items)
        (def-method realm ap "splice" 2 (this args)
          (let* ((this (to-object this))
                 (l (len this))
                 (argc (length args))
                 (start (rel-clamp (to-integer-or-infinity (arg 0 args)) l))
                 (del-count
                   (cond ((= argc 0) 0)
                         ((= argc 1) (- l start))
                         (t (let ((dc (to-integer-or-infinity (arg 1 args))))
                              (min (max (cond ((= dc *inf*) (- l start))
                                              ((= dc *-inf*) 0)
                                              (t (truncate dc)))
                                        0)
                                   (- l start))))))
                 (items (if (> argc 2) (nthcdr 2 args) '()))
                 (item-count (length items))
                 (removed '()))
            ;; new length must not exceed 2^53-1
            (when (> (+ (- l del-count) item-count) 9007199254740991)
              (js-throw (make-native-error "TypeError" "splice exceeds maximum array length")))
            ;; collect removed
            (dotimes (i del-count)
              (let ((from (k (+ start i))))
                (when (js-truthy* (js-has this from))
                  (push (cons i (js-get this from)) removed))))
            ;; build removed array (ArrayCreate throws if del-count>2^32-1)
            (when (> del-count 4294967295)
              (js-throw (make-native-error "RangeError" "Invalid array length")))
            (let ((rem-arr (make-array-object '())))
              (dolist (cell (nreverse removed))
                (js-set rem-arr (k (car cell)) (cdr cell)))
              (js-set rem-arr "length" (float del-count 1d0))
              ;; shift tail
              (cond
                ((< item-count del-count)
                 (loop for i from start below (- l del-count) do
                   (let ((from (k (+ i del-count))) (to (k (+ i item-count))))
                     (if (js-truthy* (js-has this from))
                         (js-set! this to (js-get this from))
                         (js-delete! this to))))
                 (loop for i from l above (+ (- l del-count) item-count) do
                   (js-delete! this (k (1- i)))))
                ((> item-count del-count)
                 (loop for i from (- l del-count) above start do
                   (let ((from (k (+ (1- i) del-count))) (to (k (+ (1- i) item-count))))
                     (if (js-truthy* (js-has this from))
                         (js-set! this to (js-get this from))
                         (js-delete! this to))))))
              ;; write items
              (loop for it in items for i from start do
                (js-set! this (k i) it))
              (js-set! this "length" (float (+ (- l del-count) item-count) 1d0))
              rem-arr)))

        ;; fill(value, start, end)
        (def-method realm ap "fill" 1 (this args)
          (let* ((this (to-object this))
                 (l (len this))
                 (value (arg 0 args))
                 (start (rel-clamp (to-integer-or-infinity (arg 1 args)) l))
                 (end-arg (arg 2 args))
                 (end (if (js-undefined-p end-arg) l
                          (rel-clamp (to-integer-or-infinity end-arg) l))))
            (loop for i from start below end do
              (js-set! this (k i) value))
            this))

        ;; copyWithin(target, start, end)
        (def-method realm ap "copyWithin" 2 (this args)
          (let* ((this (to-object this))
                 (l (len this))
                 (to (rel-clamp (to-integer-or-infinity (arg 0 args)) l))
                 (from (rel-clamp (to-integer-or-infinity (arg 1 args)) l))
                 (end-arg (arg 2 args))
                 (final (if (js-undefined-p end-arg) l
                            (rel-clamp (to-integer-or-infinity end-arg) l)))
                 (count (min (- final from) (- l to)))
                 (dir 1))
            (when (and (< from to) (< to (+ from count)))
              (setf dir -1
                    from (+ from count -1)
                    to (+ to count -1)))
            (loop while (> count 0) do
              (let ((fk (k from)) (tk (k to)))
                (if (js-truthy* (js-has this fk))
                    (js-set! this tk (js-get this fk))
                    (js-delete! this tk)))
              (incf from dir)
              (incf to dir)
              (decf count))
            this))

        ;; sort(comparefn)
        (def-method realm ap "sort" 1 (this args)
          (let ((cmp (arg 0 args)))
            (unless (or (js-undefined-p cmp) (js-callable-p cmp))
              (js-throw (make-native-error "TypeError" "comparefn must be a function or undefined")))
            (let* ((this (to-object this))
                   (l (len this))
                   ;; Collect present values; count holes and undefineds.
                   (present '())
                   (undef-count 0)
                   (hole-count 0))
              (dotimes (i l)
                (let ((kk (k i)))
                  (if (js-truthy* (js-has this kk))
                      (let ((v (js-get this kk)))
                        (if (js-undefined-p v)
                            (incf undef-count)
                            (push v present)))
                      (incf hole-count))))
              (setf present (nreverse present))
              ;; sortCompare
              (flet ((scmp (a b)
                       (cond
                         ((js-undefined-p a) (if (js-undefined-p b) 0 1))
                         ((js-undefined-p b) -1)
                         ((not (js-undefined-p cmp))
                          (let* ((r (js-call cmp *undefined* (list a b)))
                                 (n (to-number r)))
                            (cond ((js-nan-p n) 0)
                                  ((< n 0) -1)
                                  ((> n 0) 1)
                                  (t 0))))
                         (t (let ((sa (to-string a)) (sb (to-string b)))
                              (cond ((string< sa sb) -1)
                                    ((string> sa sb) 1)
                                    (t 0)))))))
                ;; stable merge sort
                (let ((sorted (stable-sort (copy-list present)
                                           (lambda (a b) (< (scmp a b) 0)))))
                  ;; write back: sorted values, then undefineds, then delete holes
                  (let ((i 0))
                    (dolist (v sorted) (js-set this (k i) v) (incf i))
                    (dotimes (j undef-count) (js-set this (k i) *undefined*) (incf i))
                    (dotimes (j hole-count) (js-delete this (k i)) (incf i))))))
            this))
        ))))

(register-builtin-installer 'install-array-mutators)
