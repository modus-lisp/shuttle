;;;; See array-iteration.lisp for the convention + available helpers.
;;;; Fill the (install-array-search realm) body; do not touch other files.
(in-package #:shuttle)

(defun install-array-search (realm)
  (let ((ap (realm-array-proto realm)))
    (flet ((len (this) (to-int-index (js-get this "length")))
           (callable (f) (unless (js-callable-p f)
                           (js-throw (make-native-error "TypeError" "not a function")))))
      (declare (ignorable #'len #'callable))

      (def-method realm ap "lastIndexOf" 1 (this args)
        (block done
          (let* ((target (arg 0 args))
                 (l (truncate (to-length (js-get this "length")))))
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
                (when (js-truthy* (js-has this (princ-to-string i)))
                  (when (js-strict-equal (js-get this (princ-to-string i)) target)
                    (return-from done (float i 1d0)))))
              -1d0))))

      (def-method realm ap "includes" 1 (this args)
        (block done
          (let* ((target (arg 0 args))
                 (l (truncate (to-length (js-get this "length")))))
            (when (= l 0) (return-from done *false*))
            (let ((from (let ((n (to-integer-or-infinity (arg 1 args))))
                          (cond ((= n *inf*) (return-from done *false*))
                                ((= n *-inf*) 0)
                                (t (let ((k (truncate n)))
                                     (cond ((< k 0) (max 0 (+ l k)))
                                           (t k))))))))
              (loop for i from from below l do
                ;; does NOT skip holes — read via js-get (missing => undefined)
                (when (same-value-zero (js-get this (princ-to-string i)) target)
                  (return-from done *true*)))
              *false*))))

      (def-method realm ap "at" 1 (this args)
        (block done
          (let* ((l (truncate (to-length (js-get this "length"))))
                 (n (to-integer-or-infinity (arg 0 args)))
                 (k (cond ((= n *inf*) l)
                          ((= n *-inf*) -1)
                          (t (truncate n))))
                 (idx (if (< k 0) (+ l k) k)))
            (when (or (< idx 0) (>= idx l)) (return-from done *undefined*))
            (js-get this (princ-to-string idx)))))

      (def-method realm ap "findLast" 1 (this args)
        (block done
          (let ((fn (arg 0 args)) (ta (arg 1 args))
                (l (truncate (to-length (js-get this "length")))))
            (callable fn)
            (loop for i from (1- l) downto 0 do
              (let ((v (js-get this (princ-to-string i))))
                (when (js-truthy (js-call fn ta (list v (float i 1d0) this)))
                  (return-from done v))))
            *undefined*)))

      (def-method realm ap "findLastIndex" 1 (this args)
        (block done
          (let ((fn (arg 0 args)) (ta (arg 1 args))
                (l (truncate (to-length (js-get this "length")))))
            (callable fn)
            (loop for i from (1- l) downto 0 do
              (let ((v (js-get this (princ-to-string i))))
                (when (js-truthy (js-call fn ta (list v (float i 1d0) this)))
                  (return-from done (float i 1d0)))))
            -1d0))))))

(register-builtin-installer 'install-array-search)
