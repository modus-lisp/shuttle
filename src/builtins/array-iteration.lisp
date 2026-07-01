;;;; builtins/array-iteration.lisp — Array.prototype iteration/reduction methods.
;;;; forEach/map/toString/values/@@iterator (see realm.lisp install-array);
;;;; this file adds the rest of the callback-driven family.
;;;;
;;;; Convention (copy this file to start a new group):
;;;;   - (in-package #:shuttle)
;;;;   - one (defun install-<group> (realm) ...) that pulls its proto via a
;;;;     realm accessor and adds methods with (def-method realm PROTO name len ...)
;;;;   - end with (register-builtin-installer 'install-<group>)
;;;;   - add the file to shuttle.asd (after realm)
;;;; NOTE: def-method's body is a lambda; dotimes/loop establish their own NIL
;;;; block, so to return FROM THE METHOD use an explicit (block tag ...).
;;;; Helpers available: (arg n args), len below, js-get/js-set/js-has,
;;;;   make-array-object, js-call, js-callable-p, to-int-index, js-truthy,
;;;;   js-strict-equal, same-value-zero, (make-native-error "TypeError" msg).
(in-package #:shuttle)

(defun install-array-iteration (realm)
  (let ((ap (realm-array-proto realm)))
    (flet ((len (this) (to-int-index (js-get this "length")))
           (callable (f) (unless (js-callable-p f)
                           (js-throw (make-native-error "TypeError" "not a function")))))
      (def-method realm ap "filter" 1 (this args)
        (let ((fn (arg 0 args)) (ta (arg 1 args)) (l (len this)) (out '()))
          (callable fn)
          (dotimes (i l)
            (when (js-truthy* (js-has this (princ-to-string i)))
              (let ((v (js-get this (princ-to-string i))))
                (when (js-truthy (js-call fn ta (list v (float i 1d0) this))) (push v out)))))
          (make-array-object (nreverse out))))
      (def-method realm ap "some" 1 (this args)
        (block done
          (let ((fn (arg 0 args)) (ta (arg 1 args)) (l (len this)))
            (callable fn)
            (dotimes (i l)
              (when (js-truthy* (js-has this (princ-to-string i)))
                (when (js-truthy (js-call fn ta (list (js-get this (princ-to-string i)) (float i 1d0) this)))
                  (return-from done *true*))))
            *false*)))
      (def-method realm ap "every" 1 (this args)
        (block done
          (let ((fn (arg 0 args)) (ta (arg 1 args)) (l (len this)))
            (callable fn)
            (dotimes (i l)
              (when (js-truthy* (js-has this (princ-to-string i)))
                (unless (js-truthy (js-call fn ta (list (js-get this (princ-to-string i)) (float i 1d0) this)))
                  (return-from done *false*))))
            *true*)))
      (def-method realm ap "find" 1 (this args)
        (block done
          (let ((fn (arg 0 args)) (ta (arg 1 args)) (l (len this)))
            (callable fn)
            (dotimes (i l)
              (let ((v (js-get this (princ-to-string i))))
                (when (js-truthy (js-call fn ta (list v (float i 1d0) this))) (return-from done v))))
            *undefined*)))
      (def-method realm ap "findIndex" 1 (this args)
        (block done
          (let ((fn (arg 0 args)) (ta (arg 1 args)) (l (len this)))
            (callable fn)
            (dotimes (i l)
              (let ((v (js-get this (princ-to-string i))))
                (when (js-truthy (js-call fn ta (list v (float i 1d0) this))) (return-from done (float i 1d0)))))
            -1d0)))
      (def-method realm ap "reduce" 1 (this args)
        (let ((fn (arg 0 args)) (l (len this)) (acc (arg 1 args)) (has-acc (>= (length args) 2)) (i 0))
          (callable fn)
          (unless has-acc
            (block seed
              (loop while (< i l) do
                (when (js-truthy* (js-has this (princ-to-string i)))
                  (setf acc (js-get this (princ-to-string i)) has-acc t i (1+ i)) (return-from seed))
                (incf i)))
            (unless has-acc (js-throw (make-native-error "TypeError" "Reduce of empty array with no initial value"))))
          (loop while (< i l) do
            (when (js-truthy* (js-has this (princ-to-string i)))
              (setf acc (js-call fn *undefined* (list acc (js-get this (princ-to-string i)) (float i 1d0) this))))
            (incf i))
          acc))
      (def-method realm ap "reduceRight" 1 (this args)
        (let ((fn (arg 0 args)) (l (len this)) (acc (arg 1 args)) (has-acc (>= (length args) 2)) (i (1- (len this))))
          (callable fn)
          (unless has-acc
            (block seed
              (loop while (>= i 0) do
                (when (js-truthy* (js-has this (princ-to-string i)))
                  (setf acc (js-get this (princ-to-string i)) has-acc t i (1- i)) (return-from seed))
                (decf i)))
            (unless has-acc (js-throw (make-native-error "TypeError" "Reduce of empty array with no initial value"))))
          (loop while (>= i 0) do
            (when (js-truthy* (js-has this (princ-to-string i)))
              (setf acc (js-call fn *undefined* (list acc (js-get this (princ-to-string i)) (float i 1d0) this))))
            (decf i))
          acc)))))

(register-builtin-installer 'install-array-iteration)
