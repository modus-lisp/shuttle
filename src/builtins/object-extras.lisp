;;;; See array-iteration.lisp for the convention + available helpers.
(in-package #:shuttle)

(defun install-object-extras (realm)
  (declare (ignorable realm))
  ;; TODO: build the global(s) and (define-global realm "Name" obj)
  )

(register-builtin-installer 'install-object-extras)
