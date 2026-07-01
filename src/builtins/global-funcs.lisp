;;;; See array-iteration.lisp for the convention + helpers.
(in-package #:shuttle)

(defun install-global-funcs (realm)
  (declare (ignorable realm))
  ;; TODO
  )

(register-builtin-installer 'install-global-funcs)
