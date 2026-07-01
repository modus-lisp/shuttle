;;;; See array-iteration.lisp for the convention + helpers.
(in-package #:shuttle)

(defun install-proxy (realm)
  (declare (ignorable realm))
  ;; TODO
  )

(register-builtin-installer 'install-proxy)
