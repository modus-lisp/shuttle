;;;; builtins/temporal-now.lisp — Temporal.Now.
(in-package #:shuttle)

(defun install-temporal-now (realm)
  (declare (ignorable realm))
  ;; TODO(temporal)
  )

(register-builtin-installer 'install-temporal-now)
