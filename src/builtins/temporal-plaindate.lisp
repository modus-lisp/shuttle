;;;; builtins/temporal-plaindate.lisp — Temporal.PlainDate + shared ISO date arithmetic.
(in-package #:shuttle)

(defun install-temporal-plaindate (realm)
  (declare (ignorable realm))
  ;; TODO(temporal)
  )

(register-builtin-installer 'install-temporal-plaindate)
