;;;; builtins/temporal-instant.lisp — Temporal.Instant (epochNanoseconds bigint).
(in-package #:shuttle)

(defun install-temporal-instant (realm)
  (declare (ignorable realm))
  ;; TODO(temporal)
  )

(register-builtin-installer 'install-temporal-instant)
