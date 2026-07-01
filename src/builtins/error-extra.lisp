;;;; builtins/error-extra.lisp — AggregateError + Error extras (cause, isError,
(in-package #:shuttle)

(defun install-error-extra (realm)
  (declare (ignorable realm))
  ;; TODO: AggregateError ctor+proto, Error cause option, Error.isError
  )

(register-builtin-installer 'install-error-extra)
