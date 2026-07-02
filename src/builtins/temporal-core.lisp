;;;; builtins/temporal-core.lisp — shared Temporal kernel — ISO records/parse/format, rounding engine, options readers, ToTemporalX conversions, Temporal namespace, UTC+fixed-offset zones, iso8601 calendar.
(in-package #:shuttle)

(defun install-temporal-core (realm)
  (declare (ignorable realm))
  ;; TODO(temporal)
  )

(register-builtin-installer 'install-temporal-core)
