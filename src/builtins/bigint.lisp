;;;; builtins/bigint.lisp — the BigInt global (constructor + BigInt.prototype +
;;;; asIntN/asUintN). The bigint VALUE type is a CL integer (Numbers are always
;;;; double-float, so an integer is an unambiguous bigint); typeof/operators/
;;;; coercions live in the core files. Owned by the BigInt agent.
(in-package #:shuttle)

(defun install-bigint (realm)
  (declare (ignorable realm))
  ;; TODO(bigint): BigInt(x) ctor (not newable), asIntN/asUintN,
  ;; BigInt.prototype toString/valueOf/toLocaleString/@@toStringTag.
  )

(register-builtin-installer 'install-bigint)
