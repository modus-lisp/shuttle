;;;; builtins/atomics.lisp — the Atomics namespace (single-threaded semantics:
;;;; plain read-modify-write on the backing bytes; wait/notify per the
(in-package #:shuttle)

(defun install-atomics (realm)
  (declare (ignorable realm))
  ;; TODO
  )

(register-builtin-installer 'install-atomics)
