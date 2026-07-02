;;;; builtins/function-extra.lisp — Function.prototype / Function ctor edge cases
;;;; (bind/call/apply/toString/name/length + @@hasInstance). Overrides the kernel
;;;; install-function-proto where needed (installers run after the kernel).
(in-package #:shuttle)

(defun install-function-extra (realm)
  (declare (ignorable realm))
  ;; TODO
  )

(register-builtin-installer 'install-function-extra)
