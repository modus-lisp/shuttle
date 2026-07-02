;;;; builtins/disposable.lisp — DisposableStack (+ Symbol.dispose well-known).
;;;; The explicit-resource-management built-in (the object API; the `using`
(in-package #:shuttle)

(defun install-disposable (realm)
  (declare (ignorable realm))
  ;; TODO: Symbol.dispose well-known + DisposableStack ctor/prototype
  ;; (use/dispose/adopt/defer/move, disposed getter, @@dispose, @@toStringTag)
  )

(register-builtin-installer 'install-disposable)
