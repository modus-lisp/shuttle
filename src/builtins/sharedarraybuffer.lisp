;;;; builtins/sharedarraybuffer.lisp — SharedArrayBuffer (single-threaded impl:
;;;; same byte-vector representation as ArrayBuffer; cannot be detached;
(in-package #:shuttle)

(defun install-sharedarraybuffer (realm)
  (declare (ignorable realm))
  ;; TODO
  )

(register-builtin-installer 'install-sharedarraybuffer)
