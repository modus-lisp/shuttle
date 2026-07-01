;;;; builtins/annexb-string.lisp — Annex B String.prototype HTML methods
;;;; (anchor/big/blink/bold/fixed/fontcolor/fontsize/italics/link/small/strike/
(in-package #:shuttle)

(defun install-annexb-string (realm)
  (declare (ignorable realm))
  ;; TODO: add the 13 HTML wrapper methods to (realm-string-proto realm)
  )

(register-builtin-installer 'install-annexb-string)
