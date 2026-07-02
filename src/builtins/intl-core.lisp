;;;; builtins/intl-core.lisp — Intl namespace + BCP-47/UTS35 canonicalizer + ResolveLocale + en data + numbering-system digits + getCanonicalLocales/supportedValuesOf.
(in-package #:shuttle)

(defun install-intl_core (realm)
  (declare (ignorable realm))
  ;; TODO(intl)
  )

(register-builtin-installer 'install-intl_core)
