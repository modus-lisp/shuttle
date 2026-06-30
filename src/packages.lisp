;;;; packages.lisp — shuttle: a Lisp-native JavaScript engine.
(defpackage #:shuttle
  (:use #:cl)
  (:export
   ;; consumer API (the seam weft builds DOM bindings on)
   #:make-realm #:eval-script #:define-global #:make-host-object
   #:native-function #:invoke #:js-call
   ;; value model + internal methods (host objects override these)
   #:*undefined* #:*null* #:*true* #:*false* #:js-undefined-p
   #:js-object #:make-object #:js-get #:js-set #:js-has #:js-delete
   #:js-own-keys #:js-object-proto
   ;; abstract operations (spec coercions)
   #:to-boolean #:to-number #:to-string #:to-primitive #:js-typeof
   #:js-truthy #:js-equal #:js-strict-equal
   #:shuttle-error #:js-throw))
