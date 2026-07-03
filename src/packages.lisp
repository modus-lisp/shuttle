;;;; packages.lisp — shuttle: a Lisp-native JavaScript engine.
(defpackage #:shuttle
  (:use #:cl)
  (:export
   ;; consumer API (the seam weft builds DOM bindings on)
   #:make-realm #:eval-script #:define-global #:make-host-object
   #:native-function #:invoke #:js-call #:drain-microtasks
   ;; value model + internal methods (host objects override these)
   #:*undefined* #:*null* #:*true* #:*false* #:js-undefined-p
   #:js-object #:js-object-p #:make-object #:js-get #:js-set #:js-has #:js-delete
   #:js-own-keys #:js-object-proto #:js-callable-p #:js-construct #:make-native-error
   ;; abstract operations (spec coercions)
   #:to-boolean #:to-number #:to-string #:to-primitive #:js-typeof
   #:js-truthy #:js-equal #:js-strict-equal
   #:to-object #:to-length #:to-integer-or-infinity #:require-object-coercible
   #:to-property-key #:same-value #:same-value-zero
   #:js-define-own-property #:js-get-own-property #:put #:put-accessor
   #:js-symbol #:make-js-symbol #:js-symbol-p #:js-symbol-desc
   #:shuttle-error #:js-throw))
