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
   #:shuttle-error #:js-throw
   ;; ES modules, static half: what a bundler asks of a source file
   #:parse-module #:parse-module-items
   #:module-record #:module-items #:module-requests #:module-imports #:module-exports
   #:module-source #:module-spans #:module-starts
   #:span-start #:span-end #:span-from #:span-to
   ;; ES modules, runtime half: link, evaluate, namespaces
   #:eval-module #:make-file-module-host #:set-module-host #:module-host #:source-text-module
   #:namespace-object #:link-module #:evaluate-module #:resolve-export #:*module-host*
   ;; semver (src/semver.lisp, system :shuttle/semver)
   #:semver #:parse-semver #:semver-string #:semver-compare #:semver< #:semver=
   #:semver-major #:semver-minor #:semver-patch #:semver-prerelease #:semver-build
   #:parse-range #:semver-satisfies-p #:semver-max-satisfying
   #:comparator #:comparator-op #:comparator-version
   ;; npm client (src/registry.lisp, src/resolve.lisp; system :shuttle/npm)
   #:*registry* #:*target-node* #:*platform-os* #:*platform-cpu* #:*platform-libc*
   #:resolved-runs-here-p #:registry-error #:registry-error-text #:registry-packument
   #:resolve-version #:resolved #:resolved-name #:resolved-version #:resolved-tarball
   #:resolved-integrity #:resolved-algorithm #:resolved-dependencies
   #:verify-integrity #:fetch-package
   #:resolve-tree #:tree-nodes #:tree-violations #:node-name #:node-resolved #:node-children
   #:node-path #:node-path-string
   #:install-tree #:install-node #:write-lockfile #:read-lockfile #:lock-covers-p
   #:install-locked #:project-dependencies #:save-dependencies #:save-range-for
   #:*entropy-source*
   #:minify-source #:minify-error #:minify-error-text
   #:import-entry #:export-entry
   #:entry-request #:entry-import-name #:entry-local-name #:entry-export-name))
