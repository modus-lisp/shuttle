;;;; shuttle.asd — a Lisp-native JavaScript engine.
(asdf:defsystem :shuttle
  :description "A Lisp-native JavaScript engine, clean-room (no FFI): source ->
bytecode -> stack VM, with objects built on dispatchable internal methods (the
host-binding seam a consumer like weft hangs DOM objects + reflow on). Oracle: test262."
  :version "0.0.1" :author "ynniv" :license "MIT"
  :depends-on ()
  :serial t
  :components ((:module "src" :serial t
                :components ((:file "packages") (:file "value") (:file "lex")
                             (:file "parse") (:file "module") (:file "compile") (:file "vm")
                             (:file "realm")
                             (:file "module-runtime")
                             (:file "unicode-props")
                             (:file "regex")
                             ;; built-in method groups (one file per group)
                             (:module "builtins" :serial t
                              :components ((:file "array-iteration")
                                           (:file "array-mutators")
                                           (:file "array-search")
                                           (:file "array-transform")
                                           (:file "array-immutable")
                                           (:file "json")
                                           (:file "math-extra")
                                           (:file "number-methods")
                                           (:file "string-methods")
                                           (:file "map-set")
                                           (:file "weak")
                                           (:file "object-extras")
                                           (:file "date")
                                           (:file "regexp")
                                           (:file "string-regex")
                                           (:file "iterator")
                                           (:file "arraybuffer")
                                           (:file "typedarray")
                                           (:file "dataview")
                                           (:file "proxy")
                                           (:file "global-funcs")
                                           (:file "error-extra")
                                           (:file "bigint")
                                           (:file "annexb-string")
                                           (:file "disposable")
                                           (:file "function-extra")
                                           (:file "sharedarraybuffer")
                                           (:file "atomics")
                                           (:file "temporal-core")
                                           (:file "temporal-instant")
                                           (:file "temporal-plaintime")
                                           (:file "temporal-duration")
                                           (:file "temporal-plaindate")
                                           (:file "temporal-plainyearmonth")
                                           (:file "temporal-plainmonthday")
                                           (:file "temporal-plaindatetime")
                                           (:file "temporal-zoneddatetime")
                                           (:file "temporal-now")
                                           (:file "intl-core")
                                           (:file "intl-locale")
                                           (:file "intl-numberformat")
                                           (:file "intl-datetimeformat")
                                           (:file "intl-plural-list-relative")
                                           (:file "intl-collator-segmenter-displaynames")))))))

;;; The bundler is a separate system: the engine has no business depending on a file resolver,
;;; and a consumer embedding shuttle for scripting should not get one.
(asdf:defsystem :shuttle/bundle
  :description "One script out of an ES module graph: resolve, order, splice. Replaces esbuild in
the deploy path, using shuttle's own parser for the modules and its own JSON for package.json."
  :version "0.0.1" :author "ynniv" :license "MIT"
  :depends-on (:shuttle)
  :components ((:module "src" :components ((:file "bundle")))))
