;;;; builtins/object-extras.lisp — Object statics/proto remainder (fromEntries, hasOwn, getOwnPropertyDescriptors, __proto__ accessor, groupBy).
;;;; See array-iteration.lisp for the convention + available helpers.
(in-package #:shuttle)

;;; IteratorClose on an abrupt (thrown) completion: call it.return() (ignoring
;;; its own errors) and then re-signal the original throw.
(defun object-extras-iterator-close-throw (it condition)
  "Close IT because CONDITION was thrown mid-iteration, then re-signal CONDITION."
  (let ((ret (ignore-errors (js-get it "return"))))
    (when (js-callable-p ret)
      (ignore-errors (js-call ret it '()))))
  (error condition))

(defun object-extras-set-prototype-of (o proto)
  "SetPrototypeOf(O, V): returns T on success, NIL on rejection. For a proxy/host
   object (has a :set-proto internal trap) route through js-set-proto so the trap
   fires; otherwise OrdinarySetPrototypeOf (same-value short-circuit, non-
   extensibility, cycle detection)."
  (when (and (js-object-internal o) (getf (js-object-internal o) :set-proto))
    (return-from object-extras-set-prototype-of (js-truthy* (js-set-proto o proto))))
  (let ((current (js-object-proto o)))
    ;; SameValue(V, current) -> success (no change).
    (when (same-value proto (if (js-object-p current) current *null*))
      (return-from object-extras-set-prototype-of t))
    ;; If not extensible, reject.
    (unless (js-object-extensible o)
      (return-from object-extras-set-prototype-of nil))
    ;; Cycle detection: walk proto chain from V; reject if we reach O.
    (let ((p proto))
      (loop
        (cond ((eq p *null*) (return))
              ((not (js-object-p p)) (return))
              ((eq p o) (return-from object-extras-set-prototype-of nil))
              (t (setf p (js-object-proto p))))))
    (setf (js-object-proto o) (if (eq proto *null*) *null* proto))
    t))

(defun install-object-extras (realm)
  (let ((octor (js-get (realm-global realm) "Object"))
        (op (realm-object-proto realm)))
    (when (js-object-p octor)

      ;; ----- Object.setPrototypeOf(O, proto) [OVERRIDE] -------------------
      ;; The kernel static sets the prototype unconditionally, which lets it
      ;; create cycles (→ later chain-walks hang) and ignores non-extensible
      ;; objects. Redefine with the full OrdinarySetPrototypeOf semantics and
      ;; throw TypeError when [[SetPrototypeOf]] would return false.
      (def-method realm octor "setPrototypeOf" 2 (this args)
        (let ((o (arg 0 args)) (proto (arg 1 args)))
          (require-object-coercible o "Object.setPrototypeOf")
          (unless (or (js-object-p proto) (eq proto *null*))
            (js-throw (make-native-error "TypeError" "Object prototype may only be an Object or null")))
          (when (js-object-p o)
            (unless (object-extras-set-prototype-of o proto)
              (js-throw (make-native-error "TypeError"
                          "Object.setPrototypeOf: cyclic prototype value or non-extensible object"))))
          o))

      ;; ----- Object.assign(target, ...sources) [OVERRIDE] ----------------
      ;; The kernel static uses js-set and drops failures silently. Spec calls
      ;; Set(to, key, value, true): a false result (non-writable target prop,
      ;; non-extensible target, accessor without setter) must throw TypeError.
      ;; Reading each source key value can trigger a getter, so re-check the
      ;; own descriptor's enumerability against the CURRENT source (it may have
      ;; changed), matching the spec's per-key CopyDataProperties loop.
      (def-method realm octor "assign" 2 (this args)
        (let ((target (to-object (arg 0 args))))
          (dolist (src (rest args))
            (unless (js-null-or-undef src)
              (let ((so (to-object src)))
                (dolist (k (js-own-keys so))
                  (let ((d (js-get-own-property so k)))
                    (when (and d (prop-enumerable d))
                      (let ((val (js-get so k)))
                        (let ((ok (js-set target k val target)))
                          (when (or (null ok) (eq ok *false*))
                            (js-throw (make-native-error "TypeError"
                                        "Object.assign: cannot assign to target property")))))))))))
          target))

      ;; ----- Object.fromEntries(iterable) ---------------------------------
      ;; AddEntriesFromIterable using CreateDataPropertyOnObject (define, not set).
      ;; Reads entry."0"/entry."1" as properties; closes the iterator on abrupt.
      (def-method realm octor "fromEntries" 1 (this args)
        (let ((iterable (arg 0 args)))
          (require-object-coercible iterable "Object.fromEntries argument")
          (let ((obj (make-object :proto op))
                (it (get-iterator iterable)))
            (block done
              (loop
                (let ((r (iterator-step it)))
                  (when (js-truthy (js-get r "done")) (return-from done obj))
                  (let ((entry (js-get r "value")))
                    (unless (js-object-p entry)
                      (object-extras-iterator-close-throw
                       it (make-condition 'shuttle-error
                                          :value (make-native-error "TypeError"
                                                   "iterator value is not an entry object"))))
                    (handler-case
                        (let ((k (js-get entry "0"))
                              (v (js-get entry "1")))
                          (put obj (to-property-key k) v))
                      (shuttle-error (c) (object-extras-iterator-close-throw it c))))))))))

      ;; ----- Object.hasOwn(o, key) ----------------------------------------
      (def-method realm octor "hasOwn" 2 (this args)
        (let ((o (to-object (arg 0 args)))
              (key (to-property-key (arg 1 args))))
          (js-bool (and (js-get-own-property o key) t))))

      ;; ----- Object.getOwnPropertyDescriptors(o) --------------------------
      (def-method realm octor "getOwnPropertyDescriptors" 1 (this args)
        (let* ((o (to-object (arg 0 args)))
               (result (make-object :proto op)))
          (dolist (k (js-own-keys o))
            (let ((d (js-get-own-property o k)))
              (when d
                (put result k (from-property-descriptor realm d)))))
          result))

      ;; ----- Object.groupBy(items, callbackfn) ----------------------------
      ;; Groups items by ToPropertyKey(cb(value, index)) into a null-proto
      ;; object whose values are arrays.
      (def-method realm octor "groupBy" 2 (this args)
        (let ((items (arg 0 args)) (cb (arg 1 args)))
          (require-object-coercible items "Object.groupBy argument")
          (unless (js-callable-p cb)
            (js-throw (make-native-error "TypeError" "Object.groupBy callback is not callable")))
          (let ((groups (make-object :proto *null*))
                (it (get-iterator items))
                (k 0))
            (block done
              (loop
                (let ((r (iterator-step it)))
                  (when (js-truthy (js-get r "done")) (return-from done groups))
                  (when (>= k 9007199254740991)
                    (object-extras-iterator-close-throw
                     it (make-condition 'shuttle-error
                                        :value (make-native-error "TypeError" "too many elements"))))
                  (let ((value (js-get r "value")))
                    (handler-case
                        (let ((key (to-property-key
                                    (js-call cb *undefined* (list value (float k 1d0))))))
                          (let ((existing (js-get-own-property groups key)))
                            (if existing
                                (let* ((arr (prop-value existing))
                                       (len (to-int-index (js-get arr "length"))))
                                  (put arr (princ-to-string len) value)
                                  (put arr "length" (float (1+ len) 1d0) :enumerable nil))
                                (put groups key (make-array-object (list value))))))
                      (shuttle-error (c) (object-extras-iterator-close-throw it c))))
                  (incf k)))))))

      ;; ----- Object.prototype.hasOwnProperty(V) [OVERRIDE] ---------------
      ;; Spec order: ToPropertyKey(V) BEFORE ToObject(this) (B.2.2 / 20.1.3.2).
      ;; The kernel evaluates ToObject first, so a non-coercible `this` masks a
      ;; throwing key coercion. Redefine to coerce the key first.
      (def-method realm op "hasOwnProperty" 1 (this args)
        (let ((key (to-property-key (arg 0 args))))
          (js-bool (and (js-get-own-property (to-object this) key) t))))

      ;; ----- Object.prototype.__define[GS]etter__ / __lookup[GS]etter__ ----
      ;; Annex B B.2.2.2–B.2.2.5. Order matters: ToObject(this) first (so a
      ;; non-coercible receiver throws before the key is coerced), then the
      ;; callable check, then ToPropertyKey, then DefinePropertyOrThrow.
      (def-method realm op "__defineGetter__" 2 (this args)
        (let ((o (to-object this)) (getter (arg 1 args)))
          (unless (js-callable-p getter)
            (js-throw (make-native-error "TypeError" "Object.prototype.__defineGetter__: getter must be callable")))
          (let ((key (to-property-key (arg 0 args))))
            (unless (js-define-own-property o key
                       (list :accessor t :get getter :enumerable t :configurable t))
              (js-throw (make-native-error "TypeError" "Cannot define getter")))
            *undefined*)))
      (def-method realm op "__defineSetter__" 2 (this args)
        (let ((o (to-object this)) (setter (arg 1 args)))
          (unless (js-callable-p setter)
            (js-throw (make-native-error "TypeError" "Object.prototype.__defineSetter__: setter must be callable")))
          (let ((key (to-property-key (arg 0 args))))
            (unless (js-define-own-property o key
                       (list :accessor t :set setter :enumerable t :configurable t))
              (js-throw (make-native-error "TypeError" "Cannot define setter")))
            *undefined*)))
      (def-method realm op "__lookupGetter__" 1 (this args)
        (let ((o (to-object this)) (key (to-property-key (arg 0 args))))
          (loop
            (let ((d (js-get-own-property o key)))
              (when d
                (return-from nil
                  (if (prop-accessor d) (or (prop-get d) *undefined*) *undefined*))))
            (let ((p (js-object-proto o)))
              (if (js-object-p p) (setf o p) (return-from nil *undefined*))))))
      (def-method realm op "__lookupSetter__" 1 (this args)
        (let ((o (to-object this)) (key (to-property-key (arg 0 args))))
          (loop
            (let ((d (js-get-own-property o key)))
              (when d
                (return-from nil
                  (if (prop-accessor d) (or (prop-set d) *undefined*) *undefined*))))
            (let ((p (js-object-proto o)))
              (if (js-object-p p) (setf o p) (return-from nil *undefined*))))))

      ;; ----- Object.prototype.__proto__ accessor (Annex B) ----------------
      ;; get: RequireObjectCoercible -> ToObject -> [[GetPrototypeOf]].
      ;; set: RequireObjectCoercible; if proto not Object/Null -> no-op (undefined);
      ;;      else ordinary [[SetPrototypeOf]] (cycle + extensibility checks),
      ;;      throwing TypeError on failure.
      (put-accessor op "__proto__"
        :get (native-function realm "get __proto__"
               (lambda (this args) (declare (ignore args))
                 (let ((o (to-object (require-object-coercible this "Object.prototype.__proto__"))))
                   (let ((p (js-object-proto o)))
                     (if (js-object-p p) p *null*))))
               0)
        :set (native-function realm "set __proto__"
               (lambda (this args)
                 (require-object-coercible this "Object.prototype.__proto__")
                 (let ((proto (arg 0 args)))
                   (when (or (js-object-p proto) (eq proto *null*))
                     (when (js-object-p this)
                       (unless (object-extras-set-prototype-of this proto)
                         (js-throw (make-native-error "TypeError"
                                    "cyclic __proto__ value or non-extensible object")))))
                   *undefined*))
               1)
        :enumerable nil :configurable t))))

(register-builtin-installer 'install-object-extras)
