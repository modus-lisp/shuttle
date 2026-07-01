;;;; See array-iteration.lisp for the convention + available helpers.
;;;;
;;;; WeakMap/WeakSet are Map/Set minus size/iteration/forEach/clear, plus a
;;;; "can be held weakly" restriction on keys/values: only objects and
;;;; non-registered symbols. (GC weakness is not observable by test262, so the
;;;; backing store is an ordinary strong hash-table keyed by object/symbol
;;;; identity via EQ.)
(in-package #:shuttle)

;;; ---- helpers ---------------------------------------------------------------

(defun weak-registered-symbol-p (realm sym)
  "True if SYM is a registered symbol (created via Symbol.for) — those cannot be
   held weakly per CanBeHeldWeakly."
  (block found
    (maphash (lambda (k v) (declare (ignore k)) (when (eq v sym) (return-from found t)))
             (realm-symbol-registry realm))
    nil))

(defun can-be-held-weakly (realm v)
  "CanBeHeldWeakly(v): objects, and symbols not in the GlobalSymbolRegistry."
  (or (js-object-p v)
      (and (js-symbol-p v) (not (weak-registered-symbol-p realm v)))))

(defun weak-data (o slot)
  "Return the CL hash-table backing WeakMap/WeakSet instance O under SLOT, or NIL
   if O has no such internal slot. SLOT is :weakmap-data or :weakset-data."
  (and (js-object-p o) (js-object-internal o) (getf (js-object-internal o) slot)))

(defun require-weak-data (o slot who)
  "Coerce O to its weak backing table, or throw a TypeError (this-not-object /
   missing internal slot)."
  (or (weak-data o slot)
      (js-throw (make-native-error "TypeError"
                                   (format nil "~a called on incompatible receiver" who)))))

(defun weak-proto-from-newtarget (realm nt default-proto)
  "GetPrototypeFromConstructor(nt, defaultProto) — same-realm best effort."
  (declare (ignore realm))
  (let ((p (and (js-object-p nt) (js-get nt "prototype"))))
    (if (js-object-p p) p default-proto)))

(defun weak-add-entries-from-iterable (iterable adder target pair)
  "AddEntriesFromIterable(target, iterable, adder). If PAIR, each item is a
   [key,value] entry (WeakMap); otherwise the item itself is the value (WeakSet).
   Closes the iterator on any abrupt completion."
  (let ((it (get-iterator iterable)))
    (flet ((close-and-resignal (c)
             ;; IteratorClose on abrupt completion: call it.return(); the
             ;; original condition wins (swallow any error from return()).
             (ignore-errors
              (let ((ret (js-get it "return")))
                (when (js-callable-p ret) (js-call ret it '()))))
             (error c)))
      (handler-bind ((shuttle-error #'close-and-resignal))
        (loop
          (let ((r (iterator-step it)))
            (when (js-truthy (js-get r "done")) (return))
            (let ((item (js-get r "value")))
              (if pair
                  (progn
                    (unless (js-object-p item)
                      (js-throw (make-native-error "TypeError" "Iterator value is not an entry object")))
                    (let ((k (js-get item "0")) (v (js-get item "1")))
                      (js-call adder target (list k v))))
                  (js-call adder target (list item))))))))))

;;; ---- installer -------------------------------------------------------------

(defun install-weak (realm)
  (let ((op (realm-object-proto realm))
        (tostag (symbol-tostringtag realm)))
    ;; =======================================================================
    ;; WeakMap
    ;; =======================================================================
    (let* ((wmp (make-object :proto op :class "WeakMap"))
           (wmctor (native-function realm "WeakMap"
                     (lambda (this args) (declare (ignore this args))
                       (js-throw (make-native-error "TypeError"
                                                    "Constructor WeakMap requires 'new'")))
                     0)))
      (setf (js-object-construct wmctor)
            (lambda (args nt)
              (let* ((proto (weak-proto-from-newtarget realm nt wmp))
                     (o (make-object :proto proto :class "WeakMap"
                                     :internal (list :weakmap-data (make-hash-table :test 'eq))))
                     (iterable (arg 0 args)))
                (unless (js-null-or-undef iterable)
                  (let ((adder (js-get o "set")))
                    (unless (js-callable-p adder)
                      (js-throw (make-native-error "TypeError" "WeakMap.prototype.set is not callable")))
                    (weak-add-entries-from-iterable iterable adder o t)))
                o)))
      (def-value wmctor "prototype" wmp :writable nil :configurable nil)
      (def-value wmp "constructor" wmctor)
      (def-method realm wmp "set" 2 (this args)
        (let ((tbl (require-weak-data this :weakmap-data "WeakMap.prototype.set"))
              (key (arg 0 args)) (val (arg 1 args)))
          (unless (can-be-held-weakly realm key)
            (js-throw (make-native-error "TypeError" "Invalid value used as weak map key")))
          (setf (gethash key tbl) val)
          this))
      (def-method realm wmp "get" 1 (this args)
        (let ((tbl (require-weak-data this :weakmap-data "WeakMap.prototype.get"))
              (key (arg 0 args)))
          (if (can-be-held-weakly realm key)
              (gethash key tbl *undefined*)
              *undefined*)))
      (def-method realm wmp "has" 1 (this args)
        (let ((tbl (require-weak-data this :weakmap-data "WeakMap.prototype.has"))
              (key (arg 0 args)))
          (js-bool (and (can-be-held-weakly realm key) (nth-value 1 (gethash key tbl))))))
      (def-method realm wmp "delete" 1 (this args)
        (let ((tbl (require-weak-data this :weakmap-data "WeakMap.prototype.delete"))
              (key (arg 0 args)))
          (if (and (can-be-held-weakly realm key) (nth-value 1 (gethash key tbl)))
              (progn (remhash key tbl) *true*)
              *false*)))
      ;; ---- the `upsert` proposal: getOrInsert / getOrInsertComputed ----
      (def-method realm wmp "getOrInsert" 2 (this args)
        (let ((tbl (require-weak-data this :weakmap-data "WeakMap.prototype.getOrInsert"))
              (key (arg 0 args)) (val (arg 1 args)))
          (unless (can-be-held-weakly realm key)
            (js-throw (make-native-error "TypeError" "Invalid value used as weak map key")))
          (multiple-value-bind (existing present) (gethash key tbl)
            (if present existing (setf (gethash key tbl) val)))))
      (def-method realm wmp "getOrInsertComputed" 2 (this args)
        (let ((tbl (require-weak-data this :weakmap-data "WeakMap.prototype.getOrInsertComputed"))
              (key (arg 0 args)) (cb (arg 1 args)))
          (unless (can-be-held-weakly realm key)
            (js-throw (make-native-error "TypeError" "Invalid value used as weak map key")))
          (unless (js-callable-p cb)
            (js-throw (make-native-error "TypeError" "callbackfn is not callable")))
          (multiple-value-bind (existing present) (gethash key tbl)
            (if present
                existing
                (let ((val (js-call cb *undefined* (list key))))
                  ;; Set unconditionally (overwrites any mutation the callback made).
                  (setf (gethash key tbl) val))))))
      (put wmp tostag "WeakMap" :enumerable nil :writable nil :configurable t)
      (define-global realm "WeakMap" wmctor))

    ;; =======================================================================
    ;; WeakSet
    ;; =======================================================================
    (let* ((wsp (make-object :proto op :class "WeakSet"))
           (wsctor (native-function realm "WeakSet"
                     (lambda (this args) (declare (ignore this args))
                       (js-throw (make-native-error "TypeError"
                                                    "Constructor WeakSet requires 'new'")))
                     0)))
      (setf (js-object-construct wsctor)
            (lambda (args nt)
              (let* ((proto (weak-proto-from-newtarget realm nt wsp))
                     (o (make-object :proto proto :class "WeakSet"
                                     :internal (list :weakset-data (make-hash-table :test 'eq))))
                     (iterable (arg 0 args)))
                (unless (js-null-or-undef iterable)
                  (let ((adder (js-get o "add")))
                    (unless (js-callable-p adder)
                      (js-throw (make-native-error "TypeError" "WeakSet.prototype.add is not callable")))
                    (weak-add-entries-from-iterable iterable adder o nil)))
                o)))
      (def-value wsctor "prototype" wsp :writable nil :configurable nil)
      (def-value wsp "constructor" wsctor)
      (def-method realm wsp "add" 1 (this args)
        (let ((tbl (require-weak-data this :weakset-data "WeakSet.prototype.add"))
              (val (arg 0 args)))
          (unless (can-be-held-weakly realm val)
            (js-throw (make-native-error "TypeError" "Invalid value used in weak set")))
          (setf (gethash val tbl) *true*)
          this))
      (def-method realm wsp "has" 1 (this args)
        (let ((tbl (require-weak-data this :weakset-data "WeakSet.prototype.has"))
              (val (arg 0 args)))
          (js-bool (and (can-be-held-weakly realm val) (nth-value 1 (gethash val tbl))))))
      (def-method realm wsp "delete" 1 (this args)
        (let ((tbl (require-weak-data this :weakset-data "WeakSet.prototype.delete"))
              (val (arg 0 args)))
          (if (and (can-be-held-weakly realm val) (nth-value 1 (gethash val tbl)))
              (progn (remhash val tbl) *true*)
              *false*)))
      (put wsp tostag "WeakSet" :enumerable nil :writable nil :configurable t)
      (define-global realm "WeakSet" wsctor))))

(register-builtin-installer 'install-weak)
