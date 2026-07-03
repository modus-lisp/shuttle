;;;; builtins/map-set.lisp — Map + Set (constructors + prototypes).
;;;; One method group per file. See array-iteration.lisp for the convention + helpers.
;;;;
;;;; Storage model: each instance carries a CL structure in its `internal` plist
;;;; under :map-data / :set-data. Entries are held in an append-only adjustable
;;;; vector of ENTRY structs (key value deleted-p), preserving INSERTION ORDER.
;;;; Deletion tombstones the entry (so live iterators + forEach keep a stable
;;;; cursor); a parallel equal/eq index (a CL list of live entries scanned with
;;;; SameValueZero) does membership lookup. Keys use SameValueZero; -0 normalizes
;;;; to +0 on the way in.
(in-package #:shuttle)

(defstruct (ms-entry (:constructor make-ms-entry (key value)))
  key value (deleted nil))

(defstruct (ms-data (:constructor make-ms-data))
  ;; append-only vector of ms-entry (tombstoned, never shrunk mid-life)
  (entries (make-array 0 :adjustable t :fill-pointer 0))
  ;; count of live (non-deleted) entries
  (size 0))

(defun ms-normalize-key (k)
  "SameValueZero: -0 -> +0 so map/set keys canonicalize negative zero."
  (if (and (floatp k) (zerop k)) 0d0 k))

(defun ms-find (data key)
  "Return the live ms-entry whose key is SameValueZero-equal to KEY, or NIL."
  (loop for e across (ms-data-entries data)
        when (and (not (ms-entry-deleted e)) (same-value-zero (ms-entry-key e) key))
          do (return e)))

(defun ms-this-data (this slot)
  "Pull the CL storage off THIS's internal plist; TypeError if absent."
  (let ((d (and (js-object-p this) (js-object-internal this)
                (getf (js-object-internal this) slot))))
    (unless (ms-data-p d)
      (js-throw (make-native-error "TypeError"
                                   (if (eq slot :map-data)
                                       "Method called on incompatible receiver (not a Map)"
                                       "Method called on incompatible receiver (not a Set)"))))
    d))

(defun ms-set (data key value)
  "Insert or update; returns nothing. KEY assumed already normalized."
  (let ((e (ms-find data key)))
    (if e
        (setf (ms-entry-value e) value)
        (progn
          (vector-push-extend (make-ms-entry key value) (ms-data-entries data))
          (incf (ms-data-size data))))))

(defun ms-delete (data key)
  "Tombstone the entry for KEY; return T if something was removed."
  (let ((e (ms-find data key)))
    (when e
      (setf (ms-entry-deleted e) t
            (ms-entry-key e) *undefined*
            (ms-entry-value e) *undefined*)
      (decf (ms-data-size data))
      t)))

(defun ms-clear (data)
  (loop for e across (ms-data-entries data)
        do (setf (ms-entry-deleted e) t
                 (ms-entry-key e) *undefined*
                 (ms-entry-value e) *undefined*))
  (setf (ms-data-size data) 0))

;;; ---------------------------------------------------------------------------
;;; Iterator object (mirrors make-array-iterator): next()->{value,done}, self
;;; @@iterator. KIND is :key, :value or :key+value. The cursor walks the
;;; append-only vector so entries added after creation are seen and tombstoned
;;; ones skipped (per spec live-iteration semantics).
;;; ---------------------------------------------------------------------------
(defun make-ms-iterator (realm data kind)
  (let ((i 0) (finished nil)
        (it (make-object :proto (realm-object-proto realm) :class "Map Iterator")))
    (def-method realm it "next" 0 (this args)
      (block done
        (let ((res (make-object :proto (realm-object-proto realm)))
              (entries (ms-data-entries data)))
          (when finished
            (put res "value" *undefined*) (put res "done" *true*)
            (return-from done res))
          (loop
            (when (>= i (fill-pointer entries))
              (setf finished t)
              (put res "value" *undefined*) (put res "done" *true*)
              (return-from done res))
            (let ((e (aref entries i)))
              (incf i)
              (unless (ms-entry-deleted e)
                (put res "value"
                     (ecase kind
                       (:key (ms-entry-key e))
                       (:value (ms-entry-value e))
                       (:key+value (make-array-object (list (ms-entry-key e)
                                                            (ms-entry-value e))))))
                (put res "done" *false*)
                (return-from done res)))))))
    (when *symbol-iterator*
      (put it *symbol-iterator*
           (native-function realm "[Symbol.iterator]"
             (lambda (this args) (declare (ignore args)) this) 0)
           :enumerable nil :writable t :configurable t))
    it))

;;; ---------------------------------------------------------------------------
;;; consume an iterable ctor argument: for each item, call ADDER on it.
;;; ---------------------------------------------------------------------------
(defun ms-iterator-close (it)
  "IteratorClose (best-effort): invoke it.return() ignoring its result/errors."
  (ignore-errors
    (let ((ret (js-get it "return")))
      (when (js-callable-p ret) (js-call ret it '())))))

(defun ms-consume-iterable (iter adder)
  (let ((it (get-iterator iter)))
    (loop
      (let ((r (iterator-step it)))       ; if next() throws, do NOT close
        (when (js-truthy (js-get r "done")) (return))
        ;; reading value / running adder may abrupt-complete -> IteratorClose
        (let ((normal nil))
          (unwind-protect
               (progn (funcall adder (js-get r "value")) (setf normal t))
            (unless normal (ms-iterator-close it))))))))

;;; ---------------------------------------------------------------------------
;;; Set-methods proposal (union/intersection/difference/symmetricDifference/
;;; isSubsetOf/isSupersetOf/isDisjointFrom). GetSetRecord validates a set-like
;;; argument (an object with numeric `size`, callable `has`, callable `keys`).
;;; ---------------------------------------------------------------------------
(defstruct (set-record (:constructor make-set-record (obj size has keys)))
  obj size has keys)

(defun get-set-record (obj)
  (unless (js-object-p obj)
    (js-throw (make-native-error "TypeError" "argument is not an object")))
  (let* ((raw-size (js-get obj "size"))
         (num-size (to-number raw-size)))
    (when (js-nan-p num-size)
      (js-throw (make-native-error "TypeError" "size is NaN")))
    (let ((int-size (to-integer-or-infinity num-size)))
      (when (< int-size 0)
        (js-throw (make-native-error "RangeError" "size is negative")))
      (let ((has (js-get obj "has")) (keys (js-get obj "keys")))
        (unless (js-callable-p has)
          (js-throw (make-native-error "TypeError" "has is not callable")))
        (unless (js-callable-p keys)
          (js-throw (make-native-error "TypeError" "keys is not callable")))
        (make-set-record obj int-size has keys)))))

(defun sr-has (rec key)
  (js-truthy (js-call (set-record-has rec) (set-record-obj rec) (list key))))

(defun sr-keys-iterator (rec)
  "GetKeysIterator: call rec.keys(), then GetIteratorDirect (read .next ONCE).
   Returns (values iterator next-method)."
  (let ((it (js-call (set-record-keys rec) (set-record-obj rec) '())))
    (unless (js-object-p it)
      (js-throw (make-native-error "TypeError" "keys() did not return an object")))
    (let ((next (js-get it "next")))          ; read once (GetIteratorDirect)
      (unless (js-callable-p next)
        (js-throw (make-native-error "TypeError" "keys() iterator has no next")))
      (values it next))))

(defmacro sr-do-keys ((var rec) &body body)
  "Iterate the set-like record's keys iterator, binding VAR (normalized -0).
   The iterator's .next is read ONCE (GetIteratorDirect) and reused each step.
   If BODY exits the loop early (a non-local transfer of control out of the
   macro — e.g. return-from because a decision was reached), IteratorClose the
   keys iterator (call its return()). When the iterator is exhausted normally
   (done=true), return() is NOT called (the spec CompletionRecord is normal)."
  (let ((it (gensym)) (next (gensym)) (r (gensym)) (exhausted (gensym)))
    `(multiple-value-bind (,it ,next) (sr-keys-iterator ,rec)
       (let ((,exhausted nil))
         (unwind-protect
              (loop
                (let ((,r (js-call ,next ,it '())))
                  (unless (js-object-p ,r)
                    (js-throw (make-native-error "TypeError" "iterator result is not an object")))
                  (when (js-truthy (js-get ,r "done")) (setf ,exhausted t) (return))
                  (let ((,var (ms-normalize-key (js-get ,r "value"))))
                    ,@body)))
           (unless ,exhausted (ms-iterator-close ,it)))))))

(defun ms-this-set-data (this)
  (ms-this-data this :set-data))

(defun make-fresh-set (realm entries)
  "Build a new Set instance from a CL list of (already-normalized) values."
  (let* ((data (make-ms-data))
         (sp (js-get (js-get (realm-global realm) "Set") "prototype"))
         (o (make-object :proto sp :class "Set" :internal (list :set-data data))))
    (dolist (v entries) (ms-set data v v))
    o))

;;; ===========================================================================
;;; Map
;;; ===========================================================================
(defun install-map (realm)
  (let* ((op (realm-object-proto realm))
         (proto (make-object :proto op :class "Map"))
         (ctor (native-function realm "Map"
                 (lambda (this args) (declare (ignore this args))
                   (js-throw (make-native-error "TypeError"
                               "Constructor Map requires 'new'")))
                 0)))
    (setf (js-object-construct ctor)
          (lambda (args nt) (declare (ignore nt))
            (let* ((data (make-ms-data))
                   (o (make-object :proto proto :class "Map"
                                   :internal (list :map-data data))))
              (let ((iter (arg 0 args)))
                (unless (js-null-or-undef iter)
                  (let ((setter (js-get proto "set")))
                    (unless (js-callable-p setter)
                      (js-throw (make-native-error "TypeError" "Map.prototype.set is not callable")))
                    (ms-consume-iterable iter
                      (lambda (pair)
                        (unless (js-object-p pair)
                          (js-throw (make-native-error "TypeError" "Iterator value is not an entry object")))
                        (js-call setter o (list (js-get pair "0") (js-get pair "1"))))))))
              o)))
    (def-value ctor "prototype" proto :writable nil :configurable nil)
    (def-value proto "constructor" ctor)

    ;; ---- Map.groupBy(items, callbackfn) [array-grouping proposal] ----
    ;; GroupBy with key-coercion = "zero" (SameValueZero keys, -0 -> +0). Groups
    ;; VALUES into per-key arrays; returns a fresh Map.
    (def-method realm ctor "groupBy" 2 (this args)
      (declare (ignore this))
      (let ((items (arg 0 args)) (cb (arg 1 args)))
        (when (js-null-or-undef items)
          (js-throw (make-native-error "TypeError" "items is not iterable")))
        (unless (js-callable-p cb)
          (js-throw (make-native-error "TypeError" "callbackfn is not callable")))
        (let* ((data (make-ms-data))
               (result (make-object :proto proto :class "Map"
                                    :internal (list :map-data data)))
               (it (get-iterator items)) (i 0))
          (let ((normal nil))
            (unwind-protect
                 (progn
                   (loop
                     (let ((r (iterator-step it)))
                       (when (js-truthy (js-get r "done")) (return))
                       (let* ((v (js-get r "value"))
                              (key (ms-normalize-key
                                    (js-call cb *undefined* (list v (float i 1d0)))))
                              (e (ms-find data key)))
                         (if e
                             ;; append v to the existing group array
                             (let* ((arr (ms-entry-value e))
                                    (len (truncate (to-number (js-get arr "length")))))
                               (js-set arr (princ-to-string len) v)
                               (js-set arr "length" (float (1+ len) 1d0)))
                             (ms-set data key (make-array-object (list v))))
                         (incf i))))
                   (setf normal t))
              (unless normal (ms-iterator-close it))))
          result)))

    (def-method realm proto "get" 1 (this args)
      (let* ((data (ms-this-data this :map-data))
             (e (ms-find data (ms-normalize-key (arg 0 args)))))
        (if e (ms-entry-value e) *undefined*)))
    (def-method realm proto "set" 2 (this args)
      (let ((data (ms-this-data this :map-data)))
        (ms-set data (ms-normalize-key (arg 0 args)) (arg 1 args))
        this))
    ;; ---- upsert proposal: getOrInsert / getOrInsertComputed ----
    (def-method realm proto "getOrInsert" 2 (this args)
      (let* ((data (ms-this-data this :map-data))
             (key (ms-normalize-key (arg 0 args)))
             (e (ms-find data key)))
        (if e (ms-entry-value e)
            (let ((v (arg 1 args))) (ms-set data key v) v))))
    (def-method realm proto "getOrInsertComputed" 2 (this args)
      (let* ((data (ms-this-data this :map-data))
             (key (ms-normalize-key (arg 0 args)))
             (cb (arg 1 args)))
        (unless (js-callable-p cb)
          (js-throw (make-native-error "TypeError" "callbackfn is not callable")))
        (let ((e (ms-find data key)))
          (if e (ms-entry-value e)
              ;; Compute with the (normalized) key, then insert. Re-check after the
              ;; callback (it may have mutated the map); overwrite unconditionally.
              (let ((v (js-call cb *undefined* (list key))))
                (ms-set data key v) v)))))
    (def-method realm proto "has" 1 (this args)
      (let ((data (ms-this-data this :map-data)))
        (js-bool (and (ms-find data (ms-normalize-key (arg 0 args))) t))))
    (def-method realm proto "delete" 1 (this args)
      (let ((data (ms-this-data this :map-data)))
        (js-bool (ms-delete data (ms-normalize-key (arg 0 args))))))
    (def-method realm proto "clear" 0 (this args)
      (ms-clear (ms-this-data this :map-data)) *undefined*)
    (def-method realm proto "forEach" 1 (this args)
      (let ((data (ms-this-data this :map-data))
            (cb (arg 0 args)) (ta (arg 1 args)))
        (unless (js-callable-p cb)
          (js-throw (make-native-error "TypeError" "callback is not a function")))
        (let ((entries (ms-data-entries data)) (i 0))
          (loop while (< i (fill-pointer entries)) do
            (let ((e (aref entries i)))
              (unless (ms-entry-deleted e)
                (js-call cb ta (list (ms-entry-value e) (ms-entry-key e) this))))
            (incf i)))
        *undefined*))
    (def-getter realm proto "size"
      (lambda (this args) (declare (ignore args))
        (float (ms-data-size (ms-this-data this :map-data)) 1d0)))
    (def-method realm proto "keys" 0 (this args)
      (make-ms-iterator realm (ms-this-data this :map-data) :key))
    (def-method realm proto "values" 0 (this args)
      (make-ms-iterator realm (ms-this-data this :map-data) :value))
    (let ((entries-fn
            (native-function realm "entries"
              (lambda (this args) (declare (ignore args))
                (make-ms-iterator realm (ms-this-data this :map-data) :key+value)) 0)))
      (put proto "entries" entries-fn :enumerable nil :writable t :configurable t)
      (when *symbol-iterator*
        (put proto *symbol-iterator* entries-fn :enumerable nil :writable t :configurable t)))
    (put proto (symbol-tostringtag realm) "Map"
         :enumerable nil :writable nil :configurable t)
    (define-global realm "Map" ctor)))

;;; ===========================================================================
;;; Set
;;; ===========================================================================
(defun install-set (realm)
  (let* ((op (realm-object-proto realm))
         (proto (make-object :proto op :class "Set"))
         (ctor (native-function realm "Set"
                 (lambda (this args) (declare (ignore this args))
                   (js-throw (make-native-error "TypeError"
                               "Constructor Set requires 'new'")))
                 0)))
    (setf (js-object-construct ctor)
          (lambda (args nt) (declare (ignore nt))
            (let* ((data (make-ms-data))
                   (o (make-object :proto proto :class "Set"
                                   :internal (list :set-data data))))
              (let ((iter (arg 0 args)))
                (unless (js-null-or-undef iter)
                  (let ((adder (js-get proto "add")))
                    (unless (js-callable-p adder)
                      (js-throw (make-native-error "TypeError" "Set.prototype.add is not callable")))
                    (ms-consume-iterable iter
                      (lambda (v) (js-call adder o (list v)))))))
              o)))
    (def-value ctor "prototype" proto :writable nil :configurable nil)
    (def-value proto "constructor" ctor)

    (def-method realm proto "add" 1 (this args)
      (let ((data (ms-this-data this :set-data))
            (v (ms-normalize-key (arg 0 args))))
        (ms-set data v v)
        this))
    (def-method realm proto "has" 1 (this args)
      (let ((data (ms-this-data this :set-data)))
        (js-bool (and (ms-find data (ms-normalize-key (arg 0 args))) t))))
    (def-method realm proto "delete" 1 (this args)
      (let ((data (ms-this-data this :set-data)))
        (js-bool (ms-delete data (ms-normalize-key (arg 0 args))))))
    (def-method realm proto "clear" 0 (this args)
      (ms-clear (ms-this-data this :set-data)) *undefined*)
    (def-method realm proto "forEach" 1 (this args)
      (let ((data (ms-this-data this :set-data))
            (cb (arg 0 args)) (ta (arg 1 args)))
        (unless (js-callable-p cb)
          (js-throw (make-native-error "TypeError" "callback is not a function")))
        (let ((entries (ms-data-entries data)) (i 0))
          (loop while (< i (fill-pointer entries)) do
            (let ((e (aref entries i)))
              (unless (ms-entry-deleted e)
                (js-call cb ta (list (ms-entry-value e) (ms-entry-value e) this))))
            (incf i)))
        *undefined*))
    (def-getter realm proto "size"
      (lambda (this args) (declare (ignore args))
        (float (ms-data-size (ms-this-data this :set-data)) 1d0)))

    ;; ---- Set-methods proposal --------------------------------------------
    ;; DO-SET-LIVE walks THIS's entry vector by index, re-checking liveness at
    ;; each visit (like forEach) so deletions performed by a set-like's callback
    ;; mid-iteration are observed (spec: the loop indexes SetData and skips empty
    ;; slots that were tombstoned before being visited). Early exit via BODY is
    ;; a normal Lisp non-local transfer.
    (macrolet ((do-set-live ((var data) &body body)
                 (let ((d (gensym)) (entries (gensym)) (i (gensym)) (e (gensym)))
                   `(let* ((,d ,data) (,entries (ms-data-entries ,d)) (,i 0))
                      (loop while (< ,i (fill-pointer ,entries)) do
                        (let ((,e (aref ,entries ,i)))
                          (unless (ms-entry-deleted ,e)
                            (let ((,var (ms-entry-value ,e))) ,@body)))
                        (incf ,i))))))
    (flet ((live-values (data)
             (loop for e across (ms-data-entries data)
                   unless (ms-entry-deleted e) collect (ms-entry-value e))))
      (def-method realm proto "union" 1 (this args)
        (let* ((data (ms-this-data this :set-data))
               (rec (get-set-record (arg 0 args)))
               (out (live-values data)) (seen (make-ms-data)))
          (dolist (v out) (ms-set seen v v))
          (sr-do-keys (k rec)
            (unless (ms-find seen k) (ms-set seen k k) (setf out (append out (list k)))))
          (make-fresh-set realm out)))
      (def-method realm proto "intersection" 1 (this args)
        (let* ((data (ms-this-data this :set-data))
               (rec (get-set-record (arg 0 args)))
               (result '()))
          (if (<= (ms-data-size data) (set-record-size rec))
              (do-set-live (v data)
                (when (sr-has rec v) (push v result)))
              (let ((seen (make-ms-data)))
                (sr-do-keys (k rec)
                  (when (and (ms-find data k) (not (ms-find seen k)))
                    (ms-set seen k k) (push k result)))))
          (make-fresh-set realm (nreverse result))))
      (def-method realm proto "difference" 1 (this args)
        (let* ((data (ms-this-data this :set-data))
               (rec (get-set-record (arg 0 args)))
               (result (make-ms-data)))
          (dolist (v (live-values data)) (ms-set result v v))
          (if (<= (ms-data-size data) (set-record-size rec))
              (do-set-live (v data) (when (sr-has rec v) (ms-delete result v)))
              (sr-do-keys (k rec) (when (ms-find result k) (ms-delete result k))))
          (make-fresh-set realm (loop for e across (ms-data-entries result)
                                      unless (ms-entry-deleted e) collect (ms-entry-value e)))))
      (def-method realm proto "symmetricDifference" 1 (this args)
        (let* ((data (ms-this-data this :set-data))
               (rec (get-set-record (arg 0 args)))
               (result (make-ms-data)))
          (dolist (v (live-values data)) (ms-set result v v))
          (sr-do-keys (k rec)
            (if (ms-find data k)
                (ms-delete result k)
                (unless (ms-find result k) (ms-set result k k))))
          (make-fresh-set realm (loop for e across (ms-data-entries result)
                                      unless (ms-entry-deleted e) collect (ms-entry-value e)))))
      (def-method realm proto "isSubsetOf" 1 (this args)
        (block done
          (let* ((data (ms-this-data this :set-data))
                 (rec (get-set-record (arg 0 args))))
            (when (> (ms-data-size data) (set-record-size rec)) (return-from done *false*))
            (do-set-live (v data)
              (unless (sr-has rec v) (return-from done *false*)))
            *true*)))
      (def-method realm proto "isSupersetOf" 1 (this args)
        (block done
          (let* ((data (ms-this-data this :set-data))
                 (rec (get-set-record (arg 0 args))))
            (when (< (ms-data-size data) (set-record-size rec)) (return-from done *false*))
            (sr-do-keys (k rec)
              (unless (ms-find data k) (return-from done *false*)))
            *true*)))
      (def-method realm proto "isDisjointFrom" 1 (this args)
        (block done
          (let* ((data (ms-this-data this :set-data))
                 (rec (get-set-record (arg 0 args))))
            (if (<= (ms-data-size data) (set-record-size rec))
                (do-set-live (v data)
                  (when (sr-has rec v) (return-from done *false*)))
                (sr-do-keys (k rec)
                  (when (ms-find data k) (return-from done *false*))))
            *true*)))))

    (def-method realm proto "entries" 0 (this args)
      (make-ms-iterator realm (ms-this-data this :set-data) :key+value))
    (let ((values-fn
            (native-function realm "values"
              (lambda (this args) (declare (ignore args))
                (make-ms-iterator realm (ms-this-data this :set-data) :value)) 0)))
      (put proto "values" values-fn :enumerable nil :writable t :configurable t)
      (put proto "keys" values-fn :enumerable nil :writable t :configurable t)
      (when *symbol-iterator*
        (put proto *symbol-iterator* values-fn :enumerable nil :writable t :configurable t)))
    (put proto (symbol-tostringtag realm) "Set"
         :enumerable nil :writable nil :configurable t)
    (define-global realm "Set" ctor)))

(defun install-map-set (realm)
  (install-map realm)
  (install-set realm))

(register-builtin-installer 'install-map-set)
