;;;; value.lisp — JS value model + the object internal-method protocol.
;;;;
;;;; JS values are CL values: numbers = double-float, strings = CL string
;;;; (UTF-16-code-unit semantics are a TODO — see README), booleans/undefined/
;;;; null = singletons, objects = js-object. Every object's behavior is its
;;;; internal methods ([[Get]]/[[Set]]/[[Call]]/…); ordinary objects use the
;;;; defaults here, while HOST objects (weft's DOM) and exotics/Proxy override
;;;; them via the INTERNAL slot. That one factoring is both spec-correct and the
;;;; seam a consumer hangs bindings (and weft's reflow hook) on.
(in-package #:shuttle)

(define-condition shuttle-error (error)
  ((value :initarg :value :reader shuttle-error-value))
  (:report (lambda (c s) (format s "Uncaught ~a" (ignore-errors (to-string (shuttle-error-value c)))))))
(defun js-throw (value) (error 'shuttle-error :value (if (stringp value) value value)))

;;; ---- singletons ----
(defstruct (js-singleton (:print-object (lambda (o s) (format s "#<js ~a>" (js-singleton-name o))))) name)
(defparameter *undefined* (make-js-singleton :name "undefined"))
(defparameter *null*      (make-js-singleton :name "null"))
(defparameter *true*      (make-js-singleton :name "true"))
(defparameter *false*     (make-js-singleton :name "false"))
(declaim (inline js-bool js-undefined-p))
(defun js-bool (x) (if x *true* *false*))
(defun js-undefined-p (x) (eq x *undefined*))

;;; ---- IEEE-754 specials (JS never traps on float ops) ----
(defmacro with-js-floats (&body body)
  `(sb-int:with-float-traps-masked (:invalid :overflow :divide-by-zero) ,@body))
(defparameter *inf*  sb-ext:double-float-positive-infinity)
(defparameter *-inf* sb-ext:double-float-negative-infinity)
(defparameter *nan*  (with-js-floats (- *inf* *inf*)))
(declaim (inline js-nan-p js-bigint-p))
(defun js-nan-p (x) (and (floatp x) (/= x x)))
;;; A JS BigInt value is represented as a CL INTEGER (Numbers are always
;;; double-float, so an integer is unambiguously a BigInt).
(defun js-bigint-p (x) (integerp x))

;;; ---- symbols (a distinct primitive value type) ----
(defstruct (js-symbol (:constructor %make-js-symbol) (:print-object (lambda (o s) (format s "#<js Symbol ~a>" (js-symbol-desc o)))))
  desc)                                   ; description (a CL string or nil)
(defun make-js-symbol (&optional desc) (%make-js-symbol :desc (and (not (eq desc *undefined*)) desc)))

;;; ---- objects + property descriptors ----
(defstruct (prop (:constructor make-prop))
  value get set (writable t) (enumerable t) (configurable t) (accessor nil))

(defstruct (js-object (:constructor %make-object))
  (props nil)               ; own (string/symbol)-keyed descriptors as a key->PROP map. Small-object storage (see PROPS-GET & co.): NIL (empty) -> alist (few keys) -> EQUAL hash-table (once past +props-small-limit+). Enumeration order is NOT here; KEY-ORDER carries it, so representation switches are order-safe.
  (key-order '())           ; own keys in insertion order (reversed); ordinary-own-keys re-sorts. May carry tombstones (keys since forgotten); KEY-SET is the source of truth for membership and %own-keys-in-order filters through it.
  (key-set nil)             ; lazily-created EQUAL membership set mirroring the LIVE keys — keeps %key-touch / %key-forget O(1) instead of scanning/deleting key-order (which is O(n) → O(n^2) for big arrays: bulk index writes and .length truncation)
  (key-tombstones 0)        ; count of forgotten-but-still-in-key-order entries; trigger a compaction of KEY-ORDER once they dominate
  (proto *null*)            ; [[Prototype]]
  (extensible t)
  (class "Object")          ; loosely [[Class]] / internal kind
  (internal nil)            ; plist of internal-method overrides (host objects)
  (primitive nil)           ; [[NumberData]]/[[StringData]]/[[BooleanData]]/[[SymbolData]] for wrappers
  (private nil)             ; PrivateName -> private-element (brand-checked #x members); nil until first use
  (call nil)                ; [[Call]]      : (this args-list) -> value
  (construct nil))          ; [[Construct]] : (args-list new-target) -> object

;;; ---- private class members (#x) ----
;;; A PRIVATE-NAME is a unique runtime identity for one `#name` within one class
;;; (created at class-definition time). The compiler embeds it as a constant. An
;;; object "has" a private name iff its PRIVATE table contains that identity.
(defstruct (private-name (:constructor make-private-name (description)))
  description)          ; "#x" (for error messages / debugging)
;; A private element value is one of:
;;   (:field . VALUE)         a private instance/static field
;;   (:method . FN)           a private method (shared, brand only)
;;   (:accessor GETTER SETTER) private get/set (either may be nil)
(defun object-private-table (o)
  (or (js-object-private o) (setf (js-object-private o) (make-hash-table :test 'eq))))
(defun private-get-element (o pn)
  (and (js-object-p o) (js-object-private o) (gethash pn (js-object-private o))))

(defun private-method-name (kind pn)
  "Function name for a private method/accessor: `#x`, `get #x`, or `set #x`."
  (let ((d (private-name-description pn)))
    (case kind (:get (concatenate 'string "get " d))
               (:set (concatenate 'string "set " d))
               (t d))))

(defun private-require (o pn)
  "The private element for PN on O, or a TypeError if O lacks the private brand."
  (let ((el (private-get-element o pn)))
    (unless el
      (js-throw (make-native-error "TypeError"
                  (format nil "Cannot read private member #~a from an object whose class did not declare it"
                          (private-name-description pn)))))
    el))

(defun private-element-get (el receiver)
  "Read a private element (already brand-checked)."
  (ecase (car el)
    (:field (cdr el))
    (:method (cdr el))
    (:accessor (let ((getter (second el)))
                 (if getter (js-call getter receiver '())
                     (js-throw (make-native-error "TypeError" "Private member was defined without a getter")))))))

(defun private-element-set (el receiver v)
  "Write a private element (already brand-checked)."
  (ecase (car el)
    (:field (setf (cdr el) v))
    (:method (js-throw (make-native-error "TypeError" "Private method is not writable")))
    (:accessor (let ((setter (third el)))
                 (if setter (js-call setter receiver (list v))
                     (js-throw (make-native-error "TypeError" "Private member was defined without a setter")))))))

;; Small-object threshold: at most this many own keys stay in the compact
;; (alist props / scanned key-order) representation before promoting to a
;; hash-table. Shared by PROPS storage and KEY-ORDER membership.
(defconstant +props-small-limit+ 8)

(declaim (inline %key-touch %key-forget %own-keys-in-order))
(defun %key-set-of (o)
  "The membership hash for O's live own keys, built lazily from KEY-ORDER."
  (or (js-object-key-set o)
      (setf (js-object-key-set o)
            (let ((h (make-hash-table :test 'equal
                                      :size (max 8 (length (js-object-key-order o))))))
              (dolist (ek (js-object-key-order o)) (setf (gethash ek h) t))
              h))))
(defun %key-compact (o)
  "Drop tombstoned (forgotten) entries from KEY-ORDER, keeping only live keys in
   their original relative order."
  (let ((set (js-object-key-set o)))
    (setf (js-object-key-order o)
          (delete-if-not (lambda (k) (gethash k set)) (js-object-key-order o))
          (js-object-key-tombstones o) 0)))
(defun %key-touch (o k)
  "Record K as an own key of O (idempotent, preserves first-insertion order).
   Small objects carry NO KEY-SET and test membership with a short scan of
   KEY-ORDER (which then holds exactly the live keys, no tombstones); once the
   key count crosses +props-small-limit+ a KEY-SET (an EQUAL hash mirroring the
   live keys) is built so a large object/array stays O(1) per insert."
  (let ((set (js-object-key-set o)))
    (if set
        ;; hashed regime: O(1) membership + tombstone bookkeeping
        (unless (gethash k set)
          ;; A re-added key may still linger as a tombstone in KEY-ORDER. Compact
          ;; BEFORE marking K live (compaction keys off SET membership; if K were
          ;; already in SET the stale tombstone couldn't be told apart and would
          ;; survive, duplicating K and corrupting enumeration order).
          (when (plusp (js-object-key-tombstones o)) (%key-compact o))
          (setf (gethash k set) t)
          (push k (js-object-key-order o)))
        ;; small regime: KEY-ORDER is exactly the live keys (no tombstones)
        (unless (member k (the list (js-object-key-order o)) :test #'equal)
          (push k (js-object-key-order o))
          (when (> (length (the list (js-object-key-order o))) +props-small-limit+)
            (%key-set-of o))))))    ; promote to the hashed regime
(defun %key-forget (o k)
  "Remove K from O's live own keys. Hashed regime: O(1) — leave a tombstone in
   KEY-ORDER that %own-keys-in-order filters out, compacting once tombstones
   dominate (keeps bulk deletion O(n) overall, not O(n^2)). Small regime:
   KEY-ORDER holds only live keys, so delete K from it directly."
  (let ((set (js-object-key-set o)))
    (if set
        (when (gethash k set)
          (remhash k set)
          (when (> (incf (js-object-key-tombstones o))
                   (hash-table-count set))
            (%key-compact o)))
        (setf (js-object-key-order o)
              (delete k (the list (js-object-key-order o)) :test #'equal)))))
(defun %own-keys-in-order (o)          ; insertion order, tombstones filtered out
  (if (plusp (js-object-key-tombstones o))
      (let ((set (js-object-key-set o)))
        (loop for k in (reverse (js-object-key-order o))
              when (or (null set) (gethash k set)) collect k))
      (reverse (js-object-key-order o))))

(defun make-object (&key (proto *null*) (class "Object") call construct internal)
  (%make-object :proto proto :class class :call call :construct construct :internal internal))

;;; ---- own-property storage (small-object optimization) --------------------
;;; The PROPS slot maps an own property key (a CL string, or a js-symbol
;;; compared by EQ) to its PROP descriptor. Allocating a full EQUAL hash-table
;;; per object is wasteful — most objects hold only a handful of properties — so
;;; storage grows lazily through three shapes:
;;;   NIL          — no own properties yet (the fresh-object common case)
;;;   alist        — ((key . prop) ...), while the count stays <= +props-small-limit+
;;;   hash-table   — EQUAL-tested, once an insert would exceed the small limit
;;; Enumeration ORDER is tracked separately in KEY-ORDER / KEY-SET (and
;;; ordinary-own-keys re-sorts index keys), so PROPS never has to preserve order:
;;; representation switches are order-safe and MAP-PROPS may run in any order.
;;; All access goes through this five-function API (get / present-p / set /
;;; remove / map) so the representation is swappable in one place.
;;; (+props-small-limit+ is defined above, shared with the KEY-ORDER helpers.)

(declaim (inline props-get props-present-p map-props))
(defun props-get (o k)
  "Own PROP for already-coerced key K on O, as (values prop present-p)."
  (let ((s (js-object-props o)))
    (cond ((null s) (values nil nil))
          ((hash-table-p s) (gethash k s))
          (t (let ((cell (assoc k (the list s) :test #'equal)))
               (if cell (values (cdr cell) t) (values nil nil)))))))

(defun props-present-p (o k)
  "T iff O has an own property named K (K already coerced)."
  (let ((s (js-object-props o)))
    (cond ((null s) nil)
          ((hash-table-p s) (nth-value 1 (gethash k s)))
          (t (and (assoc k (the list s) :test #'equal) t)))))

(defun props-set (o k p)
  "Store descriptor P under key K on O (insert or replace), migrating the alist
   to a hash-table once it would grow past +props-small-limit+ entries. Does NOT
   update KEY-ORDER — callers pair this with %key-touch."
  (let ((s (js-object-props o)))
    (cond
      ((hash-table-p s) (setf (gethash k s) p))
      ((null s) (setf (js-object-props o) (list (cons k p))))
      (t (let ((cell (assoc k (the list s) :test #'equal)))
           (cond
             (cell (setf (cdr cell) p))
             ((>= (length (the list s)) +props-small-limit+)
              (let ((h (make-hash-table :test 'equal :size (* 2 +props-small-limit+))))
                (dolist (c s) (setf (gethash (car c) h) (cdr c)))
                (setf (gethash k h) p (js-object-props o) h)))
             (t (setf (js-object-props o) (cons (cons k p) s)))))))
    p))

(defun props-remove (o k)
  "Remove key K's own descriptor from O (no-op if absent). Does NOT update
   KEY-ORDER — callers pair this with %key-forget."
  (let ((s (js-object-props o)))
    (cond ((null s))
          ((hash-table-p s) (remhash k s))
          (t (setf (js-object-props o) (delete k (the list s) :test #'equal :key #'car))))))

(defun map-props (o fn)
  "Call FN with (key prop) for each own property of O, in UNSPECIFIED order
   (order lives in KEY-ORDER, not here)."
  (let ((s (js-object-props o)))
    (cond ((null s))
          ((hash-table-p s) (maphash fn s))
          (t (dolist (c s) (funcall fn (car c) (cdr c)))))))

(declaim (inline prop-key))
(defun prop-key (k)
  "Coerce a value to a property key: strings and symbols pass through (symbols
   compare by EQ in the EQUAL-tested props table); everything else -> ToString."
  (cond ((stringp k) k) ((js-symbol-p k) k) (t (to-property-key k))))

;;; ---- internal-method dispatch (override hook, then ordinary) ----
(macrolet ((defop (name trap ordinary args)
             (let ((call (remove-if (lambda (s) (member s '(&optional &rest &key))) args)))
               `(defun ,name (o ,@args)
                  (if (js-object-p o)
                      (let ((tr (and (js-object-internal o) (getf (js-object-internal o) ,trap))))
                        (if tr (funcall tr o ,@call) (,ordinary o ,@call)))
                      (,ordinary o ,@call))))))
  (defop js-get    :get    ordinary-get    (key &optional receiver))
  (defop js-set    :set    ordinary-set    (key v &optional receiver))
  (defop js-has    :has    ordinary-has    (key))
  (defop js-delete :delete ordinary-delete (key))
  (defop js-own-keys :own-keys ordinary-own-keys ()))

;;; ---- [[GetPrototypeOf]] / [[SetPrototypeOf]] / [[IsExtensible]] /
;;;      [[PreventExtensions]] : honor a host/Proxy INTERNAL override, else the
;;;      ordinary struct-slot behavior. Callers (Reflect/Object/instanceof) must
;;;      route through these so Proxy traps actually fire.
(defun js-get-proto (o)
  "[[GetPrototypeOf]]: internal :get-proto trap, else the struct slot."
  (if (js-object-p o)
      (let ((tr (and (js-object-internal o) (getf (js-object-internal o) :get-proto))))
        (if tr (funcall tr o) (js-object-proto o)))
      *null*))

(defun js-set-proto (o v)
  "[[SetPrototypeOf]]: internal :set-proto trap, else OrdinarySetPrototypeOf.
   Ordinary: same proto -> T; non-extensible & different proto -> NIL (reject);
   a cycle through ordinary objects -> NIL. Returns T/NIL."
  (if (js-object-p o)
      (let ((tr (and (js-object-internal o) (getf (js-object-internal o) :set-proto))))
        (if tr (and (funcall tr o v) t)
            (ordinary-set-proto o v)))
      nil))

(defun ordinary-set-proto (o v)
  "OrdinarySetPrototypeOf(O, V): V is an object or null."
  (let ((current (js-object-proto o)))
    (cond
      ;; SameValue(V, current) -> succeed with no change.
      ((eq v current) t)
      ;; non-extensible and V differs -> reject.
      ((not (js-object-extensible o)) nil)
      (t
       ;; cycle check: walk the proposed chain. Stop (allow) if we reach null, or
       ;; hit an exotic object with its own [[SetPrototypeOf]] (its check is opaque).
       (let ((p v))
         (loop
           (cond
             ((eq p *null*) (return))                    ; no cycle
             ((eq p o) (return-from ordinary-set-proto nil)) ; cycle
             ((and (js-object-p p) (js-object-internal p)
                   (getf (js-object-internal p) :set-proto))
              (return))                                  ; exotic proto: stop walking
             ((js-object-p p) (setf p (js-object-proto p)))
             (t (return)))))
       (setf (js-object-proto o) v) t))))

(defun js-extensible-p (o)
  "[[IsExtensible]]: internal :is-extensible trap, else the struct slot. Returns T/NIL."
  (if (js-object-p o)
      (let ((tr (and (js-object-internal o) (getf (js-object-internal o) :is-extensible))))
        (if tr (and (funcall tr o) t) (and (js-object-extensible o) t)))
      nil))

(defun js-prevent-extensions (o)
  "[[PreventExtensions]]: internal :prevent-extensions trap, else clear the slot.
   Returns T/NIL."
  (if (js-object-p o)
      (let ((tr (and (js-object-internal o) (getf (js-object-internal o) :prevent-extensions))))
        (if tr (and (funcall tr o) t)
            (progn (setf (js-object-extensible o) nil) t)))
      nil))

(defun ordinary-get (o key &optional receiver)
  (unless receiver (setf receiver o))
  (cond
    ((js-object-p o)
     (let ((d (props-get o (prop-key key))))
       (cond (d (if (prop-accessor d)
                    (let ((g (prop-get d)))
                      (if (and g (not (js-undefined-p g))) (js-call g receiver '()) *undefined*))
                    (prop-value d)))
             ((js-object-p (js-object-proto o)) (js-get (js-object-proto o) key receiver))
             (t *undefined*))))
    ;; primitive property access: string index/length inline, else box → proto
    ((js-null-or-undef o)
     (js-throw (make-native-error "TypeError"
                                  (format nil "Cannot read properties of ~a (reading '~a')"
                                          (if (eq o *null*) "null" "undefined")
                                          (if (js-symbol-p key) (to-symbol-string key) (to-string key))))))
    (t (primitive-get o key (if (eq receiver o) o receiver)))))

(defun primitive-get (o key receiver)
  "[[Get]] on a primitive value: strings expose length + integer indices without
   allocating a wrapper; otherwise dispatch to the primitive's prototype."
  (declare (ignore receiver))
  (when (stringp o)
    (let ((k (prop-key key)))
      (cond ((and (stringp k) (string= k "length")) (return-from primitive-get (float (length o) 1d0)))
            ((and (stringp k) (array-index-string-p k))
             (let ((i (parse-integer k)))
               (return-from primitive-get
                 (if (< i (length o)) (string (char o i)) *undefined*)))))))
  (let ((proto (primitive-proto o)))
    (if (js-object-p proto) (js-get proto key o) *undefined*)))

(defun primitive-proto (v)
  "The prototype an unboxed primitive dispatches to (from the current realm)."
  (when (boundp '*current-realm*)
    (let ((r (symbol-value '*current-realm*)))
      (cond ((stringp v) (realm-string-proto r))
            ((floatp v) (realm-number-proto r))
            ((or (eq v *true*) (eq v *false*)) (realm-boolean-proto r))
            ((js-symbol-p v) (realm-symbol-proto r))
            ((js-bigint-p v) (or (getf (realm-intrinsics r) :bigint-proto) *null*))
            (t *null*)))))

;;; ---- UTF-16 code-unit string helpers -------------------------------------
;;; A JS string is a CL string whose every character is a UTF-16 code UNIT
;;; (0x0000..0xFFFF, lone surrogates allowed). An astral scalar value (> 0xFFFF)
;;; is stored as a surrogate PAIR of two CL chars. These are the ENCODE/DECODE
;;; boundary helpers; use them wherever a string is built from, or read back to,
;;; Unicode code points.
(defun utf16-encode-cp (cp)
  "A CL string of the UTF-16 code unit(s) encoding scalar value CP: one char for
   a BMP scalar (incl. lone surrogate values), a surrogate pair for astral."
  (if (<= cp #xFFFF)
      (string (code-char cp))
      (let ((v (- cp #x10000)) (s (make-string 2)))
        (setf (char s 0) (code-char (+ #xD800 (ash v -10)))
              (char s 1) (code-char (+ #xDC00 (logand v #x3FF))))
        s)))

(defun string-from-code-points (cps)
  "Concatenate the UTF-16 encodings of a list of scalar values CPS."
  (let ((out (make-string-output-stream)))
    (dolist (cp cps) (write-string (utf16-encode-cp cp) out))
    (get-output-stream-string out)))

(defun code-point-at (str i)
  "Decode the code point beginning at code-unit index I of STR. Returns
   (values code-point units-consumed): a high surrogate at I followed by a low
   surrogate combines to an astral scalar (2 units); otherwise the lone unit."
  (let ((cc (char-code (char str i))))
    (if (and (<= #xD800 cc #xDBFF) (< (1+ i) (length str))
             (<= #xDC00 (char-code (char str (1+ i))) #xDFFF))
        (values (+ #x10000 (ash (- cc #xD800) 10) (- (char-code (char str (1+ i))) #xDC00)) 2)
        (values cc 1))))

(defun js-array-p (o) (and (js-object-p o) (string= (js-object-class o) "Array")))
(defun to-uint32 (v)
  (let ((n (to-number v)))
    (if (or (js-nan-p n) (= n *inf*) (= n *-inf*)) 0 (mod (truncate n) #x100000000))))
(defun array-length (o)
  (let ((ld (props-get o "length"))) (if ld (truncate (prop-value ld)) 0)))

(defun %array-indices->=  (o newlen)
  "Present own array-index integers of O that are >= NEWLEN, in DESCENDING order.
   Iterates the property table (not the 0..2^32 range), so shrinking a sparse
   array is cheap regardless of how large its length is."
  (let ((idxs '()))
    (map-props o (lambda (k v) (declare (ignore v))
                   (when (and (stringp k) (array-index-string-p k))
                     (let ((i (parse-integer k))) (when (>= i newlen) (push i idxs))))))
    (sort idxs #'>)))

(defun array-set-length (o v)
  "Array exotic [[Set]] \"length\": coerce to uint32 (RangeError on mismatch);
   when shrinking, delete indices >= new length (highest first, honoring
   non-configurable), then store the new length."
  (let* ((num (to-number v)) (newlen (to-uint32 v)))
    (unless (= newlen num) (js-throw (make-native-error "RangeError" "Invalid array length")))
    (let ((ld (props-get o "length")))
      (when (and ld (not (prop-writable ld))) (return-from array-set-length *false*))
      (let ((oldlen (if ld (truncate (prop-value ld)) 0)))
        (when (< newlen oldlen)
          (dolist (i (%array-indices->= o newlen))
            (let ((k (princ-to-string i)) (d nil))
              (setf d (props-get o k))
              (if (prop-configurable d)
                  (progn (props-remove o k) (%key-forget o k))
                  (progn (when ld (setf (prop-value ld) (float (1+ i) 1d0)))
                         (return-from array-set-length *false*))))))
        (if ld (setf (prop-value ld) (float newlen 1d0))
            (put o "length" (float newlen 1d0) :enumerable nil))
        *true*))))

(defun array-index-inherited-blocker-p (o k)
  "T if K resolves on O's prototype chain to an accessor or a non-writable data
   property, OR the chain contains an exotic object (Proxy / anything with its own
   [[Set]] / [[GetOwnProperty]] internal trap) — cases where the fast index write
   must NOT just create an own data prop, but fall through to the ordinary
   proto-walk so an inherited setter / a proxy trap runs."
  (loop for p = (js-object-proto o) then (js-object-proto p)
        while (js-object-p p)
        do (let ((int (js-object-internal p)))
             (when (and int (or (getf int :set) (getf int :get-own-property)
                                (getf int :get-proto)))
               (return t)))
           (let ((d (props-get p k)))
             (when d (return (or (prop-accessor d) (not (prop-writable d))))))))

(defun ordinary-set (o key v &optional receiver)
  ;; OrdinarySet with the receiver walk: an own data prop on RECEIVER is written;
  ;; an inherited accessor's setter is called with RECEIVER as this.
  (unless receiver (setf receiver o))
  (unless (js-object-p o)
    (when (js-null-or-undef o)
      (js-throw (make-native-error "TypeError" "Cannot set properties of null/undefined")))
    ;; setting on a primitive: walk its proto for an inherited setter, else no-op
    (let ((proto (primitive-proto o)))
      (return-from ordinary-set (if (js-object-p proto) (js-set proto key v o) *false*))))
  ;; ---- Array exotic [[Set]]: length maintenance ----
  ;; Only the length property and the index fast-path (own writable-data /
  ;; absent index that extends length) are special-cased here. An index that
  ;; already holds an own accessor or a non-writable data property falls
  ;; through to the ordinary logic below, so its setter runs / write is rejected.
  (when (and (js-array-p o) (eq o receiver))
    (let ((k (prop-key key)))
      (when (stringp k)
        (cond ((string= k "length") (return-from ordinary-set (array-set-length o v)))
              ((array-index-string-p k)
               (let ((own (props-get o k)))
                 ;; Fast path only when the write lands as an own data prop: own
                 ;; writable-data, or absent-with-no-inherited-blocker. An own
                 ;; accessor/non-writable, or an INHERITED accessor/non-writable,
                 ;; falls through to the ordinary proto-walk (setter runs / reject).
                 (when (or (and own (not (prop-accessor own)) (prop-writable own))
                           (and (null own) (not (array-index-inherited-blocker-p o k))))
                   (let* ((idx (parse-integer k)) (len (array-length o))
                          (ld (props-get o "length")))
                     (when (and ld (not (prop-writable ld)) (>= idx len))
                       (return-from ordinary-set *false*))
                     (let ((res (%create-data-on-receiver o k v)))
                       (when (and (eq res *true*) ld (>= idx len))
                         (setf (prop-value ld) (float (1+ idx) 1d0)))
                       (return-from ordinary-set res))))))))))
  (let* ((k (prop-key key)) (d (props-get o k)))
    (cond
      ((and d (prop-accessor d))
       (let ((s (prop-set d)))
         (if (and s (not (js-undefined-p s)))
             (progn (js-call s receiver (list v)) *true*)
             *false*)))
      ((and d (not (prop-writable d))) *false*)
      (d (if (eq o receiver)
             (progn (setf (prop-value d) v) *true*)
             (%create-data-on-receiver receiver k v)))
      ((js-object-p (js-object-proto o)) (js-set (js-object-proto o) key v receiver))
      ((eq o receiver) (%create-data-on-receiver receiver k v))
      (t (%create-data-on-receiver receiver k v)))))

(defun %create-data-on-receiver (receiver k v)
  (if (js-object-p receiver)
      (let ((ex (props-get receiver k)))
        (cond ((and ex (prop-accessor ex)) *false*)
              ((and ex (not (prop-writable ex))) *false*)
              (ex (setf (prop-value ex) v) *true*)
              ((js-object-extensible receiver)
               (props-set receiver k (make-prop :value v))
               (%key-touch receiver k) *true*)
              (t *false*)))
      *false*))

(defun ordinary-has (o key)
  (let ((k (prop-key key)))
    (or (props-present-p o k)
        (and (js-object-p (js-object-proto o)) (js-truthy* (js-has (js-object-proto o) k))))))
(defun ordinary-delete (o key)
  (let* ((k (prop-key key)) (d (props-get o k)))
    (cond ((null d) *true*)
          ((prop-configurable d) (props-remove o k) (%key-forget o k) *true*)
          (t *false*))))
(defun ordinary-own-keys (o)
  ;; Spec order: integer indices ascending, then string keys in insertion order,
  ;; then symbol keys in insertion order.
  (let ((order (%own-keys-in-order o)) (ints '()) (strs '()) (syms '()))
    (dolist (k order)
      (cond ((js-symbol-p k) (push k syms))
            ((array-index-string-p k) (push k ints))
            (t (push k strs))))
    (nconc (sort (nreverse ints) #'< :key (lambda (s) (parse-integer s)))
           (nreverse strs) (nreverse syms))))

(defun array-index-string-p (k)
  "True iff K is a canonical array index string (0 .. 2^32-2)."
  (and (stringp k) (plusp (length k))
       (or (string= k "0")
           (and (char/= (char k 0) #\0)
                (every #'digit-char-p k)
                (ignore-errors (< (parse-integer k) #xFFFFFFFF))))))

(defun put (o key value &key (enumerable t) (writable t) (configurable t))
  "Define an own data property (internal helper for building intrinsics)."
  (let ((k (prop-key key)))
    (props-set o k
          (make-prop :value value :enumerable enumerable :writable writable :configurable configurable))
    (%key-touch o k))
  o)

(defun put-accessor (o key &key get set (enumerable t) (configurable t))
  "Define an own accessor property (internal helper for building intrinsics)."
  (let ((k (prop-key key)))
    (props-set o k
          (make-prop :accessor t :get get :set set :enumerable enumerable :configurable configurable))
    (%key-touch o k))
  o)

;;; ---- [[GetOwnProperty]] / [[DefineOwnProperty]] (spec descriptor ops) ----
(defun js-get-own-property (o key)
  "Return the own PROP descriptor for KEY, or NIL. Honors host GET-OWN traps."
  (when (js-object-p o)
    (let ((tr (and (js-object-internal o) (getf (js-object-internal o) :get-own-property))))
      (if tr (funcall tr o (prop-key key))
          (props-get o (prop-key key))))))

(defun array-define-length (o desc)
  "ArraySetLength(A, Desc): the Array exotic [[DefineOwnProperty]] for \"length\".
   Returns T/NIL."
  ;; No [[Value]] field: only attributes change (writable/enumerable/configurable).
  (unless (present-p desc :value)
    (return-from array-define-length (ordinary-define-own-property o "length" desc)))
  (let* ((val (getf desc :value))
         (newlen (to-uint32 val))
         (numlen (to-number val)))
    (unless (= newlen numlen) (js-throw (make-native-error "RangeError" "Invalid array length")))
    (let* ((ld (props-get o "length"))
           (oldlen (if ld (truncate (prop-value ld)) 0))
           ;; newLenDesc: same as desc but value coerced to newlen
           (newdesc (let ((d (copy-list desc))) (setf (getf d :value) (float newlen 1d0)) d)))
      (when (>= newlen oldlen)
        (return-from array-define-length (ordinary-define-own-property o "length" newdesc)))
      (when (and ld (not (prop-writable ld)))
        (return-from array-define-length nil))
      ;; Decide new writability; defer making it non-writable until after shrink.
      (let ((new-writable (or (not (present-p newdesc :writable)) (getf newdesc :writable))))
        (unless new-writable (setf (getf newdesc :writable) t))
        (unless (ordinary-define-own-property o "length" newdesc)
          (return-from array-define-length nil))
        ;; Delete present indices >= newlen, highest first, honoring
        ;; non-configurable. Iterate existing keys only (sparse-safe).
        (dolist (i (%array-indices->= o newlen))
          (let* ((kk (princ-to-string i)) (d (props-get o kk)))
            (if (prop-configurable d)
                (progn (props-remove o kk) (%key-forget o kk))
                (progn
                  (let ((ld2 (props-get o "length")))
                    (when ld2 (setf (prop-value ld2) (float (1+ i) 1d0))))
                  (unless new-writable
                    (ordinary-define-own-property o "length" (list :writable nil)))
                  (return-from array-define-length nil)))))
        (unless new-writable
          (ordinary-define-own-property o "length" (list :writable nil)))
        t))))

(defun array-define-own-property (o key desc)
  "Array exotic [[DefineOwnProperty]]: special-cases \"length\" and array indices."
  (let ((k (prop-key key)))
    (cond
      ((and (stringp k) (string= k "length")) (array-define-length o desc))
      ((and (stringp k) (array-index-string-p k))
       (let* ((index (parse-integer k))
              (ld (props-get o "length"))
              (oldlen (if ld (truncate (prop-value ld)) 0)))
         (when (and (>= index oldlen) ld (not (prop-writable ld)))
           (return-from array-define-own-property nil))
         (unless (ordinary-define-own-property o k desc)
           (return-from array-define-own-property nil))
         (when (>= index oldlen)
           (let ((ld2 (props-get o "length")))
             (if ld2 (setf (prop-value ld2) (float (1+ index) 1d0))
                 (put o "length" (float (1+ index) 1d0) :enumerable nil))))
         t))
      (t (ordinary-define-own-property o k desc)))))

(defun js-define-own-property (o key desc)
  "[[DefineOwnProperty]]. DESC is a PROP-like plist of the FIELDS THAT ARE
   PRESENT (:value/:get/:set/:writable/:enumerable/:configurable/:accessor).
   Returns T on success, NIL on rejection (caller decides throw vs silent)."
  (let ((tr (and (js-object-internal o) (getf (js-object-internal o) :define-own-property))))
    (when tr (return-from js-define-own-property (funcall tr o (prop-key key) desc))))
  (when (js-array-p o)
    (return-from js-define-own-property (array-define-own-property o key desc)))
  (ordinary-define-own-property o key desc))

(defun ordinary-define-own-property (o key desc)
  "OrdinaryDefineOwnProperty (no exotic dispatch). Returns T/NIL."
  (let* ((k (prop-key key)) (cur (props-get o k))
         (accessor (if (present-p desc :accessor) (getf desc :accessor)
                       (or (present-p desc :get) (present-p desc :set)))))
    (cond
      ;; new property
      ((null cur)
       (unless (js-object-extensible o) (return-from ordinary-define-own-property nil))
       (let ((p (if accessor
                    (make-prop :accessor t
                               :get (if (present-p desc :get) (getf desc :get) *undefined*)
                               :set (if (present-p desc :set) (getf desc :set) *undefined*)
                               :enumerable (and (present-p desc :enumerable) (getf desc :enumerable))
                               :configurable (and (present-p desc :configurable) (getf desc :configurable)))
                    (make-prop :value (if (present-p desc :value) (getf desc :value) *undefined*)
                               :writable (and (present-p desc :writable) (getf desc :writable))
                               :enumerable (and (present-p desc :enumerable) (getf desc :enumerable))
                               :configurable (and (present-p desc :configurable) (getf desc :configurable))))))
         (props-set o k p) (%key-touch o k) t))
      ;; existing property — validate against configurable
      ;; (ValidateAndApplyPropertyDescriptor). DESC's descriptor "kind":
      ;;   data     = has :value or :writable
      ;;   accessor = has :get or :set
      ;;   generic  = neither (only enumerable/configurable, or empty)
      (t
       (let* ((cfg (prop-configurable cur))
              (desc-data (or (present-p desc :value) (present-p desc :writable)))
              (desc-acc  (or (present-p desc :get) (present-p desc :set)))
              (cur-acc   (prop-accessor cur)))
         ;; reject illegal changes on a non-configurable property
         (when (not cfg)
           (when (and (present-p desc :configurable) (getf desc :configurable))
             (return-from ordinary-define-own-property nil))
           (when (and (present-p desc :enumerable)
                      (not (eq (and (getf desc :enumerable) t) (prop-enumerable cur))))
             (return-from ordinary-define-own-property nil))
           ;; changing the descriptor kind (data<->accessor) is forbidden
           (when (or (and desc-acc (not cur-acc)) (and desc-data cur-acc))
             (return-from ordinary-define-own-property nil))
           (if cur-acc
               (progn
                 (when (and (present-p desc :get) (not (eq (getf desc :get) (or (prop-get cur) *undefined*))))
                   (return-from ordinary-define-own-property nil))
                 (when (and (present-p desc :set) (not (eq (getf desc :set) (or (prop-set cur) *undefined*))))
                   (return-from ordinary-define-own-property nil)))
               ;; current is data; if also non-writable, value/writable are locked
               (when (not (prop-writable cur))
                 (when (and (present-p desc :writable) (getf desc :writable))
                   (return-from ordinary-define-own-property nil))
                 (when (and (present-p desc :value)
                            (not (same-value (getf desc :value) (prop-value cur))))
                   (return-from ordinary-define-own-property nil)))))
         ;; apply — first, a kind change resets the unrelated fields to defaults
         (when (and desc-acc (not cur-acc))
           (setf (prop-accessor cur) t (prop-value cur) *undefined* (prop-writable cur) nil
                 (prop-get cur) *undefined* (prop-set cur) *undefined*))
         (when (and desc-data cur-acc)
           (setf (prop-accessor cur) nil (prop-get cur) nil (prop-set cur) nil
                 (prop-value cur) *undefined* (prop-writable cur) nil))
         (when (present-p desc :get) (setf (prop-get cur) (getf desc :get)))
         (when (present-p desc :set) (setf (prop-set cur) (getf desc :set)))
         (when (present-p desc :value) (setf (prop-value cur) (getf desc :value)))
         (when (present-p desc :writable) (setf (prop-writable cur) (and (getf desc :writable) t)))
         (when (present-p desc :enumerable) (setf (prop-enumerable cur) (and (getf desc :enumerable) t)))
         (when (present-p desc :configurable) (setf (prop-configurable cur) (and (getf desc :configurable) t)))
         t)))))

(defparameter +absent+ '#:absent)
(defun present-p (plist key) (not (eq (getf plist key +absent+) +absent+)))

;;; ---- [[Call]] / [[Construct]] ----
(defun js-callable-p (f) (and (js-object-p f) (js-object-call f)))
(defparameter *max-depth* 900) (defvar *depth* 0)   ; bound JS recursion before the CL stack overflows
(defvar *new-target* *undefined*)   ; [[NewTarget]] of the running fn env: the ctor when `new`'d, undefined on a plain [[Call]]
(defun js-call (f this args)
  (unless (js-callable-p f) (js-throw (make-native-error "TypeError" (format nil "~a is not a function" (to-string f)))))
  (let ((*depth* (1+ *depth*)) (*new-target* *undefined*))   ; an ordinary [[Call]] => new.target is undefined
    (when (> *depth* *max-depth*) (js-throw (make-native-error "RangeError" "Maximum call stack size exceeded")))
    (funcall (js-object-call f) this args)))
(defun js-construct (f args &optional (new-target f))
  (unless (and (js-object-p f) (js-object-construct f))
    (js-throw (make-native-error "TypeError" (format nil "~a is not a constructor" (to-string f)))))
  (let ((*new-target* new-target))    ; [[Construct]] => new.target is the newTarget ctor
    (funcall (js-object-construct f) args new-target)))

;;; ===========================================================================
;;; Abstract operations (spec coercions)
;;; ===========================================================================
(defun js-truthy (v)
  (cond ((eq v *true*) t) ((member v (list *false* *undefined* *null*)) nil)
        ((stringp v) (plusp (length v)))
        ((floatp v) (not (or (zerop v) (js-nan-p v))))
        ((js-bigint-p v) (not (zerop v)))
        (t t)))
(defun to-boolean (v) (js-bool (js-truthy v)))

(defvar *symbol-to-primitive* nil)   ; the @@toPrimitive well-known symbol (set at realm build)
(defun to-primitive (v &optional hint)
  (if (js-object-p v)
      (progn
        ;; @@toPrimitive via GetMethod: undefined OR null -> absent (fall through
        ;; to OrdinaryToPrimitive); present-but-not-callable -> TypeError.
        (when *symbol-to-primitive*
          (let ((exotic (js-get v *symbol-to-primitive*)))
            (unless (js-null-or-undef exotic)
              (unless (js-callable-p exotic)
                (js-throw (make-native-error "TypeError" "Symbol.toPrimitive is not a function")))
              (let ((r (js-call exotic v (list (case hint (:string "string") (:number "number") (t "default"))))))
                (if (js-object-p r)
                    (js-throw (make-native-error "TypeError" "Cannot convert object to primitive value"))
                    (return-from to-primitive r))))))
        (let ((order (if (eq hint :string) '("toString" "valueOf") '("valueOf" "toString"))))
          (dolist (m order (js-throw (make-native-error "TypeError" "Cannot convert object to primitive value")))
            (let ((fn (js-get v m)))
              (when (js-callable-p fn)
                (let ((r (js-call fn v '()))) (unless (js-object-p r) (return r))))))))
      v))

(defun to-number (v)
  (cond ((floatp v) v)
        ((eq v *true*) 1d0) ((eq v *false*) 0d0)
        ((eq v *null*) 0d0) ((eq v *undefined*) *nan*)
        ((stringp v) (string-to-number v))
        ((js-bigint-p v) (js-throw (make-native-error "TypeError" "Cannot convert a BigInt value to a number")))
        ((js-symbol-p v) (js-throw (make-native-error "TypeError" "Cannot convert a Symbol value to a number")))
        ((js-object-p v) (to-number (to-primitive v :number)))
        (t *nan*)))

(defparameter +js-ws+
  (list #\Space #\Tab #\Newline #\Return #\Page #\Vt          ; TAB VT FF SP + LF CR
        #\No-Break_Space                                       ; U+00A0
        #\Line_Separator #\Paragraph_Separator                 ; U+2028 U+2029
        #\U+FEFF                                                ; ZWNBSP (BOM)
        (code-char #x1680)                                     ; OGHAM SPACE MARK
        (code-char #x2000) (code-char #x2001) (code-char #x2002) (code-char #x2003)
        (code-char #x2004) (code-char #x2005) (code-char #x2006) (code-char #x2007)
        (code-char #x2008) (code-char #x2009) (code-char #x200A) ; EN QUAD .. HAIR SPACE
        (code-char #x202F)                                     ; NARROW NO-BREAK SPACE
        (code-char #x205F)                                     ; MEDIUM MATHEMATICAL SPACE
        (code-char #x3000)))                                   ; IDEOGRAPHIC SPACE
(defun string-to-number (s)
  (let ((s (string-trim +js-ws+ s)))
    (cond ((string= s "") 0d0)
          ((or (string= s "Infinity") (string= s "+Infinity")) *inf*)
          ((string= s "-Infinity") *-inf*)
          ;; radix literals (no sign allowed per StringNumericLiteral)
          ((and (>= (length s) 2) (char= (char s 0) #\0) (member (char s 1) '(#\x #\X)))
           (or (ignore-errors (float (parse-integer s :start 2 :radix 16) 1d0)) *nan*))
          ((and (>= (length s) 2) (char= (char s 0) #\0) (member (char s 1) '(#\o #\O)))
           (or (ignore-errors (float (parse-integer s :start 2 :radix 8) 1d0)) *nan*))
          ((and (>= (length s) 2) (char= (char s 0) #\0) (member (char s 1) '(#\b #\B)))
           (or (ignore-errors (float (parse-integer s :start 2 :radix 2) 1d0)) *nan*))
          (t (or (parse-js-decimal s) *nan*)))))

(defun %round-half-to-even (num den)
  "Round the exact rational NUM/DEN (DEN > 0) to the nearest integer, ties to even."
  (multiple-value-bind (q rem) (floor num den)
    (let ((twice (* 2 rem)))
      (cond ((< twice den) q)
            ((> twice den) (1+ q))
            (t (if (evenp q) q (1+ q)))))))

(defun rational->double (r)
  "Convert a NON-NEGATIVE exact rational R to the closest double-float, ties to
   even. Correct across normals AND subnormals (unlike CL:COERCE/the reader, which
   mis-round subnormals in SBCL)."
  (when (zerop r) (return-from rational->double 0d0))
  (let* ((num (numerator r)) (den (denominator r))
         ;; approximate floor(log2 r); the loops below correct any off-by-one
         (log2r (- (integer-length num) (integer-length den)))
         (e (max (- log2r 52) -1074)))
    (multiple-value-bind (n d)
        (if (>= e 0) (values num (* den (expt 2 e)))
            (values (* num (expt 2 (- e))) den))
      (let ((sig (%round-half-to-even n d)))
        ;; significand overflowed 2^53 (rounded up): shift right, bump exponent
        (loop while (>= sig (ash 1 53)) do
          (setf d (* d 2) sig (%round-half-to-even n d) e (1+ e)))
        ;; significand too small for a normalized double: shift left (until the
        ;; subnormal floor E = -1074), re-round
        (loop while (and (> e -1074) (< sig (ash 1 52))) do
          (setf e (1- e) n (* n 2) sig (%round-half-to-even n d)))
        ;; overflow: exponent above the max for a finite double -> +Infinity
        (if (> e 971) *inf*
            (handler-case (scale-float (coerce sig 'double-float) e)
              (floating-point-overflow () *inf*)))))))

(defun decimal-string->rational (s)
  "Parse a syntactically-valid JS decimal literal S (sign/digits/'.'/exponent)
   into an exact RATIONAL (or NIL for an all-zero magnitude). No rounding."
  (let ((n (length s)) (i 0) (sign 1) (int-part 0) (frac-digits 0) (frac 0) (exp 0))
    (when (and (< i n) (member (char s i) '(#\+ #\-)))
      (when (char= (char s i) #\-) (setf sign -1)) (incf i))
    (loop while (and (< i n) (digit-char-p (char s i)))
          do (setf int-part (+ (* int-part 10) (digit-char-p (char s i)))) (incf i))
    (when (and (< i n) (char= (char s i) #\.))
      (incf i)
      (loop while (and (< i n) (digit-char-p (char s i)))
            do (setf frac (+ (* frac 10) (digit-char-p (char s i)))) (incf frac-digits) (incf i)))
    (when (and (< i n) (member (char s i) '(#\e #\E)))
      (incf i)
      (let ((esign 1))
        (when (and (< i n) (member (char s i) '(#\+ #\-)))
          (when (char= (char s i) #\-) (setf esign -1)) (incf i))
        (loop while (and (< i n) (digit-char-p (char s i)))
              do (setf exp (+ (* exp 10) (digit-char-p (char s i)))) (incf i))
        (setf exp (* esign exp))))
    (let* ((mant (+ int-part (/ frac (expt 10 frac-digits))))
           (val (* mant (expt 10 exp))))
      (if (zerop val) nil (* sign val)))))

(defun parse-js-decimal (s)
  "Parse a JS decimal StringNumericLiteral (optional sign, digits, '.', exponent).
   Returns a double-float or NIL. Rejects trailing junk; '' handled by caller."
  (let ((n (length s)) (i 0) (sign 1d0) (seen-digit nil))
    (when (and (< i n) (member (char s i) '(#\+ #\-)))
      (when (char= (char s i) #\-) (setf sign -1d0)) (incf i))
    (let ((mant-start i))
      (loop while (and (< i n) (digit-char-p (char s i))) do (incf i) (setf seen-digit t))
      (when (and (< i n) (char= (char s i) #\.))
        (incf i)
        (loop while (and (< i n) (digit-char-p (char s i))) do (incf i) (setf seen-digit t)))
      (unless seen-digit (return-from parse-js-decimal nil))
      (progn mant-start)
      (progn
        (when (and (< i n) (member (char s i) '(#\e #\E)))
          (incf i)
          (when (and (< i n) (member (char s i) '(#\+ #\-))) (incf i))
          (let ((exp-digit nil))
            (loop while (and (< i n) (digit-char-p (char s i))) do (incf i) (setf exp-digit t))
            (unless exp-digit (return-from parse-js-decimal nil))))
        (unless (= i n) (return-from parse-js-decimal nil))
        ;; Build an exact rational from the (already syntax-validated) digits and
        ;; exponent, then round-to-nearest-even to a double. This is correctly
        ;; rounded across the whole range INCLUDING subnormals, where SBCL's own
        ;; reader / rational->float coercion mis-rounds. Overflow -> +/-Infinity.
        (with-js-floats
          (let ((r (decimal-string->rational s)))
            (if (null r) (* sign 0d0)
                (let ((mag (rational->double (abs r))))
                  (if (> mag most-positive-double-float) (* sign *inf*)
                      (* sign mag))))))))))

(defun number-to-string (n)
  (cond ((js-nan-p n) "NaN") ((= n *inf*) "Infinity") ((= n *-inf*) "-Infinity")
        ((zerop n) "0")                                    ; both +0 and -0 -> "0"
        ((minusp n) (concatenate 'string "-" (number-to-string (- n))))
        ((= n (with-js-floats (ftruncate n)))
         ;; Integer-valued double: route through the shortest round-tripping
         ;; path so e.g. 1000000000000000128 -> "1000000000000000100" (the
         ;; shortest decimal that reads back to the same double), rather than
         ;; the full exact integer. >=1e21 uses exponential per spec.
         (if (< n 1d21) (dtoa n) (dtoa-exponential n)))
        (t (dtoa n))))

(defun dtoa (n)
  "Shortest round-tripping decimal for a positive finite non-integer double,
   in ECMAScript Number::toString format (fixed vs exponential by magnitude)."
  ;; SBCL's float printer already emits a shortest round-tripping representation.
  (let* ((s (let ((*read-default-float-format* 'double-float)) (prin1-to-string n))))
    ;; s looks like "12.34" or "1.234e10" or "1.0e-5"; normalise to JS.
    (let* ((epos (position #\e s))
           (mant (if epos (subseq s 0 epos) s))
           (exp (if epos (parse-integer s :start (1+ epos)) 0)))
      ;; strip a trailing ".0"
      (when (and (> (length mant) 1) (string= mant ".0" :start1 (- (length mant) 2)))
        (setf mant (subseq mant 0 (- (length mant) 2))))
      (js-format-decimal mant exp))))

(defun dtoa-exponential (n)
  (let ((s (let ((*read-default-float-format* 'double-float)) (prin1-to-string n))))
    (let* ((epos (position #\e s))
           (mant (if epos (subseq s 0 epos) s))
           (exp (if epos (parse-integer s :start (1+ epos)) 0)))
      (js-format-decimal mant exp))))

(defun js-format-decimal (mant exp)
  "Assemble a JS number string from a decimal mantissa string MANT (may contain a
   '.') and base-10 EXP. Chooses fixed vs 'e' notation like ECMAScript does."
  ;; collect significant digits and the position of the decimal point
  (let* ((dot (position #\. mant))
         (digits (remove #\. mant))
         (int-len (if dot dot (length mant)))
         ;; k = number of significant digits, n = exponent so value = digits * 10^(n-k)
         (trimmed (string-right-trim "0" digits)))
    (when (string= trimmed "") (setf trimmed "0"))
    ;; leading zeros -> adjust
    (let* ((lead (or (position-if (lambda (c) (char/= c #\0)) trimmed) 0))
           (sig (subseq trimmed lead))
           (k (length sig))
           (n (+ (- int-len lead) exp)))
      (when (string= sig "") (return-from js-format-decimal "0"))
      (cond
        ((<= k n 21)                     ; integer, pad with zeros
         (concatenate 'string sig (make-string (- n k) :initial-element #\0)))
        ((< 0 n 21)                      ; digits with a decimal point inside
         (concatenate 'string (subseq sig 0 n) "." (subseq sig n)))
        ((< -6 n 1)                      ; 0.00…digits
         (concatenate 'string "0." (make-string (- n) :initial-element #\0) sig))
        (t                               ; exponential
         (let ((e (1- n)))
           (concatenate 'string (subseq sig 0 1)
                        (if (> k 1) (concatenate 'string "." (subseq sig 1)) "")
                        "e" (if (minusp e) "-" "+") (format nil "~d" (abs e)))))))))

(defun to-string (v)
  (cond ((stringp v) v) ((floatp v) (number-to-string v))
        ((js-bigint-p v) (bigint-to-string v))
        ((eq v *undefined*) "undefined") ((eq v *null*) "null")
        ((eq v *true*) "true") ((eq v *false*) "false")
        ((js-symbol-p v) (js-throw (make-native-error "TypeError" "Cannot convert a Symbol value to a string")))
        ((js-object-p v) (to-string (to-primitive v :string)))
        (t (princ-to-string v))))

(defun js-typeof (v)
  (cond ((eq v *undefined*) "undefined")
        ((or (eq v *true*) (eq v *false*)) "boolean")
        ((floatp v) "number") ((stringp v) "string")
        ((js-bigint-p v) "bigint")
        ((js-symbol-p v) "symbol")
        ((eq v *null*) "object")
        ((js-callable-p v) "function")
        ((js-object-p v) "object") (t "object")))

;;; ---- BigInt conversions (a BigInt value is a CL integer) ----
(defun bigint-to-string (b &optional (radix 10))
  "BigInt::toString — decimal (or RADIX 2..36), lowercase digits."
  (if (= radix 10) (princ-to-string b)
      (let ((s (string-downcase (write-to-string (abs b) :base radix))))
        (if (minusp b) (concatenate 'string "-" s) s))))

(defun string-to-bigint (s)
  "StringToBigInt: trim JS whitespace; empty/ws -> 0n; integer syntax incl
   0x/0o/0b (no sign on radix forms); a decimal may carry a leading +/-.
   Invalid -> :syntax-error (caller raises SyntaxError). No fractional/exponent."
  (let ((s (string-trim +js-ws+ s)))
    (cond
      ((string= s "") 0)
      ((and (>= (length s) 2) (char= (char s 0) #\0) (member (char s 1) '(#\x #\X)))
       (or (and (> (length s) 2) (every (lambda (c) (digit-char-p c 16)) (subseq s 2))
                (parse-integer s :start 2 :radix 16))
           :syntax-error))
      ((and (>= (length s) 2) (char= (char s 0) #\0) (member (char s 1) '(#\o #\O)))
       (or (and (> (length s) 2) (every (lambda (c) (digit-char-p c 8)) (subseq s 2))
                (parse-integer s :start 2 :radix 8))
           :syntax-error))
      ((and (>= (length s) 2) (char= (char s 0) #\0) (member (char s 1) '(#\b #\B)))
       (or (and (> (length s) 2) (every (lambda (c) (digit-char-p c 2)) (subseq s 2))
                (parse-integer s :start 2 :radix 2))
           :syntax-error))
      (t
       (let* ((neg (char= (char s 0) #\-))
              (body (if (member (char s 0) '(#\+ #\-)) (subseq s 1) s)))
         (if (and (plusp (length body)) (every #'digit-char-p body))
             (let ((v (parse-integer body))) (if neg (- v) v))
             :syntax-error))))))

(defun to-bigint (v)
  "ToBigInt(v). boolean->1/0; string->StringToBigInt (SyntaxError on invalid);
   bigint->itself; number/undefined/null/symbol->TypeError; object->
   ToPrimitive(number) then ToBigInt."
  (cond
    ((js-bigint-p v) v)
    ((eq v *true*) 1) ((eq v *false*) 0)
    ((stringp v)
     (let ((r (string-to-bigint v)))
       (if (eq r :syntax-error)
           (js-throw (make-native-error "SyntaxError"
                       (format nil "Cannot convert ~a to a BigInt" v)))
           r)))
    ((floatp v) (js-throw (make-native-error "TypeError" "Cannot convert a Number to a BigInt")))
    ((js-null-or-undef v)
     (js-throw (make-native-error "TypeError"
                 (format nil "Cannot convert ~a to a BigInt" (if (eq v *null*) "null" "undefined")))))
    ((js-symbol-p v) (js-throw (make-native-error "TypeError" "Cannot convert a Symbol value to a BigInt")))
    ((js-object-p v) (to-bigint (to-primitive v :number)))
    (t (js-throw (make-native-error "TypeError" "Cannot convert value to a BigInt")))))

(defun js-strict-equal (a b)
  (cond ((and (floatp a) (floatp b)) (and (not (js-nan-p a)) (not (js-nan-p b)) (= a b)))
        ((and (stringp a) (stringp b)) (string= a b))
        ((and (js-bigint-p a) (js-bigint-p b)) (= a b))   ; same type required; mixed -> not covered here
        (t (eq a b))))

(defun bigint-number-equal (bi num)
  "Mathematically-exact BigInt == Number (no rounding). NaN/Inf -> not equal."
  (and (floatp num) (not (js-nan-p num)) (/= num *inf*) (/= num *-inf*)
       (= num (with-js-floats (ftruncate num)))   ; a non-integer number can't equal a bigint
       (= bi (truncate num))))

(defun js-equal (a b)             ; loose == (the common cases)
  (cond ((or (js-null-or-undef a) (js-null-or-undef b))   ; null/undefined only equal each other
         (and (js-null-or-undef a) (js-null-or-undef b) t))
        ((js-strict-equal a b) t)
        ((and (floatp a) (stringp b)) (js-strict-equal a (to-number b)))
        ((and (stringp a) (floatp b)) (js-strict-equal (to-number a) b))
        ;; BigInt <-> Number: exact mathematical comparison
        ((and (js-bigint-p a) (floatp b)) (bigint-number-equal a b))
        ((and (floatp a) (js-bigint-p b)) (bigint-number-equal b a))
        ;; BigInt <-> String: parse the string as a BigInt (invalid -> false)
        ((and (js-bigint-p a) (stringp b))
         (let ((r (string-to-bigint b))) (and (integerp r) (= a r))))
        ((and (stringp a) (js-bigint-p b))
         (let ((r (string-to-bigint a))) (and (integerp r) (= r b))))
        ((or (eq a *true*) (eq a *false*)) (js-equal (to-number a) b))
        ((or (eq b *true*) (eq b *false*)) (js-equal a (to-number b)))
        ((and (js-object-p a) (not (js-object-p b)) (not (js-null-or-undef b))) (js-equal (to-primitive a) b))
        ((and (js-object-p b) (not (js-object-p a)) (not (js-null-or-undef a))) (js-equal a (to-primitive b)))
        (t nil)))
(defun js-null-or-undef (x) (or (eq x *null*) (eq x *undefined*)))

(defun js-add (a b)
  (let ((pa (to-primitive a)) (pb (to-primitive b)))
    (cond
      ;; if either primitive is a String -> string concatenation
      ((or (stringp pa) (stringp pb))
       (concatenate 'string (to-string pa) (to-string pb)))
      ;; both BigInt -> integer addition
      ((and (js-bigint-p pa) (js-bigint-p pb)) (+ pa pb))
      ;; mixing BigInt with a non-string, non-bigint numeric -> TypeError
      ((or (js-bigint-p pa) (js-bigint-p pb))
       (js-throw (make-native-error "TypeError" "Cannot mix BigInt and other types, use explicit conversions")))
      (t (with-js-floats (+ (to-number pa) (to-number pb)))))))

;;; ===========================================================================
;;; More abstract operations (the kernel the built-in library builds on)
;;; ===========================================================================
(declaim (inline js-negative-zero-p))
(defun js-negative-zero-p (x) (and (floatp x) (zerop x) (minusp (float-sign x))))

(defun same-value (a b)
  "SameValue: like ===, but NaN==NaN and +0 != -0."
  (cond ((and (floatp a) (floatp b))
         (cond ((and (js-nan-p a) (js-nan-p b)) t)
               ((and (zerop a) (zerop b)) (eq (js-negative-zero-p a) (js-negative-zero-p b)))
               (t (= a b))))
        ((and (stringp a) (stringp b)) (string= a b))
        ((and (js-bigint-p a) (js-bigint-p b)) (= a b))
        (t (eq a b))))

(defun same-value-zero (a b)
  "SameValueZero: like SameValue but +0 == -0 (used by includes/Set/Map)."
  (cond ((and (floatp a) (floatp b))
         (cond ((and (js-nan-p a) (js-nan-p b)) t) (t (= a b))))
        ((and (stringp a) (stringp b)) (string= a b))
        ((and (js-bigint-p a) (js-bigint-p b)) (= a b))
        (t (eq a b))))

(defun to-symbol-string (sym)
  "String(Symbol) -> \"Symbol(desc)\" (used by String() and description access)."
  (format nil "Symbol(~a)" (or (js-symbol-desc sym) "")))

(defun js-key-name (k)
  "The function-name string for a property key K (already a key: string or symbol).
   A symbol key names the function \"[desc]\" (empty desc -> \"\") per spec; a string
   key passes through. Anything else is ToString'd defensively."
  (cond ((stringp k) k)
        ((js-symbol-p k) (let ((d (js-symbol-desc k))) (if d (format nil "[~a]" d) "")))
        (t (to-string k))))

(defun to-property-key (v)
  "ToPropertyKey: symbols pass through; everything else -> ToString.
   (Objects with Symbol.toPrimitive/toString are coerced via to-primitive.)"
  (cond ((js-symbol-p v) v)
        ((stringp v) v)
        ((js-object-p v) (let ((p (to-primitive v :string))) (if (js-symbol-p p) p (to-string p))))
        (t (to-string v))))

(defun require-object-coercible (v &optional what)
  "RequireObjectCoercible: null/undefined -> TypeError, else pass through."
  (when (js-null-or-undef v)
    (js-throw (make-native-error "TypeError"
                                 (format nil "~a is ~a" (or what "value") (if (eq v *null*) "null" "undefined")))))
  v)

(defun to-integer-or-infinity (v)
  "ToIntegerOrInfinity: NaN->0, +/-Inf kept, else truncate toward zero (a double)."
  (let ((n (to-number v)))
    (cond ((js-nan-p n) 0d0)
          ((or (= n *inf*) (= n *-inf*)) n)
          (t (with-js-floats (ftruncate n))))))

(defun to-length (v)
  "ToLength: clamp ToIntegerOrInfinity to [0, 2^53-1]."
  (let ((n (to-integer-or-infinity v)))
    (cond ((<= n 0) 0d0)
          ((> n 9007199254740991d0) 9007199254740991d0)
          (t n))))

(defun to-int-index (v)
  "A CL integer index from a JS value (for element access / loops)."
  (let ((n (to-integer-or-infinity v)))
    (if (or (= n *inf*) (= n *-inf*)) 0 (truncate n))))

(defun make-native-error (name message)
  "Build a native Error object of the given constructor name in the current realm.
   Used by CL-side abstract ops that must throw the right JS error type."
  (if (boundp '*current-realm*)
      (let* ((realm (symbol-value '*current-realm*))
             (ctor (ignore-errors (js-get (realm-global realm) name))))
        (if (and ctor (js-object-p ctor) (js-object-construct ctor))
            (js-construct ctor (list message))
            message))
      message))

;;; ToObject: primitives box into their wrapper; the realm supplies the protos.
(defun to-object (v)
  (cond ((js-object-p v) v)
        ((js-null-or-undef v)
         (js-throw (make-native-error "TypeError" "Cannot convert undefined or null to object")))
        (t (box-primitive v))))
;; BOX-PRIMITIVE is defined in vm.lisp once realm protos are available.
