;;;; See array-iteration.lisp for the convention + helpers.
;;;;
;;;; A Proxy is an ordinary js-object whose INTERNAL plist entries are closures
;;;; over (target handler revoked-cell). Each closure looks the same-named trap
;;;; up on the handler (GetMethod: undefined OR null => absent, else must be
;;;; callable) and, if present, calls it with (target key ...) coercing the
;;;; result per the [[…]] spec — including the invariant checks test262 pins.
;;;; If absent, it performs the default (Reflect semantics) directly on target.
;;;;
;;;; The core INTERNAL dispatch (value.lisp) covers get/set/has/delete/own-keys/
;;;; get-own-property/define-own-property + [[Call]]/[[Construct]] (via the CALL/
;;;; CONSTRUCT slots), plus getPrototypeOf/setPrototypeOf/isExtensible/
;;;; preventExtensions via js-get-proto/js-set-proto/js-extensible-p/
;;;; js-prevent-extensions (wired to the :get-proto/:set-proto/:is-extensible/
;;;; :prevent-extensions internal keys). Every default-forwarding branch calls
;;;; those dispatchers on the target (never the raw struct slots) so nested-proxy
;;;; targets forward correctly.
(in-package #:shuttle)

;;; ---------------------------------------------------------------------------
;;; helpers
;;; ---------------------------------------------------------------------------
(defun %proxy-throw (msg) (js-throw (make-native-error "TypeError" msg)))

(defun %get-trap (handler name)
  "GetMethod(handler, name): NIL if the trap is undefined or null; a TypeError
   if present-but-not-callable; otherwise the callable trap."
  (let ((tr (js-get handler name)))
    (cond ((or (js-undefined-p tr) (eq tr *null*)) nil)
          ((js-callable-p tr) tr)
          (t (%proxy-throw (format nil "'~a' trap is not a function" name))))))

(defmacro %proxy-guard (revoked-cell)
  "Throw if this proxy has been revoked (handler cleared)."
  `(when (car ,revoked-cell)
     (%proxy-throw "Cannot perform operation on a revoked proxy")))

(defun %pk (key)
  "Normalize a property key to a String or Symbol (ToPropertyKey). A trap always
   receives a String|Symbol per spec, but core's internal-method dispatch may
   hand us a raw number (e.g. `proxy[10]`) — coerce it so the trap sees \"10\",
   not the number 10. Strings and Symbols pass through unchanged."
  (if (or (stringp key) (js-symbol-p key)) key (prop-key key)))

(defun %prop-to-desc-plist (prop)
  "PROP struct -> a to-property-descriptor-style plist (all fields present)."
  (if (prop-accessor prop)
      (list :accessor t
            :get (or (prop-get prop) *undefined*) :set (or (prop-set prop) *undefined*)
            :enumerable (prop-enumerable prop) :configurable (prop-configurable prop))
      (list :value (prop-value prop) :writable (prop-writable prop)
            :enumerable (prop-enumerable prop) :configurable (prop-configurable prop))))

;;; ---------------------------------------------------------------------------
;;; the trap closures — one per internal method
;;; ---------------------------------------------------------------------------
(defun %make-proxy-internal (realm target handler revoked-cell)
  "Build the INTERNAL plist for a proxy over TARGET with HANDLER."
  (let ((internal '()))
    ;; ---- [[Get]] ----
    (setf (getf internal :get)
          (lambda (o key &optional receiver)
            (declare (ignore o))
            (%proxy-guard revoked-cell)
            (setf key (%pk key))
            (let ((tr (%get-trap handler "get")) (rcv (or receiver o)))
              (if (null tr)
                  (js-get target key rcv)
                  (let ((result (js-call tr handler (list target key rcv))))
                    ;; invariant: non-configurable non-writable data prop must match
                    (let ((td (js-get-own-property target key)))
                      (when (and td (not (prop-configurable td)))
                        (if (not (prop-accessor td))
                            (unless (prop-writable td)
                              (unless (same-value result (prop-value td))
                                (%proxy-throw "proxy get: non-configurable non-writable property value mismatch")))
                            (when (or (null (prop-get td)) (js-undefined-p (prop-get td)))
                              (unless (js-undefined-p result)
                                (%proxy-throw "proxy get: non-configurable accessor with undefined getter must return undefined"))))))
                    result)))))
    ;; ---- [[Set]] ----
    (setf (getf internal :set)
          (lambda (o key v &optional receiver)
            (declare (ignore o))
            (%proxy-guard revoked-cell)
            (setf key (%pk key))
            (let ((tr (%get-trap handler "set")) (rcv (or receiver o)))
              (if (null tr)
                  ;; default [[Set]] = OrdinarySet(target,key,v,receiver=proxy).
                  (%proxy-default-set target key v rcv o)
                  (let ((ok (js-truthy (js-call tr handler (list target key v rcv)))))
                    (when ok
                      (let ((td (js-get-own-property target key)))
                        (when (and td (not (prop-configurable td)))
                          (if (not (prop-accessor td))
                              (when (not (prop-writable td))
                                (unless (same-value v (prop-value td))
                                  (%proxy-throw "proxy set: cannot change non-configurable non-writable data property")))
                              (when (or (null (prop-set td)) (js-undefined-p (prop-set td)))
                                (%proxy-throw "proxy set: cannot set through non-configurable accessor with undefined setter"))))))
                    (js-bool ok))))))
    ;; ---- [[Has]] ----
    (setf (getf internal :has)
          (lambda (o key)
            (declare (ignore o))
            (%proxy-guard revoked-cell)
            (setf key (%pk key))
            (let ((tr (%get-trap handler "has")))
              (if (null tr)
                  ;; return a CL boolean to match ordinary-has (the `in` operator
                  ;; and ordinary-has proto-walk both treat js-has as CL-boolean).
                  (js-truthy* (js-has target key))
                  (let ((present (js-truthy (js-call tr handler (list target key)))))
                    (unless present
                      (let ((td (js-get-own-property target key)))
                        (when td
                          (when (not (prop-configurable td))
                            (%proxy-throw "proxy has: cannot report non-configurable property as non-existent"))
                          (unless (js-extensible-p target)
                            (%proxy-throw "proxy has: cannot report existing property of non-extensible target as non-existent")))))
                    present)))))
    ;; ---- [[Delete]] ----
    (setf (getf internal :delete)
          (lambda (o key)
            (declare (ignore o))
            (%proxy-guard revoked-cell)
            (setf key (%pk key))
            (let ((tr (%get-trap handler "deleteProperty")))
              (if (null tr)
                  (js-delete target key)
                  (let ((ok (js-truthy (js-call tr handler (list target key)))))
                    (when ok
                      (let ((td (js-get-own-property target key)))
                        (when td
                          (when (not (prop-configurable td))
                            (%proxy-throw "proxy deleteProperty: cannot delete non-configurable property"))
                          (unless (js-extensible-p target)
                            (%proxy-throw "proxy deleteProperty: cannot delete property of non-extensible target")))))
                    (js-bool ok))))))
    ;; ---- [[OwnPropertyKeys]] ----
    (setf (getf internal :own-keys)
          (lambda (o)
            (declare (ignore o))
            (%proxy-guard revoked-cell)
            (let ((tr (%get-trap handler "ownKeys")))
              (if (null tr)
                  (js-own-keys target)
                  (let* ((res (js-call tr handler (list target)))
                         (keys (%proxy-own-keys-list res)))
                    (%proxy-check-own-keys target keys)
                    keys)))))
    ;; ---- [[GetOwnProperty]] ----
    (setf (getf internal :get-own-property)
          (lambda (o key)
            (declare (ignore o))
            (%proxy-guard revoked-cell)
            (setf key (%pk key))
            (let ((tr (%get-trap handler "getOwnPropertyDescriptor")))
              (if (null tr)
                  (js-get-own-property target key)
                  (let* ((res (js-call tr handler (list target key)))
                         (td (js-get-own-property target key)))
                    (cond
                      ((js-undefined-p res)
                       (when td
                         (when (not (prop-configurable td))
                           (%proxy-throw "proxy getOwnPropertyDescriptor: cannot report non-configurable property as non-existent"))
                         (unless (js-extensible-p target)
                           (%proxy-throw "proxy getOwnPropertyDescriptor: cannot report existing property of non-extensible target as non-existent")))
                       nil)
                      ((js-object-p res)
                       (let* ((plist (to-property-descriptor res))
                              (prop (%complete-desc-to-prop plist)))
                         (%proxy-check-goopd target key prop td)
                         prop))
                      (t (%proxy-throw "proxy getOwnPropertyDescriptor: trap returned neither object nor undefined"))))))))
    ;; ---- [[DefineOwnProperty]] ----
    (setf (getf internal :define-own-property)
          (lambda (o key desc)
            (declare (ignore o))
            (%proxy-guard revoked-cell)
            (setf key (%pk key))
            (let ((tr (%get-trap handler "defineProperty")))
              (if (null tr)
                  (js-define-own-property target key desc)
                  (let* ((descobj (from-desc-plist realm desc))
                         (ok (js-truthy (js-call tr handler (list target key descobj)))))
                    (when ok
                      (%proxy-check-define target key desc))
                    ok)))))
    ;; ---- getPrototypeOf / setPrototypeOf / isExtensible / preventExtensions ----
    ;; Core now dispatches these via js-get-proto/js-set-proto/js-extensible-p/
    ;; js-prevent-extensions (Reflect/Object/instanceof route through them), so these
    ;; traps fire. The default-forwarding branches call the SAME dispatchers on the
    ;; target so a nested-proxy target forwards correctly. NOTE: Object.setPrototypeOf
    ;; is currently overridden in object-extras.lisp to touch struct slots directly
    ;; and does NOT go through js-set-proto — so the setPrototypeOf trap only fires
    ;; via Reflect.setPrototypeOf / __proto__ assignment until that override is fixed
    ;; (see report proposals).
    (setf (getf internal :get-proto)
          (lambda (o)
            (declare (ignore o))
            (%proxy-guard revoked-cell)
            (let ((tr (%get-trap handler "getPrototypeOf")))
              (if (null tr)
                  (js-get-proto target)
                  (let ((res (js-call tr handler (list target))))
                    (unless (or (js-object-p res) (eq res *null*))
                      (%proxy-throw "proxy getPrototypeOf: trap must return object or null"))
                    (unless (js-extensible-p target)
                      (unless (same-value res (or (js-get-proto target) *null*))
                        (%proxy-throw "proxy getPrototypeOf: non-extensible target prototype mismatch")))
                    res)))))
    (setf (getf internal :set-proto)
          (lambda (o v)
            (declare (ignore o))
            (%proxy-guard revoked-cell)
            (let ((tr (%get-trap handler "setPrototypeOf")))
              (if (null tr)
                  (js-set-proto target v)
                  (let ((ok (js-truthy (js-call tr handler (list target v)))))
                    (when ok
                      (unless (js-extensible-p target)
                        (unless (same-value v (or (js-get-proto target) *null*))
                          (%proxy-throw "proxy setPrototypeOf: non-extensible target prototype mismatch"))))
                    ok)))))
    (setf (getf internal :is-extensible)
          (lambda (o)
            (declare (ignore o))
            (%proxy-guard revoked-cell)
            (let ((tr (%get-trap handler "isExtensible")))
              (if (null tr)
                  (js-extensible-p target)
                  (let ((res (js-truthy (js-call tr handler (list target)))))
                    (unless (eq res (js-extensible-p target))
                      (%proxy-throw "proxy isExtensible: result must match target extensibility"))
                    res)))))
    (setf (getf internal :prevent-extensions)
          (lambda (o)
            (declare (ignore o))
            (%proxy-guard revoked-cell)
            (let ((tr (%get-trap handler "preventExtensions")))
              (if (null tr)
                  (js-prevent-extensions target)
                  (let ((ok (js-truthy (js-call tr handler (list target)))))
                    (when (and ok (js-extensible-p target))
                      (%proxy-throw "proxy preventExtensions: cannot report extensible target as non-extensible"))
                    ok)))))
    internal))

;;; ---------------------------------------------------------------------------
;;; default [[Set]] with a Proxy receiver — OrdinarySet spelled out
;;; ---------------------------------------------------------------------------
;;; Core's %create-data-on-receiver reads/writes the receiver's props table
;;; directly, bypassing the proxy's internal traps. So when the set trap is
;;; absent we replicate OrdinarySet here: inherited accessor setters fire with
;;; RECEIVER (the proxy) as `this`; a data write lands via the proxy's
;;; [[DefineOwnProperty]] (which delegates to the target), matching the spec's
;;; Receiver.[[DefineOwnProperty]] path.
(defun %proxy-default-set (target key v receiver proxy)
  ;; Step 1: resolve ownDesc, walking the target's prototype chain if absent.
  ;; We must NOT delegate the whole set to a parent (its ordinary-set would write
  ;; to the proxy receiver via %create-data-on-receiver, bypassing the traps);
  ;; instead find the effective descriptor, then apply on the proxy receiver.
  (let ((own (loop for cur = target then (js-get-proto cur)
                   while (js-object-p cur)
                   for d = (js-get-own-property cur key)
                   when d return d)))
    (when (null own)
      ;; absent all the way up: a fresh writable/enumerable/configurable data prop
      (setf own (make-prop :value *undefined* :writable t :enumerable t :configurable t)))
    ;; Step 2: apply per OrdinarySetWithOwnDescriptor.
    (if (prop-accessor own)
        (if (and (prop-set own) (not (js-undefined-p (prop-set own))))
            (progn (js-call (prop-set own) receiver (list v)) *true*)
            *false*)
        (if (not (prop-writable own))
            *false*
            ;; data property + a proxy receiver: consult Receiver.[[GetOwnProperty]]
            ;; then Receiver.[[DefineOwnProperty]] (both fire the proxy's traps).
            (let ((existing (js-get-own-property proxy key)))
              (cond
                ((and existing (prop-accessor existing)) *false*)
                ((and existing (not (prop-writable existing))) *false*)
                (existing (js-bool (js-define-own-property proxy key (list :value v))))
                (t (js-bool (js-define-own-property proxy key
                              (list :value v :writable t :enumerable t :configurable t))))))))))

;;; ---------------------------------------------------------------------------
;;; ownKeys result coercion + invariants
;;; ---------------------------------------------------------------------------
(defun %proxy-own-keys-list (res)
  "CreateListFromArrayLike(res, «String, Symbol»): must be an object; each
   element must be a String or Symbol (else TypeError)."
  (unless (js-object-p res)
    (%proxy-throw "proxy ownKeys: trap result must be an object"))
  (let* ((len (to-length (js-get res "length")))
         (n (truncate len))
         (out '()))
    (dotimes (i n)
      (let ((el (js-get res (princ-to-string i))))
        (unless (or (stringp el) (js-symbol-p el))
          (%proxy-throw "proxy ownKeys: keys must be Strings or Symbols"))
        (push el out)))
    (nreverse out)))

(defun %proxy-check-own-keys (target keys)
  "The [[OwnPropertyKeys]] invariants: no duplicates; all non-configurable target
   keys present; if target non-extensible, keys must exactly equal target keys."
  ;; duplicate check
  (let ((seen (make-hash-table :test 'equal)))
    (dolist (k keys)
      (when (gethash k seen) (%proxy-throw "proxy ownKeys: duplicate keys are not allowed"))
      (setf (gethash k seen) t)))
  (let* ((target-keys (js-own-keys target))
         (extensible (js-extensible-p target))
         (nonconfig '())
         (present (make-hash-table :test 'equal)))
    (dolist (k keys) (setf (gethash k present) t))
    (dolist (k target-keys)
      (let ((d (js-get-own-property target k)))
        (when (and d (not (prop-configurable d))) (push k nonconfig))))
    ;; every non-configurable target key must appear
    (dolist (k nonconfig)
      (unless (gethash k present)
        (%proxy-throw "proxy ownKeys: non-configurable key missing from trap result")))
    (unless extensible
      ;; every target key must appear, and no extra keys
      (dolist (k target-keys)
        (unless (gethash k present)
          (%proxy-throw "proxy ownKeys: non-extensible target key missing from trap result")))
      (let ((tset (make-hash-table :test 'equal)))
        (dolist (k target-keys) (setf (gethash k tset) t))
        (dolist (k keys)
          (unless (gethash k tset)
            (%proxy-throw "proxy ownKeys: non-extensible target reported an extra key")))))))

;;; ---------------------------------------------------------------------------
;;; getOwnPropertyDescriptor helpers + invariants
;;; ---------------------------------------------------------------------------
(defun %complete-desc-to-prop (plist)
  "CompletePropertyDescriptor(plist) -> a PROP struct with all fields filled in
   (absent value/get/set -> undefined; absent booleans -> false)."
  (let ((accessor (or (present-p plist :accessor)
                      (present-p plist :get) (present-p plist :set))))
    (if accessor
        (make-prop :accessor t
                   :get (if (present-p plist :get) (getf plist :get) *undefined*)
                   :set (if (present-p plist :set) (getf plist :set) *undefined*)
                   :enumerable (and (present-p plist :enumerable) (getf plist :enumerable))
                   :configurable (and (present-p plist :configurable) (getf plist :configurable)))
        (make-prop :value (if (present-p plist :value) (getf plist :value) *undefined*)
                   :writable (and (present-p plist :writable) (getf plist :writable))
                   :enumerable (and (present-p plist :enumerable) (getf plist :enumerable))
                   :configurable (and (present-p plist :configurable) (getf plist :configurable))))))

(defun %proxy-check-goopd (target key prop td)
  "[[GetOwnProperty]] invariants for a returned descriptor PROP (target desc TD)."
  (declare (ignore key))
  (let ((extensible (js-extensible-p target)))
    (unless (prop-configurable prop)
      ;; a non-configurable descriptor may only be reported for a matching target
      ;; non-configurable property.
      (when (null td)
        (%proxy-throw "proxy getOwnPropertyDescriptor: cannot report non-existent property as non-configurable"))
      (when (prop-configurable td)
        (%proxy-throw "proxy getOwnPropertyDescriptor: cannot report configurable property as non-configurable"))
      ;; non-configurable non-writable data must match value
      (when (and (not (prop-accessor prop)) (not (prop-accessor td))
                 (not (prop-writable prop)) (prop-writable td))
        (%proxy-throw "proxy getOwnPropertyDescriptor: cannot report writable property as non-writable non-configurable")))
    (when (and (null td) (not extensible))
      (%proxy-throw "proxy getOwnPropertyDescriptor: cannot report new property on non-extensible target"))))

;;; ---------------------------------------------------------------------------
;;; defineProperty invariants
;;; ---------------------------------------------------------------------------
(defun %proxy-check-define (target key desc)
  "[[DefineOwnProperty]] invariants after the trap reports success."
  (let ((td (js-get-own-property target key))
        (extensible (js-extensible-p target))
        (setting-nonconfig (and (present-p desc :configurable)
                                (not (getf desc :configurable)))))
    (cond
      ((null td)
       (when (not extensible)
         (%proxy-throw "proxy defineProperty: cannot add property to non-extensible target"))
       (when setting-nonconfig
         (%proxy-throw "proxy defineProperty: cannot define non-configurable property that does not exist on target")))
      (t
       ;; if target prop is non-configurable, the described change must be a valid
       ;; redefinition (ValidateAndApplyPropertyDescriptor on a copy).
       (unless (%desc-compatible-p desc td extensible)
         (%proxy-throw "proxy defineProperty: incompatible with existing non-configurable target property"))
       (when (and setting-nonconfig (prop-configurable td))
         (%proxy-throw "proxy defineProperty: cannot make configurable target property non-configurable"))
       ;; Proxy-specific invariant (stricter than IsCompatible): a non-configurable
       ;; WRITABLE data property on target may not be redefined non-writable.
       (when (and (not (prop-configurable td)) (not (prop-accessor td)) (prop-writable td)
                  (present-p desc :writable) (not (getf desc :writable)))
         (%proxy-throw "proxy defineProperty: cannot make non-configurable writable property non-writable"))))))

(defun %desc-compatible-p (desc td extensible)
  "Would applying DESC to TD be a legal [[DefineOwnProperty]]?  Uses the core
   validator against a fresh clone so we don't mutate the real target."
  (declare (ignore extensible))
  (if (prop-configurable td)
      t
      ;; non-configurable: re-run the descriptor validation logic
      (let ((clone (copy-prop-struct td)))
        ;; simulate by attempting define on a throwaway holder
        (let ((holder (make-object)))
          (setf (gethash "k" (js-object-props holder)) clone)
          (%key-touch holder "k")
          (js-define-own-property holder "k" desc)))))

(defun copy-prop-struct (p)
  (make-prop :value (prop-value p) :get (prop-get p) :set (prop-set p)
             :writable (prop-writable p) :enumerable (prop-enumerable p)
             :configurable (prop-configurable p) :accessor (prop-accessor p)))

;;; ---------------------------------------------------------------------------
;;; descriptor plist -> JS object (for defineProperty trap argument)
;;; ---------------------------------------------------------------------------
(defun from-desc-plist (realm desc)
  "Build a JS descriptor object from a DEFINE-style plist (only present fields)."
  (let ((o (make-object :proto (realm-object-proto realm)))
        (accessor (or (present-p desc :accessor)
                      (present-p desc :get) (present-p desc :set))))
    (if accessor
        (progn
          (when (present-p desc :get) (put o "get" (getf desc :get)))
          (when (present-p desc :set) (put o "set" (getf desc :set))))
        (progn
          (when (present-p desc :value) (put o "value" (getf desc :value)))
          (when (present-p desc :writable) (put o "writable" (js-bool (getf desc :writable))))))
    (when (present-p desc :enumerable) (put o "enumerable" (js-bool (getf desc :enumerable))))
    (when (present-p desc :configurable) (put o "configurable" (js-bool (getf desc :configurable))))
    o))

;;; ---------------------------------------------------------------------------
;;; [[Call]] / [[Construct]] wrappers for a callable target
;;; ---------------------------------------------------------------------------
(defun %make-proxy-call (realm target handler revoked-cell)
  (declare (ignore realm))
  (lambda (this args)
    (%proxy-guard revoked-cell)
    (let ((tr (%get-trap handler "apply")))
      (if (null tr)
          (js-call target this args)
          (js-call tr handler (list target this (make-array-object args)))))))

(defun %make-proxy-construct (realm target handler revoked-cell)
  (declare (ignore realm))
  (lambda (args new-target)
    (%proxy-guard revoked-cell)
    (let ((tr (%get-trap handler "construct"))
          (nt (or new-target target)))
      (if (null tr)
          (js-construct target args nt)
          (let ((res (js-call tr handler (list target (make-array-object args) nt))))
            (unless (js-object-p res)
              (%proxy-throw "proxy construct: trap must return an object"))
            res)))))

;;; ---------------------------------------------------------------------------
;;; Proxy exotic object construction
;;; ---------------------------------------------------------------------------
(defun %make-proxy (realm target handler revoked-cell)
  (unless (js-object-p target) (%proxy-throw "Cannot create proxy with a non-object as target"))
  (unless (js-object-p handler) (%proxy-throw "Cannot create proxy with a non-object as handler"))
  (let* ((internal (%make-proxy-internal realm target handler revoked-cell))
         (proxy (make-object :proto *null* :internal internal)))
    ;; A proxy's own proto slot is irrelevant (dispatch is via traps once core
    ;; hooks land); leave it null. Class stays "Object".
    (when (js-callable-p target)
      (setf (js-object-call proxy) (%make-proxy-call realm target handler revoked-cell)))
    (when (and (js-object-p target) (js-object-construct target))
      (setf (js-object-construct proxy) (%make-proxy-construct realm target handler revoked-cell)))
    proxy))

;;; ---------------------------------------------------------------------------
;;; install
;;; ---------------------------------------------------------------------------
(defun install-proxy (realm)
  (let ((*current-realm* realm))
    (let ((ctor (native-function realm "Proxy"
                  (lambda (this args) (declare (ignore this args))
                    (%proxy-throw "Constructor Proxy requires 'new'")) 2)))
      ;; [[Construct]]
      (setf (js-object-construct ctor)
            (lambda (args new-target) (declare (ignore new-target))
              (%make-proxy realm (arg 0 args) (arg 1 args) (list nil))))
      ;; Proxy has no .prototype property (proxy-no-prototype.js).
      ;; Proxy.revocable(target, handler) -> { proxy, revoke }
      (def-method realm ctor "revocable" 2 (this args)
        (let* ((revoked-cell (list nil))
               (proxy (%make-proxy realm (arg 0 args) (arg 1 args) revoked-cell))
               (result (make-object :proto (realm-object-proto realm)))
               (revoke (native-function realm ""
                         (lambda (this args) (declare (ignore this args))
                           (setf (car revoked-cell) t)
                           *undefined*) 0)))
          (put result "proxy" proxy)
          (put result "revoke" revoke)
          result))
      (define-global realm "Proxy" ctor)
      ;; global built-in constructors are non-enumerable (define-global stores an
      ;; enumerable data prop; fix the attribute to match the spec / verifyProperty).
      (let ((d (gethash "Proxy" (js-object-props (realm-global realm)))))
        (when d (setf (prop-enumerable d) nil))))))

(register-builtin-installer 'install-proxy)
