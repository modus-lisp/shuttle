;;;; compile.lisp — AST -> bytecode. A flat instruction stream (op . args) with
;;;; symbolic labels, then assembled to a vector with resolved jump targets.
;;;; Stack machine; variables are name-resolved through an environment chain
;;;; (indexed locals + scope analysis = a later optimization).
(in-package #:shuttle)

(defstruct code name params instrs)
(defvar *out*)
(defvar *break-target* nil) (defvar *continue-target* nil)
(defun em (op &rest args) (push (cons op args) *out*))
(defun lbl () (gensym "L"))

(defun assemble (rev-instrs)
  (let ((instrs (nreverse rev-instrs)) (pos (make-hash-table)) (idx 0) (out '()))
    (dolist (in instrs) (if (eq (car in) :label) (setf (gethash (cadr in) pos) idx) (incf idx)))
    (dolist (in instrs)
      (unless (eq (car in) :label)
        (push (if (member (car in) '(:jmp :jmp-if-false :jmp-if-true :and-jmp :or-jmp :push-handler))
                  (list (car in) (gethash (cadr in) pos)) in) out)))
    (coerce (nreverse out) 'vector)))

(defun compile-toplevel (src)
  ;; top-level falls off the end so RUN returns the completion value (eval semantics)
  (compile-fn nil '() (parse-program src) t))

(defun compile-fn (name params body &optional toplevel)
  (let ((*out* '()))
    ;; hoist: pre-declare all `var` names (as undefined) so forward reads don't
    ;; ReferenceError. Function declarations are hoisted by :func handling below.
    (dolist (v (collect-var-names body))
      (unless (member v params :test #'string=)
        (em :const *undefined*) (em :declare-var v)))
    (compile-stmt body)
    (unless toplevel (em :const *undefined*) (em :ret))   ; functions default-return undefined
    (make-code :name name :params params :instrs (assemble *out*))))

(defun collect-var-names (node &optional acc)
  "Collect `var`-declared names in NODE, NOT descending into nested functions."
  (when (consp node)
    (case (car node)
      ((:func :arrow) acc)               ; nested function scope: stop
      (:var (dolist (d (third node)) (pushnew (car d) acc :test #'string=)) acc)
      (:for-in (setf acc (collect-var-names (fourth node) (collect-var-names (second node) acc))))
      (:for-of (setf acc (collect-var-names (fourth node) (collect-var-names (second node) acc))))
      (t (dolist (x (cdr node))
           (cond ((and (consp x) (keywordp (car x))) (setf acc (collect-var-names x acc)))
                 ((and (consp x) (consp (car x)))   ; a list of statements/cases
                  (dolist (y x) (when (consp y) (setf acc (collect-var-names y acc)))))))
         acc))))

;;; ---- statements ----
(defun compile-stmt (node)
  (ecase (car node)
    (:block (mapc #'compile-stmt (second node)))
    (:empty nil)
    (:expr (compile-expr (second node)) (em :save-completion))
    (:var (loop for (name . init) in (third node)
                do (if init (compile-expr init) (em :const *undefined*)) (em :declare-var name)))
    (:func (compile-expr node) (em :declare-var (second node)))
    (:return (compile-expr (second node)) (em :ret))
    (:throw (compile-expr (second node)) (em :throw-op))
    (:if (let ((l1 (lbl)) (l2 (lbl)))
           (compile-expr (second node)) (em :jmp-if-false l1)
           (compile-stmt (third node)) (em :jmp l2)
           (em :label l1) (when (fourth node) (compile-stmt (fourth node)))
           (em :label l2)))
    (:while (let ((top (lbl)) (end (lbl)))
              (em :label top) (compile-expr (second node)) (em :jmp-if-false end)
              (let ((*break-target* end) (*continue-target* top)) (compile-stmt (third node)))
              (em :jmp top) (em :label end)))
    (:for (destructuring-bind (init test update body) (cdr node)
            (let ((top (lbl)) (cont (lbl)) (end (lbl)))
              (when init (compile-stmt (if (eq (car init) :var) init (list :expr (second init)))))
              (em :label top)
              (when test (compile-expr test) (em :jmp-if-false end))
              (let ((*break-target* end) (*continue-target* cont)) (compile-stmt body))
              (em :label cont)
              (when update (compile-expr update) (em :pop))
              (em :jmp top) (em :label end))))
    (:for-in (compile-for-in node))
    (:for-of (compile-for-of node))
    (:break (if *break-target* (em :jmp *break-target*) (js-throw "illegal break")))
    (:continue (if *continue-target* (em :jmp *continue-target*) (js-throw "illegal continue")))
    (:switch (destructuring-bind (disc cases default) (cdr node)
               (let ((dv (string (gensym "SW"))) (end (lbl)) (deflabel (lbl))
                     (clabels (mapcar (lambda (c) (cons c (lbl))) cases)))
                 (compile-expr disc) (em :declare-var dv)
                 (dolist (cl clabels)
                   (em :get-var dv) (compile-expr (car (car cl))) (em :bin "===") (em :jmp-if-true (cdr cl)))
                 (em :jmp deflabel)
                 (let ((*break-target* end))
                   (dolist (cl clabels) (em :label (cdr cl)) (mapc #'compile-stmt (cdr (car cl))))
                   (em :label deflabel) (when default (mapc #'compile-stmt default)))
                 (em :label end))))
    (:try (destructuring-bind (blk param catch fin) (cdr node)
            (if catch
                (let ((lc (lbl)) (after (lbl)))
                  (em :push-handler lc) (compile-stmt blk) (em :pop-handler) (em :jmp after)
                  (em :label lc) (if param (em :declare-var param) (em :pop))   ; bind/discard thrown value
                  (compile-stmt catch) (em :label after))
                (compile-stmt blk))
            (when fin (compile-stmt fin))))))   ; v0: finally runs on the normal/caught path

(defun for-head-assign (head)
  "Bind the value currently on top of the stack to the loop target (consumes it)."
  (cond ((eq (car head) :var) (em :declare-var (car (first (third head)))))
        ((eq (car head) :ident) (em :set-var (second head)) (em :pop))
        (t (js-throw "unsupported for-in/of target"))))

(defun compile-for-in (node)
  (destructuring-bind (head obj body) (cdr node)
    (let ((keys (string (gensym "KS"))) (idx (string (gensym "I"))) (len (string (gensym "N")))
          (top (lbl)) (cont (lbl)) (end (lbl)))
      (compile-expr obj) (em :for-in-keys) (em :declare-var keys)  ; array of enumerable keys
      (em :const 0d0) (em :declare-var idx)
      (em :get-var keys) (em :get-prop-c "length") (em :declare-var len)
      (em :label top)
      (em :get-var idx) (em :get-var len) (em :bin "<") (em :jmp-if-false end)
      (em :get-var keys) (em :get-var idx) (em :get-prop)     ; the key string
      (for-head-assign head)
      (let ((*break-target* end) (*continue-target* cont)) (compile-stmt body))
      (em :label cont)
      (em :get-var idx) (em :const 1d0) (em :bin "+") (em :set-var idx) (em :pop)
      (em :jmp top) (em :label end))))

(defun compile-for-of (node)
  (destructuring-bind (head obj body) (cdr node)
    (let ((it (string (gensym "IT"))) (res (string (gensym "R")))
          (top (lbl)) (cont (lbl)) (end (lbl)))
      (compile-expr obj) (em :get-iterator) (em :declare-var it)
      (em :label top)
      (em :get-var it) (em :iter-next) (em :declare-var res)     ; {value,done}
      (em :get-var res) (em :get-prop-c "done") (em :jmp-if-true end)
      (em :get-var res) (em :get-prop-c "value")
      (for-head-assign head)
      (let ((*break-target* end) (*continue-target* cont)) (compile-stmt body))
      (em :label cont) (em :jmp top) (em :label end))))

;;; ---- expressions (each leaves exactly one value on the stack) ----
(defun compile-expr (node)
  (ecase (car node)
    (:num (em :const (second node)))
    (:str (em :const (second node)))
    (:bool (em :const (if (second node) *true* *false*)))
    (:null (em :const *null*))
    (:undefined (em :const *undefined*))
    (:this (em :get-this))
    (:ident (em :get-var (second node)))
    (:bin (compile-expr (third node)) (compile-expr (fourth node)) (em :bin (second node)))
    (:unary (if (and (string= (second node) "typeof") (eq (car (third node)) :ident))
                (em :typeof-var (second (third node)))     ; typeof of a NAME never throws
                (progn (compile-expr (third node)) (em :unary (second node)))))
    (:delete (let ((tgt (second node)))
               (if (eq (car tgt) :member)
                   (progn (compile-expr (second tgt))
                          (if (fourth tgt) (compile-expr (third tgt)) (em :const (second (third tgt))))
                          (em :del-prop))
                   (em :const *true*))))   ; delete of a non-reference is true (sloppy)
    (:logical (let ((end (lbl)))
                (compile-expr (third node))
                (em (if (string= (second node) "&&") :and-jmp :or-jmp) end)
                (compile-expr (fourth node)) (em :label end)))
    (:cond (let ((l1 (lbl)) (l2 (lbl)))
             (compile-expr (second node)) (em :jmp-if-false l1)
             (compile-expr (third node)) (em :jmp l2)
             (em :label l1) (compile-expr (fourth node)) (em :label l2)))
    (:assign (compile-assign (second node) (third node) (fourth node)))
    (:update (compile-update (second node) (third node) (fourth node)))
    (:member (compile-expr (second node))
             (if (fourth node) (progn (compile-expr (third node)) (em :get-prop))
                 (em :get-prop-c (second (third node)))))   ; non-computed key node is (:str name)
    (:call (compile-call (second node) (third node)))
    (:new (compile-expr (second node)) (mapc #'compile-expr (third node)) (em :new (length (third node))))
    (:array (mapc #'compile-expr (second node)) (em :array (length (second node))))
    (:object (loop for (k . v) in (second node) do (em :const k) (compile-expr v))
             (em :object (length (second node))))
    (:func (em :closure (compile-fn (second node) (third node) (fourth node))))
    (:arrow (em :closure (compile-fn nil (second node) (third node))))))

(defun compile-call (callee args)
  (if (eq (car callee) :member)            ; method call: `this` is the object
      (progn (compile-expr (second callee)) (em :dup)
             (if (fourth callee) (progn (compile-expr (third callee)) (em :get-prop))
                 (em :get-prop-c (second (third callee)))))
      (progn (em :const *undefined*) (compile-expr callee)))   ; plain call: this = undefined
  (mapc #'compile-expr args)
  (em :call (length args)))

(defun compile-assign (op target value)
  (let ((base (and (> (length op) 1) (subseq op 0 (1- (length op))))))  ; "+=" -> "+"
    (ecase (car target)
      (:ident (if base (progn (em :get-var (second target)) (compile-expr value) (em :bin base))
                  (compile-expr value))
              (em :set-var (second target)))
      (:member
       (compile-expr (second target))                                       ; obj
       (if (fourth target) (compile-expr (third target)) (em :const (second (third target)))) ; key
       (if base
           ;; obj key -> [obj key obj-key-get] -> bin -> set-prop  (dup obj+key first)
           (progn (em :dup2)               ; stack: obj key obj key
                  (em :get-prop)           ; stack: obj key old
                  (compile-expr value) (em :bin base))  ; stack: obj key new
           (compile-expr value))
       (em :set-prop)))))

(defun compile-update (op prefix target)
  (let ((binop (if (string= op "++") "+" "-")))
    (ecase (car target)
      (:ident
       (let ((name (second target)))
         (em :get-var name) (em :to-num)
         (if prefix
             (progn (em :const 1d0) (em :bin binop) (em :set-var name))
             (progn (em :dup) (em :const 1d0) (em :bin binop) (em :set-var name) (em :pop)))))
      (:member
       (compile-expr (second target))
       (if (fourth target) (compile-expr (third target)) (em :const (second (third target))))
       ;; stack: obj key ; VM op reads obj[key], applies +/-1, writes back,
       ;; and pushes the new (prefix) or old (postfix) numeric value.
       (em :update-prop (if (string= op "++") 1d0 -1d0) prefix)))))
