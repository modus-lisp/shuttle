;;;; parse.lisp — a Pratt parser: expressions (full precedence) + core
;;;; statements. AST = lists tagged by keyword. (Destructuring, classes,
;;;; generators, modules, full ASI: TODO — the grammar grows from here.)
(in-package #:shuttle)

(defvar *toks*) (defvar *pos*)
(defun cur () (aref *toks* *pos*))
(defun cur-type () (car (cur)))
(defun cur-val () (cdr (cur)))
(defun adv () (prog1 (cur) (incf *pos*)))
(defun punct? (v) (and (eq (cur-type) :punct) (string= (cur-val) v)))
(defun kw? (v) (and (eq (cur-type) :ident) (string= (cur-val) v)))
(defun eat (v) (if (punct? v) (adv) (js-throw (format nil "Expected '~a'" v))))
(defun opt (v) (when (punct? v) (adv) t))

(defparameter *binops*
  ;; op -> binding power (left); equality/relational/etc.
  '(("||" . 3) ("&&" . 4) ("|" . 5) ("^" . 6) ("&" . 7)
    ("==" . 8) ("!=" . 8) ("===" . 8) ("!==" . 8)
    ("<" . 9) (">" . 9) ("<=" . 9) (">=" . 9)
    ("<<" . 10) (">>" . 10) (">>>" . 10)
    ("+" . 11) ("-" . 11) ("*" . 12) ("/" . 12) ("%" . 12)))
(defparameter *assignops* '("=" "+=" "-=" "*=" "/=" "%="))

(defun parse-program (src)
  (let ((*toks* (tokenize src)) (*pos* 0) (stmts '()))
    (loop until (eq (cur-type) :eof) do (push (parse-stmt) stmts))
    (list :block (nreverse stmts))))

;;; ---- statements ----
(defun parse-stmt ()
  (cond
    ((punct? "{") (parse-block))
    ((or (kw? "var") (kw? "let") (kw? "const")) (parse-var))
    ((kw? "function") (parse-function nil))
    ((kw? "return") (adv) (let ((e (if (or (punct? ";") (punct? "}") (eq (cur-type) :eof)) *undefined-ast*
                                       (parse-expr 1)))) (opt ";") (list :return e)))
    ((kw? "if") (parse-if))
    ((kw? "while") (adv) (eat "(") (let ((c (parse-expr 1))) (eat ")") (list :while c (parse-stmt))))
    ((kw? "for") (parse-for))
    ((kw? "switch") (parse-switch))
    ((kw? "break") (adv) (opt ";") (list :break))
    ((kw? "continue") (adv) (opt ";") (list :continue))
    ((kw? "try") (parse-try))
    ((kw? "throw") (adv) (let ((e (parse-expr 1))) (opt ";") (list :throw e)))
    ((punct? ";") (adv) (list :empty))
    (t (let ((e (parse-expr 1))) (opt ";") (list :expr e)))))

(defparameter *undefined-ast* '(:undefined))
(defun parse-block () (eat "{") (let ((s '())) (loop until (punct? "}") do (push (parse-stmt) s)) (eat "}")
                        (list :block (nreverse s))))
(defun parse-if () (adv) (eat "(") (let ((c (parse-expr 1))) (eat ")")
                    (let ((then (parse-stmt)) (else (when (kw? "else") (adv) (parse-stmt))))
                      (list :if c then else))))
(defun parse-var-decl ()                 ; no trailing semicolon (for use in `for`)
  (let ((kind (cur-val))) (adv)
    (let ((decls '()))
      (loop (let ((name (cur-val))) (adv)
              (push (cons name (when (opt "=") (parse-expr 2))) decls))
            (unless (opt ",") (return)))
      (list :var kind (nreverse decls)))))
(defun parse-var () (prog1 (parse-var-decl) (opt ";")))

(defun parse-for ()
  (adv) (eat "(")
  (let ((init (cond ((punct? ";") nil)
                    ((or (kw? "var") (kw? "let") (kw? "const")) (parse-var-decl))
                    (t (list :expr (parse-expr 1))))))
    (eat ";")
    (let ((test (unless (punct? ";") (parse-expr 1)))) (eat ";")
      (let ((update (unless (punct? ")") (parse-expr 1)))) (eat ")")
        (list :for init test update (parse-stmt))))))

(defun parse-switch ()
  (adv) (eat "(") (let ((disc (parse-expr 1))) (eat ")") (eat "{")
    (let ((cases '()) (default nil))
      (loop until (punct? "}") do
        (flet ((body () (let ((s '()))
                          (loop until (or (kw? "case") (kw? "default") (punct? "}")) do (push (parse-stmt) s))
                          (nreverse s))))
          (cond ((kw? "case") (adv) (let ((e (parse-expr 1))) (eat ":") (push (cons e (body)) cases)))
                ((kw? "default") (adv) (eat ":") (setf default (body)))
                (t (js-throw "malformed switch")))))
      (eat "}") (list :switch disc (nreverse cases) default))))

(defun parse-try ()
  (adv) (let ((blk (parse-block)) (param nil) (catch nil) (fin nil))
          (when (kw? "catch") (adv)
            (when (punct? "(") (adv) (setf param (cur-val)) (adv) (eat ")"))
            (setf catch (parse-block)))
          (when (kw? "finally") (adv) (setf fin (parse-block)))
          (list :try blk param catch fin)))
(defun parse-function (exprp)
  (adv)                                       ; 'function'
  (let ((name (when (eq (cur-type) :ident) (prog1 (cur-val) (adv)))))
    (eat "(") (let ((params '()))
                (loop until (punct? ")") do (push (cur-val) params) (adv) (unless (punct? ")") (eat ",")))
                (eat ")")
                (let ((body (parse-block)))
                  (declare (ignore exprp))
                  (list :func name (nreverse params) body)))))

;;; ---- expressions (Pratt) ----
(defun parse-expr (min-bp)
  (let ((left (parse-unary)))
    (loop
      (let ((tt (cur-type)) (tv (cur-val)))
        (cond
          ;; assignment (right-assoc), lowest
          ((and (eq tt :punct) (member tv *assignops* :test #'string=) (>= 1 (1- min-bp)))
           (adv) (setf left (list :assign tv left (parse-expr 1))))
          ;; conditional ?:
          ((and (punct? "?") (>= 2 min-bp))
           (adv) (let ((then (parse-expr 1))) (eat ":")
                   (setf left (list :cond left then (parse-expr 2)))))
          ;; instanceof / in (keyword operators, relational precedence)
          ((and (eq tt :ident) (member tv '("instanceof" "in") :test #'string=) (>= 9 min-bp))
           (adv) (setf left (list :bin tv left (parse-expr 10))))
          ;; binary / logical
          ((and (eq tt :punct) (assoc tv *binops* :test #'string=))
           (let ((bp (cdr (assoc tv *binops* :test #'string=))))
             (if (< bp min-bp) (return)
                 (progn (adv) (setf left (let ((r (parse-expr (1+ bp))))
                                           (if (member tv '("&&" "||") :test #'string=)
                                               (list :logical tv left r) (list :bin tv left r))))))))
          (t (return)))))
    left))

(defun parse-unary ()
  (let ((tt (cur-type)) (tv (cur-val)))
    (cond
      ((and (eq tt :punct) (member tv '("!" "-" "+" "~") :test #'string=)) (adv) (list :unary tv (parse-unary)))
      ((kw? "typeof") (adv) (list :unary "typeof" (parse-unary)))
      ((kw? "new") (adv) (let ((callee (parse-member (parse-primary) nil))) ; member, but NOT the call
                           (list :new callee (if (punct? "(") (parse-args) '()))))
      ((or (punct? "++") (punct? "--")) (let ((op tv)) (adv) (list :update op t (parse-unary))))
      (t (parse-postfix)))))

(defun parse-postfix ()
  (let ((e (parse-member (parse-primary))))
    (if (or (punct? "++") (punct? "--")) (prog1 (list :update (cur-val) nil e) (adv)) e)))

(defun parse-member (e &optional (allow-call t))   ; . [] () chains
  (loop
    (cond ((punct? ".") (adv) (setf e (list :member e (list :str (cur-val)) nil)) (adv))
          ((punct? "[") (adv) (let ((k (parse-expr 1))) (eat "]") (setf e (list :member e k t))))
          ((and allow-call (punct? "(")) (setf e (list :call e (parse-args))))
          (t (return e)))))

(defun parse-args ()
  (eat "(") (let ((args '()))
              (loop until (punct? ")") do (push (parse-expr 2) args) (unless (punct? ")") (eat ",")))
              (eat ")") (nreverse args)))

(defun parse-primary ()
  (let ((tt (cur-type)) (tv (cur-val)))
    (cond
      ((eq tt :num) (adv) (list :num tv))
      ((eq tt :str) (adv) (list :str tv))
      ((kw? "true") (adv) '(:bool t)) ((kw? "false") (adv) '(:bool nil))
      ((kw? "null") (adv) '(:null)) ((kw? "undefined") (adv) '(:undefined))
      ((kw? "this") (adv) '(:this))
      ((kw? "function") (parse-function t))
      ((punct? "(") (parse-paren-or-arrow))
      ((punct? "[") (adv) (let ((elems '()))
                            (loop until (punct? "]") do (push (parse-expr 2) elems) (unless (punct? "]") (eat ",")))
                            (eat "]") (list :array (nreverse elems))))
      ((punct? "{") (parse-object-literal))
      ((eq tt :ident)
       (adv) (if (punct? "=>")                  ; id => body  (arrow)
                 (progn (adv) (list :arrow (list tv) (parse-arrow-body)))
                 (list :ident tv)))
      (t (js-throw (format nil "Unexpected token ~a ~s" tt tv))))))

(defun parse-arrow-body ()
  (if (punct? "{") (parse-block) (list :block (list (list :return (parse-expr 2))))))

(defun parse-paren-or-arrow ()
  ;; parse ( ... ); if followed by =>, it's an arrow whose contents are params.
  (eat "(")
  (let ((items '()))
    (loop until (punct? ")") do (push (parse-expr 2) items) (unless (punct? ")") (eat ",")))
    (eat ")")
    (setf items (nreverse items))
    (if (punct? "=>")
        (progn (adv) (list :arrow (mapcar (lambda (e) (if (eq (car e) :ident) (second e)
                                                          (js-throw "bad arrow param"))) items)
                           (parse-arrow-body)))
        (or (car (last items)) (js-throw "empty ()")))))

(defun parse-object-literal ()
  (eat "{") (let ((props '()))
              (loop until (punct? "}") do
                (let ((key (cur-val))) (adv) (eat ":")
                  (push (cons key (parse-expr 2)) props))
                (unless (punct? "}") (eat ",")))
              (eat "}") (list :object (nreverse props))))
