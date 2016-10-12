;:  Single-file version of the interpreter.
;; Easier to submit to server, probably harder to use in the development process

(load "chez-init.ss") 

;-------------------+
;                   |
;    DATATYPES      |
;                   |
;-------------------+

;; Parsed expression datatypes

(define-datatype environment environment?
  (empty-env-record)
  (extended-env-record
   (syms (list-of symbol?))
   (vals (list-of scheme-value?))
   (env environment?)))

(define-datatype expression expression?
    [var-exp ; variable references
        (id symbol?)]
    [lit-exp        ; "Normal" data.  Did I leave out any types?
        (datum
            (lambda (x)
                (ormap (lambda (pred) (pred x))
                (list number? vector? boolean? symbol? string? pair? null?))))]
    [app-exp        ; applications
        (rator expression?)
        (rands (list-of expression?))]
    [quote-exp
        (datum always?)]
    ;[if-exp
    ;    (test-exp expression?)
    ;    (then-exp expression?)
    ;    (else-exp always?)]
    [if-exp
        (test-exp expression?)
        (then-exp expression?)
        (else-exp expression?)]
    [if-else-exp
        (test-exp expression?)
        (true-exp expression?)
        (false-exp expression?)]
    [single-let-exp (var expression?) ;--------------------------------------------------symbol 
               (body expression?)]
    [let-exp
        (vars (list-of expression?))
        ;(exps (list-of expression?))
        (bodies (list-of expression?))]
    [lambda-exp 
        (ids (list-of symbol?))
        (bodies (list-of expression?))]
    [lambda-exp-improper
        (vars (list-of expression?))
        (extra-vars symbol?)
        (bodies (list-of expression?))]
    [cond-exp
        (exps (list-of expression?))]
    [case-exp
        (eva (lambda (x) (or (expression? x)((list-of expression?) x))))
        (cases (list-of expression?))])

  
; datatype for procedures.  At first there is only one
; kind of procedure, but more kinds will be added later.

(define-datatype proc-val proc-val?
    [prim-proc
        (name symbol?)]
    [closure
        (vars (lambda (x)
                (or (symbol? x) ((list-of symbol?) x) (pair? x))))
        (bodies (list-of expression?))
        (env environment?)]
    [closure-improper
        (vars (list-of symbol?))
        (improper-var symbol?)
        (bodies (list-of expression?))
        (env environment?)])
   
  
;; environment type definitions

(define scheme-value?
  (lambda (x) #t))



;-------------------+
;                   |
;    PARSER         |
;                   |
;-------------------+

; This is a parser for simple Scheme expressions, such as those in EOPL, 3.1 thru 3.3.

; You will want to replace this with your parser that includes more expression types, more options for these types, and error-checking.

; Procedures to make the parser a little bit saner.
(define 1st car)
(define 2nd cadr)
(define 3rd caddr)
(define 4rd cadddr)

;;(define parse-exp         
;  (lambda (datum)
;    (cond
;     [(symbol? datum) (var-exp datum)]
;     [(number? datum) (lit-exp datum)]
;     [(pair? datum)
;      (cond
;      
;       [else (app-exp (parse-exp (1st datum))
;         (map parse-exp (cdr datum)))])]
;     [else (eopl:error 'parse-exp "bad expression: ~s" datum)])))
;;helper, check whether the list are all symbol
(define list-of-expression?
  [lambda (e)
    (if (list? e) (andmap expression? e) #f)])

(define lambda-var?
  [lambda (e)
    (cond 
      [(symbol? e) #t]
      [(pair? e)
          (let helper ([rest e])
            (cond 
              [(null? rest) #t]
              [(symbol? rest) #t]
              [else 
                (and (symbol? (car rest)) (helper (cdr rest)))]))]
      [else #f])])

(define lit?
  (lambda (e)
    (or (number? e)
      (string? e)
      (symbol? e)
      (boolean? e)
      (char? e)
      (vector? e)
      (list? e))))

(define parse-exp
  (lambda (datum)
    (cond
     [(and (list? datum) (eq? 'quote (1st datum)))
      (if (> (length datum) 2)
        (eopl:error 'parse-exp "Invalid syntax for quote: ~s" datum)
        (lit-exp (cadr datum)))]
   [((lambda (e)
    (or (number? e)
      (string? e)
      (boolean? e)
      (char? e)
      (vector? e))) datum) (lit-exp datum)]
   [(symbol? datum) (var-exp datum)]
     ;;set! expression
     [(eqv? (1st datum) 'set!)
      (cond
        [(> (length datum) 3)
          (eopl:error 'parse-exp "Too many parts: ~s" datum)]
      [(= (length datum) 3)
        (if (symbol? (2nd datum))
            (set!-exp (parse-exp (2nd datum)) (parse-exp (3rd datum)))
          (eopl:error 'parse-exp "declaration in set-expression ~s must take a symbol" (2nd datum)))]
      [else (eopl:error 'parse-exp "set expression ~s has incorrect arguments" datum)]
          )]
     [(pair? datum)
      (cond
        [(not (list? datum))
          (eopl:error 'parse-exp "expression ~s is an improper list" datum)]
        ;;lambda expression
    [(eqv? (car datum) 'lambda)
          (cond
            [(< (length datum) 3)
              (eopl:error 'parse-exp "lambda expression: ~s" datum)]
            [(symbol? (2nd datum))
              (lambda-exp (2nd datum) (map parse-exp (cddr datum)))]
            [(list? (2nd datum))
              (if (andmap (lambda (v) (symbol? v)) (cadr datum))
                (lambda-exp (2nd datum) (map parse-exp (cddr datum)))
                (eopl:error 'parse-exp "lambda argument list: formals must be symbols: ~s" datum))]
        [else (eopl:error 'parse-exp "Incorrect lambda syntax: ~s" datum)])]
    ;;if expression
    [(eqv? 'if (1st datum))
      (cond
        [(= 2 (length datum))
          (eopl:error 'parse-exp "missing then and else parts: ~s" datum)]
        [(= 3 (length datum))
          (if-exp (parse-exp (2nd datum)) (parse-exp (3rd datum)))]
        [(= 4 (length datum))
          (if-else-exp (parse-exp (2nd datum))
                 (parse-exp (3rd datum))
                 (parse-exp (4th datum)))]
        [else
          (eopl:error 'parse-exp "if-expression: ~s does not have the right format: condition, then, else" datum)])]
    ;;let expression
    [(or (eqv? 'let (1st datum)) (eqv? 'letrec (1st datum)) (eqv? 'let* (1st datum)));;check whether the 1st datum meeet any let type
      (cond
        [(< (length datum) 3) (eopl:error 'parse-exp "let-expression has incorrect length")]
        [else
          (letrec ([parse-let
            (trace-lambda parselet (ls)
              (trace-let helper ((rest ls))
                (cond
                  [(null? rest) (list)]
                  [(not (list? rest)) (eopl:error 'parse-exp "~s-list is not a proper list" (1st datum) rest)]
                  [(not (list? (car rest))) (eopl:error 'parse-exp "declaration in ~s-list is not a proper list" (1st datum) (car rest))]
                  [(not (= 2 (length (car rest)))) (eopl:error 'parse-exp "declaration in ~s-list must be in length of two ~s" (1st datum) (car rest))]
                  [(not (symbol? (caar rest))) (eopl:error 'parse-exp "variable in ~s must be a symbol ~s" (1st datum) (caar rest))]
                  [else
                    (cons (single-let-exp (parse-exp (caar rest))
                                          (parse-exp (cadar rest)))
                                          (helper (cdr rest)))])))])
              (cond
                [(symbol? (2nd datum))
                (cond
                  [(= 3 (length datum)) (eopl:error 'parse-exp "named-let-exp has incorrect length ~s" datum)]
                  [(not (eqv? 'let (1st datum))) (eopl:error 'parse-exp "declaration in ~s must be a proper list ~s" (1st datum) (2nd datum))]
                  [else (named-let-exp (var-exp (2nd datum))
                            (parse-let (3rd datum))
                            (map parse-exp (cdddr datum)))])]
                [(eqv? 'let (1st datum))
                  (let-exp (parse-let (2nd datum)) (map parse-exp (cddr datum)))]
                [(eqv? 'let* (1st datum))
                  (let*-exp (parse-let (2nd datum)) (map parse-exp (cddr datum)))]
                [else
                  (letrec-exp (parse-let (2nd datum)) (map parse-exp (cddr datum)))]))])]
        [else (app-exp (parse-exp (1st datum))
              (map parse-exp (cdr datum)))])]
     [else (eopl:error 'parse-exp "bad expression: ~s" datum)])))

;;#4b
(define unparse-exp
  (lambda (e)
    (cases expression e
      [var-exp (id) id]
      [lit-exp (id) id]
      [lambda-var-exp (var) var]
      [lambda-exp (var body) 
        (cons 'lambda (cons (if (symbol? var) var (map unparse-exp var)) 
                  (map unparse-exp body)))]
      [set!-exp (id r-val-exp) 
            (list 'set! (unparse-exp id) (unparse-exp r-val-exp))]
      [if-exp (condition-exp true-exp) 
            (list 'if (unparse-exp condition-exp) (unparse-exp true-exp))]
      [if-else-exp (condition-exp true-exp false-exp) 
            (list 'if (unparse-exp condition-exp) (unparse-exp true-exp) (unparse-exp false-exp))]
      [let-exp (ls body) 
          (cons* 'let (map unparse-exp ls) (map unparse-exp body))]
      [single-let-exp (var body) 
            (list (unparse-exp var) (unparse-exp body))]
      [named-let-exp (name ls body) (cons 'let 
          (cons (unparse-exp name) (cons (map unparse-exp ls) (map unparse-exp body))))]
      [let*-exp (ls body) (cons* 'let* 
          (cons (map unparse-exp ls) (map unparse-exp body)))]
      [letrec-exp (ls body) (cons* 'letrec 
          (cons (map unparse-exp ls) (map unparse-exp body)))]
      [app-exp (rator rand) (cons (unparse-exp rator) (map unparse-exp rand))])))

;-------------------+
;                   |
;   ENVIRONMENTS    |
;                   |
;-------------------+

; Environment definitions for CSSE 304 Scheme interpreter.  Based on EoPL section 2.3

;(define empty-env
;(lambda ()
;'()))
;(define extend-env
;(lambda (syms vals env)
;(cons (cons syms (list->vector vals))
;env)))

(define empty-env
  (lambda ()
    (empty-env-record)))

(define extend-env
  (lambda (syms vals env)
    (extended-env-record syms vals env)))

(define list-find-position
  (lambda (sym los)
    (list-index (lambda (xsym) (eqv? sym xsym)) los)))

(define list-index
  (lambda (pred ls)
    (cond
     ((null? ls) #f)
     ((pred (car ls)) 0)
     (else (let ((list-index-r (list-index pred (cdr ls))))
       (if (number? list-index-r)
     (+ 1 list-index-r)
     #f))))))

;(define apply-env
;  (lambda (env sym)
;    (if (null? env)
;    (eopl:error 'apply-env "No binding for ~s" sym)
;      (let ((syms (car (car env)))
;        (vals (cdr (car env)))
;        (env (cdr env)))
;      (let ([pos (rib-find-position sym syms)])
;        (if (number? pos)
;          (vector-ref vals pos)
;          (apply-env env sym)))))))

(define apply-env
    (lambda (env sym succeed fail) ; succeed and fail are procedures applied if the var is or isn't found, respectively.
        (cases environment env
            (empty-env-record ()
                (fail))
            (extended-env-record (syms vals env)
              (let ((pos (list-find-position sym syms)))
                     (if (number? pos)
                     (succeed (list-ref vals pos))
                     (apply-env env sym succeed fail))))
            )))

;-----------------------+
;                       |
;   SYNTAX EXPANSION    |
;                       |
;-----------------------+



; To be added later









;-------------------+
;                   |
;   INTERPRETER    |
;                   |
;-------------------+

; top-level-eval evaluates a form in the global environment

(define top-level-eval
  (lambda (form)
    ; later we may add things that are not expressions.
    (eval-exp form init-env)))

; eval-exp is the main component of the interpreter

(define eval-bodies
  (lambda (bodies env)
    ;(if (null? bodies)
    ;  (display 'problem-------------)
      (if (null? (cdr bodies))
        (eval-exp (car bodies) env)
        (begin
          (eval-exp (car bodies) env)
          (eval-bodies (cdr bodies) env)))));)

(define eval-exp
  (lambda (exp env)
    (printf "~s \n" exp)
    (cases expression exp
      [lit-exp (datum) datum]
      ;[var-exp (id)
      ;  (apply-env2 env id; look up its value.
      ;     (lambda (x) x) ; procedure to call if id is in the environment 
      ;     (lambda () (eopl:error 'apply-env ; procedure to call if id not in env
      ;        "variable not found in environment: ~s"
      ;   id)))] 
      [var-exp (id) ; look up its value.
        (apply-env env
                   id
                   (lambda (x) x) ; procedure to call if id is in env
                   (lambda () ; procedure to call if id is not in env
                      (apply-env init-env ; was init-env
                                id
                                (lambda (x) x) ; call if id is in global-env
                                (lambda () ; call if id not in global-env
                                  (eopl:error 'apply-env
                                          "variable ~s is not bound"
                                          id)))))]
      [app-exp (rator rands)
        (let ([proc-value (eval-exp rator env)]
              [args (eval-rands rands env)])
          (apply-proc proc-value args))]
      [lambda-exp (ids bodies)
          (display 'hello)
          (closure ids bodies env)]
      [let-exp (vars bodies)
        (let ([new-env (extend-env (map (lambda (x) (cadr (cadr x))) vars) 
                                   (eval-rands (map (lambda (x) (caddr x)) vars) env)
                                   env)])
          (eval-bodies bodies new-env))]

;;      [quote-exp (datum) datum]
      [else (eopl:error 'eval-exp "Bad abstract syntax: ~a" exp)])))

; evaluate the list of operands, putting results into a list

(define eval-rands
  (lambda (rands env)
    (map (lambda (x) (eval-exp x env)) rands)))

;  Apply a procedure to its arguments.
;  At this point, we only have primitive procedures.  
;  User-defined procedures will be added later.

(define apply-proc
  (lambda (proc-value args)
    (printf "~s\n ~s\n" proc-value args)
    (cases proc-val proc-value
        [prim-proc (op) (apply-prim-proc op args)]
      ; You will add other cases
        [closure (vars bodies env) (cond 
                                      [((list-of symbol?) vars)
                                            (let eval-loop ([bodies bodies]
                                                            [env (extend-env vars args env)])
                                                            (cond
                                                                [(null? (cdr bodies)) (eval-exp (car bodies) env)]
                                                                [else (begin (eval-exp (car bodies) env) (eval-loop (cdr bodies) env))]))]
                                      [else (eval-rands bodies (extend-env (list vars) (list args) env))])]
        [closure-improper (vars improper-var bodies env) 
            (eval-rands bodies (extend-env (append vars (list improper-var)) 
                                            (make-improper args (length vars) 1) env))]
        [else (error 'apply-proc
                   "Attempt to apply bad procedure: ~s" 
                    proc-value)])))

(define *prim-proc-names* '(+ - * / add1 sub1 cons = < > <= >= not zero?
    car cadr cdr caar cddar cddr caddr caadr cdddr list null? eq? equal? eqv? atom? length list->vector list? 
    pair? procedure? vector->list? vector make-vector vector-ref vector? number?
    symbol? set-car! set-cdr! vector-set! display newline ))

(define init-env         ; for now, our initial global environment only contains 
  (extend-env            ; procedure names.  Recall that an environment associates
     *prim-proc-names*   ;  a value (not an expression) with an identifier.
     (map prim-proc      
          *prim-proc-names*)
     (empty-env)))

; Usually an interpreter must define each 
; built-in procedure individually.  We are "cheating" a little bit.

(define apply-prim-proc
  (lambda (prim-proc args)
    (cond [(null? prim-proc) (error 'apply-prim-proc
      "You have no primitive procedure specified")]
          [(null? args) (error 'apply-prim-proc
            "You have no arguments specified")]
    [else 
        (case prim-proc
            [(+) (apply + args)]
            [(-) (apply - args)]
            [(*) (apply * args)]
            [(/) (apply / args)]
            [(add1) (if (= (length args) 1)
                        (+ (1st args) 1)
                        (error 'apply-prim-proc "You need to pass one argument into add1, args: " args))]
            [(sub1) (if (= (length args) 1) 
                        (- (1st args) 1)
                        (error 'apply-prim-proc "You need to pass one argument into sub1, args: " args))]
            [(cons) (cons (1st args) (2nd args))]
            [(=) (apply = args)]
            [(<) (apply < args)]
            [(>) (apply > args)]
            [(<=) (apply <= args)]
            [(>=) (apply >= args)]
            [(not) (not (1st args))]
            [(zero?) (= 0 (1st args))]
            [(car) (car (1st args))]
            [(cdr) (cdr (1st args))]
            [(caar) (car (car (1st args)))] [(caaar) (car (car (car (1st args))))]
            [(cddr) (cdr (cdr (1st args)))] [(cdddr) (cdr (cdr (cdr (1st args))))]
            [(cadr) (car (cdr (1st args)))]
            [(caddr) (car (cdr (cdr (1st args))))] [(cdr) (cdr (1st args))]
            [(caadr) (car (car (cdr args)))] [(cadar) (car (cdr (car (1st args))))]
            [(cddar) (cdr (cdr (car (1st args))))]
            [(list) (apply list args)]
            [(null?) (apply null? args)]
            [(eq?) (if (null? (cdr args)) 
                            (error 'apply-prim-proc "eq? requires 2 args")
                            (eq? (1st args) (2nd args)))]
            [(eqv?) (if (null? (cdr args))
                            (error 'apply-prim-proc "eqv? requires 2 args")
                            (eqv? (1st args) (2nd args)))]
            [(equal?) (if (null? (cdr args))
                            (error 'apply-prim-proc "equal requires 2 args")
                            (equal? (1st args) (2nd args)))]
            [(atom?) (not (pair? args))]
            [(length) (apply length args)]
            [(list->vector) (apply list->vector args)]
            [(list?) (apply list? args)]
            [(pair?) (pair? args)]
            [(procedure?) (apply proc-val? args)]
            [(vector->list) (apply vector->list args)]
            [(vector) (apply vector args)]
            [(make-vector) (if (number? (1st args))
                            (if (null? (cdr args))
                                (make-vector (1st args))
                                (make-vector (1st args) (2nd args)))
                            (error 'apply-prim-proc "First argument to make-vector must be a number"))]
            [(vector-ref) (vector-ref (1st args) (2nd args))]
            [(vector?) (apply vector? args)]
            [(number?) (if (= (length args) 1)
                            (number? (1st args))
                            (error 'apply-prim-proc "number? can only be applied to an arg of length 1, not arg: " args))]
            [(symbol?) (if (= (length args) 1)
                            (symbol? (1st args))
                            (error 'apply-prim-proc "symbol? can only be applied to an arg of length 1, not arg: " args))]
            [(set-car!) (set-car! (1st args) (2nd args))]
            [(set-cdr!) (set-cdr! (1st args) (2nd args))]
            [(vector-set!) (vector-set! (1st args) (2nd args) (3rd args))]
            [(display) (apply display args)]
            [(newline) (apply newline args)]
            [else (error 'apply-prim-proc 
            "Bad primitive procedure name: ~s" 
            prim-proc)])])))

(define rep      ; "read-eval-print" loop.
  (lambda ()
    (display "--> ")
    ;; notice that we don't save changes to the environment...
    (let ([answer (top-level-eval (parse-exp (read)))])
      ;; TODO: are there answers that should display differently?
      (eopl:pretty-print answer) (newline)
      (rep))))  ; tail-recursive, so stack doesn't grow.

(define eval-one-exp
  (lambda (x) (top-level-eval (parse-exp x))))





