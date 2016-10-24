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
   (syms (lambda (x) (or ((list-of symbol?) x)(pair? x))))
   (vals (list-of scheme-value?))
   (env environment?))
   [recursively-extended-env-record
    (proc-names (list-of symbol?))
    (idss (lambda (x) (or ((list-of symbol?) x)(pair? x))))
    (bodiess (lambda (x) (or ((list-of expression?) x) ((list-of (list-of expression?)) x))))
    (env environment?)])

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
    [if-then-exp 
        (test expression?)
        (true expression?)]
    [if-else-exp
        (test-exp expression?)
        (true-exp expression?)
        (false-exp expression?)]
    [let-exp (ids (list-of symbol?))
       (vals (list-of expression?))
       (body (list-of expression?))]
   [let*-exp (ids (list-of symbol?))
       (vals (list-of expression?))
       (body (list-of expression?))]
   [letrec-exp
      (proc-names (list-of symbol?))
     ; (idss (list-of (list-of symbol?)))
     (idss (lambda (x) 
        (ormap (lambda (y) 
                  (or ((list-of symbol?) y)
                         ((list-of improper?) y))) x)))
      (bodiess (lambda (x) (or ((list-of expression?) x) ((list-of (list-of expression?)) x))))
      (letrec-bodies (list-of expression?))]
    [letrec-exp-improper
      (proc-names (list of symbol?))
      (idss (lambda (x) (or (list-of (list-of symbol?)))))
      (bodies (list-of expression?))
      (letrec-body (lambda (x) (or (expression? x) ((list-of expression?) x))))]
   [let-named-exp (name symbol?)
       (ids (list-of symbol?))
       (vals (list-of expression?))
       (body (list-of expression?))]

    ;[single-let-exp (var expression?) ;--------------------------------------------------symbol 
    ;           (body expression?)]
    ;[let-exp
    ;    (vars (list-of expression?))
    ;    (exps (list-of expression?))
    ;    (bodies (list-of expression?))]
    [lambda-var-exp (var lambda-var?)]
    [lambda-exp 
        (ids (lambda (x) (or (symbol? x) ((list-of symbol?) x))))
        (bodies (list-of expression?))]
    [lambda-exp-improper
        (vars pair?)
        (opt symbol?)
        (bodies (list-of expression?))]
    [cond-exp
        (args (list-of expression?))
        (bodies (list-of expression?))]
    [or-exp
        (bodies (list-of expression?))]
    [begin-exp
        (bodies (list-of expression?))]
    [and-exp
        (bodies (list-of expression?))]
    [case-exp
        (tests (lambda (x)
                  (or (symbol? x) (number? x) (pair? x))))
        (vars (lambda (x)
                  (or (symbol? x) (number? x) (pair? x))))
        (bodies (list-of expression?))]
    [while-exp
        (test expression?)
        (bodies (list-of expression?))])

  
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
(define 4th cadddr)

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
  (lambda (e)
    (and (symbol? (car e)) ((list-of expression?) (cdr e)))))

(define improper?
  (lambda (ls)
    (let check ([rest ls])
      (cond [(null? rest) #t]
        [(symbol? rest) #t]
        [else (and (symbol? (car rest)) (check (cdr rest)))]))))

(define lit?
  (lambda (e)
    (or (number? e)
      (string? e)
      (symbol? e)
      (boolean? e)
      (char? e)
      (vector? e)
      (list? e))))

(define tillsym ; gets required args from improper lambda 
  (lambda (var)
    (if (symbol? var)
      '()
      (cons (car var) (tillsym (cdr var))))))
(define endsym ; gets optional arg from improper lambda
  (lambda (var)
    (if (symbol? var)
      var
      (endsym (cdr var)))))

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
            [(and (not ((list-of symbol?) (2nd datum))) (pair? (2nd datum)))
              (lambda-exp-improper (tillsym (2nd datum)) (endsym (2nd datum)) (map parse-exp (cddr datum)))]
            [(list? (2nd datum))
              (if (andmap symbol? (cadr datum))
                (lambda-exp (2nd datum) (map parse-exp (cddr datum)))
                (eopl:error 'parse-exp "lambda argument list: formals must be symbols: ~s" datum))]
        [else (eopl:error 'parse-exp "Incorrect lambda syntax: ~s" datum)])]
    ;;if expression
    [(eqv? 'if (1st datum))
      (cond
        [(= 2 (length datum))
          (eopl:error 'parse-exp "missing then and else parts: ~s" datum)]
        [(= 3 (length datum))
          (if-then-exp (parse-exp (2nd datum)) (parse-exp (3rd datum)))]
        [(= 4 (length datum))
          (if-else-exp (parse-exp (2nd datum))
                 (parse-exp (3rd datum))
                 (parse-exp (4th datum)))]
        [else
          (eopl:error 'parse-exp "if-expression: ~s does not have the right format: condition, then, else" datum)])]
    ;;let expression
     [(eqv? (1st datum) 'let)
      (cond
         [(< (length datum) 3)
                        (eopl:error 'parse-exp "incorrect number of arguments for ~s" datum)]
         [(and (not (list? (2nd datum)))
                          (not (symbol? (2nd datum))))
                        (eopl:error 'parse-exp "not all lists are proper in ~s" datum)]
         [(and (list? (2nd datum)) (ormap (lambda (x) (not (eq? (length x) 2))) (2nd datum)))
                        (eopl:error 'parse-exp "not all length 2: ~s" datum)]
         [(and (null? (caddr datum)) (ormap list? (2nd datum)))
                        (eopl:error 'parse-exp "not proper: ~s" datum)]
         [(not (symbol? (2nd datum)))
                        (let-exp (map car (2nd datum)) (map parse-exp (map cadr (2nd datum))) (map parse-exp (cddr datum)))]
         [else (let-named-exp (2nd datum) (map car (3rd datum)) (map parse-exp (map cadr (3rd datum))) (map parse-exp (cdddr datum)))])]

 [(eqv? (1st datum) 'let*)
    (cond
       [(< (length datum) 3)
                      (eopl:error 'parse-exp "incorrect number of arguments for ~s" datum)]
       [(not (list? (2nd datum)))
                      (eopl:error 'parse-exp "no body in ~s" datum)]
       [(ormap (lambda (x) (not (eq? (length x) 2))) (2nd datum))
                      (eopl:error 'parse-exp "not all length 2: ~s" datum)]
       [else (let*-exp (map car (2nd datum)) (map parse-exp (map cadr (2nd datum))) (map parse-exp (cddr datum)))])]

 [(eqv? (1st datum) 'letrec)
    (cond
       [(< (length datum) 3)
                      (eopl:error 'parse-exp "incorrect number of arguments for ~s" datum)]
       [(not (list? (2nd datum)))
                      (eopl:error 'parse-exp "no body in ~s" datum)]
       [(ormap (lambda (x) (not (eq? (length x) 2))) (2nd datum))
                      (eopl:error 'parse-exp "not all length 2: ~s" datum)]
       [else (letrec-exp (map car (2nd datum)) ;;check the proper list
                         (map cadr (map cadr (cadr datum)))
                         (map parse-exp (map caddr (map cadr (cadr datum))))
                         (map parse-exp (cddr datum)))])]
          [(eqv? (1st datum) 'or)
            (or-exp (map parse-exp (cdr datum)))]
          [(eqv? (1st datum) 'cond)
            (cond-exp (map parse-exp (map car (cdr datum))) (map parse-exp (map cadr (cdr datum))))]
          [(eqv? (1st datum) 'begin)
            (begin-exp (map parse-exp (cdr datum)))]
          [(eqv? (1st datum) 'and)
            (and-exp (map parse-exp (cdr datum)))]
          [(eqv? (1st datum) 'case)
            (case-exp (parse-exp (cadr datum)) (map (lambda (x) (if (list? x) (map parse-exp x) (parse-exp x))) (map car (cddr datum))) (map parse-exp (map cadr (cddr datum))))]
          [(eqv? (1st datum) 'while)
            (while-exp (parse-exp (cadr datum)) (map parse-exp (cddr datum)))]
          [else (app-exp (parse-exp (1st datum))
              (map parse-exp (cdr datum)))])]
      [else (eopl:error 'parse-exp "bad expression: ~s" datum)]
      )))

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
      [if-then-exp (condition-exp true-exp) 
            (list 'if (unparse-exp condition-exp) (unparse-exp true-exp))]
      [if-else-exp (condition-exp true-exp false-exp) 
            (list 'if (unparse-exp condition-exp) (unparse-exp true-exp) (unparse-exp false-exp))]
      ;[let-named-exp (name ls body)]
      ;[let-exp (var exp body) 
      ;    (cons* 'let (map unparse-exp var) (map unparse-exp body))]
      ;;[single-let-exp (var body) 
      ;;      (list (unparse-exp var) (unparse-exp body))]
      ;;[named-let-exp (name ls body) (cons 'let 
      ;;    (cons (unparse-exp name) (cons (map unparse-exp ls) (map unparse-exp body))))]
      ;[let*-exp (ls body) (cons* 'let* 
      ;    (cons (map unparse-exp ls) (map unparse-exp body)))]
      ;[letrec-exp (ls body) (cons* 'letrec 
      ;    (cons (map unparse-exp ls) (map unparse-exp body)))]
      [let-exp (ids vals body)
        (cons 'let
           (cons (matrix-transpose (list ids (map unparse-exp vals)))
              (map unparse-exp body)))]
      [let*-exp (ids vals body)
        (cons 'let*
           (cons (matrix-transpose (list ids (map unparse-exp vals)))
              (map unparse-exp body)))]
      [letrec-exp (ids vals body)
        (cons 'letrec
           (cons (matrix-transpose (list ids (map unparse-exp vals)))
              (map unparse-exp body)))]
      [let-named-exp (name ids vals body)
        (cons* 'let name
           (cons (matrix-transpose (list ids (map unparse-exp vals)))
              (map unparse-exp body)))]

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

(define extend-env-recursively
  (lambda (proc-names idss bodiess old-env)
    (recursively-extended-env-record
      proc-names idss bodiess old-env)))

(define extend-env-recursively-improper
  (lambda (proc-names improper proper old-env)
    (recursively-extended-env-record-improper proc-names improper proper old-env)))

(define get-improper-first
  (lambda (ls)
    (if (symbol? ls)
      '()
      (cons
        (car ls)
        (get-improper-first (cdr ls))))))

(define get-improper-last
  (lambda (ls)
    (if (symbol? ls)
      ls
      (get-improper-last (cdr ls)))))

(define apply-env
    (lambda (env sym succeed fail) ; succeed and fail are procedures applied if the var is or isn't found, respectively.
        (cases environment env
            [empty-env-record ()
                (fail)]
            [extended-env-record (syms vals env)
              (let ((pos (list-find-position sym syms)))
                     (if (number? pos)
                     (succeed (list-ref vals pos))
                     (apply-env env sym succeed fail)))]
            [recursively-extended-env-record
              (procnames idss bodiess old-env)
              (let ([pos
                      (list-find-position sym procnames)])
              (if (number? pos)
                (closure
                  (list-ref idss pos)
                  (list(list-ref bodiess pos))
                  env)
              (apply-env old-env sym succeed fail)))]
            [recursively-extended-env-record-improper 
              (procnames idss bodiess old-env)
              (let ([pos 
                      (list-find-position sym procnames)])
              (if (number? pos)
                (if (and (not (list? (list-ref idss pos))) (pair? (list-ref idss pos)))
                  (closure-improper 
                    (get-improper-first(list-ref idss pos))
                    (get-improper-last(list-ref idss pos))
                    (list(list-ref bodiess pos))
                    env)
                  (closure 
                    (list-ref idss pos)
                    (list(list-ref bodiess pos))
                    env))
                (apply-env old-env sym succeed fail)))])))

;-----------------------+
;                       |
;   SYNTAX EXPANSION    |
;                       |
;-----------------------+

(define syntax-expand
  (lambda (exp)
    (cases expression exp
        [lit-exp (datum) exp]
        [var-exp (datum) exp]
        [app-exp (rator rands)
                (app-exp (syntax-expand rator) (map syntax-expand rands))]
        [quote-exp (datum) exp]
        [if-then-exp (test true)
                (if-then-exp (syntax-expand test) (syntax-expand true))]
        [if-else-exp (test true false)
                (if-else-exp (syntax-expand test)
                              (syntax-expand true)
                              (syntax-expand false))]
        [let-exp (vars exps bodies)
                (app-exp (lambda-exp vars (map syntax-expand bodies)) 
                  (map syntax-expand exps))]
        [letrec-exp (vars exps bodies letrec-bodies)
          (letrec-exp vars exps
            (map syntax-expand bodies)
            (map syntax-expand letrec-bodies))]
       [let-named-exp (name vars bodies body)
          (letrec-exp (list name) (list vars) (map syntax-expand body)
            (list (app-exp (var-exp name) bodies)))]
        [lambda-exp (ids bodies)
                (lambda-exp ids (map syntax-expand bodies))]
        [lambda-exp-improper (vars opt bodies)
                (lambda-exp-improper vars opt (map syntax-expand bodies))]
        [cond-exp (args bodies)
             (cond-loop args bodies)]
;        [or-exp (bodies)
;                (or-loop (map syntax-expand bodies))]
        [or-exp (var) 
          (let help ([val var])
           (cond [(null? val) (lit-exp #f)]
              [(null? (cdr val)) (syntax-expand (car val))]
              [else 
                (app-exp
                  (lambda-exp 
                    (list 'x)
                    (list 
                      (if-else-exp 
                        (var-exp 'x)
                        (var-exp 'x)
                        (help (cdr val))))) 
                  (list (syntax-expand (1st val))))]))]
        [begin-exp (bodies)
                (app-exp (lambda-exp '() (map syntax-expand bodies)) '())]
        [and-exp (bodies)
                (and-loop (map syntax-expand bodies))]
        [case-exp (tests vars bodies)
                (case-loop tests vars bodies)]
        [while-exp (test bodies)
                (while-exp (syntax-expand test) (map syntax-expand bodies))]
        [else (eopl:error 'syntax-expand "Bad syntax expansion ~s" exp)])))


(define cond-loop
  (lambda (args bodies)
    (cond
      [(null? (cdr args))
        (if (equal? (car args) (var-exp 'else))
        (syntax-expand (car bodies))
        (if-then-exp (syntax-expand (car args)) (syntax-expand (car bodies))))]
      [else (if-else-exp (syntax-expand (car args)) (syntax-expand (car bodies)) (cond-loop (cdr args) (cdr bodies)))])))

(define and-loop
  (lambda (bodies)
    (cond
      [(null? bodies) (list-exp #t)]
      [else (if (null? (cdr bodies))
            (if-else-exp (syntax-expand (car bodies)) (syntax-expand (car bodies)) (lit-exp #f))
            (if-else-exp (syntax-expand (car bodies)) (and-loop (cdr bodies)) (lit-exp #f)))])))

(define case-loop
  (lambda (tests vars bodies)
    (cond
      [(equal? (car vars) (var-exp 'else)) (car bodies)]
      [else (if-else-exp (app-exp (var-exp 'member) (list tests (app-exp (var-exp 'list) (car vars))))
                         (syntax-expand (car bodies))
                         (case-loop tests (cdr vars) (cdr bodies)))])))




;-------------------+
;                   |
;   INTERPRETER     |
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
      [lambda-exp-improper (ids opt bodies)
        (closure-improper ids opt bodies env)]
      [lambda-exp (ids bodies)
          (closure ids bodies env)]
      [let-exp (vars exps bodies)
        (let ([new-env (extend-env vars
                                   (eval-rands exps env)
                                   env)])
          (eval-bodies bodies new-env))]
      [letrec-exp (proc-names idss bodiess letrec-bodies)
        (eval-bodies letrec-bodies
          (extend-env-recursively
            proc-names idss bodiess env))]
      [if-then-exp (test-exp then-exp)
        (if (eval-exp test-exp env)
          (eval-exp then-exp env))]
      [if-else-exp (test-exp then-exp else-exp)
        (if (eval-exp test-exp env)
          (eval-exp then-exp env)
          (eval-exp else-exp env))]
;;      [quote-exp (datum) datum]
      [while-exp (test bodies)
        (let recur ([test-result (eval-exp test env)])
          (if test-result
            (let recur2 ([bodies bodies])
              (if (not (null? bodies))
                (begin (eval-exp (car bodies) env)
                  (recur2 (cdr bodies))
                  (recur (eval-exp test env)))))))]

      [else (eopl:error 'eval-exp "Bad abstract syntax: ~a" exp)])))



; evaluate the list of operands, putting results into a list

(define eval-rands
  (lambda (rands env)
    (map (lambda (x) (eval-exp x env)) rands)))

(define (eval-rands-wo-map rands env)
  (if (null? (cdr rands))
    (eval-exp (car rands) env)
    (begin (eval-exp (car rands) env)
            (eval-rands-wo-map (cdr rands) env))))

;  Apply a procedure to its arguments.
;  At this point, we only have primitive procedures.  
;  User-defined procedures will be added later.

(define apply-proc
  (lambda (proc-value args)
    (cases proc-val proc-value
        [prim-proc (op) (apply-prim-proc op args)]
      ; You will add other cases
        [closure (vars bodies env) (cond 
                                      [(symbol? vars) 
                                        (let single-lambda-loop ([bodies bodies])
                                          (if (null? (cdr bodies))
                                            (eval-exp (car bodies) (extend-env (list vars) (list args) env))
                                            (begin
                                              (eval-exp (car bodies) (extend-env (list vars) (list args) env))
                                              (single-lambda-loop (cdr bodies)))))]
                                      [((list-of symbol?) vars)
                                            (let eval-loop ([bodies bodies]
                                                            [env (extend-env vars args env)])
                                                            (cond
                                                                [(null? (cdr bodies)) (eval-exp (car bodies) env)]
                                                                [else (begin (eval-exp (car bodies) env) (eval-loop (cdr bodies) env))]))]
                                      [else (eval-rands bodies (extend-env (list vars) (list args) env))])]
        [closure-improper (vars improper-var bodies env) 
            (eval-rands-wo-map bodies (extend-env (append vars (list improper-var))
                                            (make-improper args (length vars) 1) env))]
        [else (error 'apply-proc
                   "Attempt to apply bad procedure: ~s" 
                    proc-value)])))
(define (make-improper args lenvars start)
  (if (equal? lenvars start)
    (cons (car args) (list (cdr args)))
    (cons (car args) (make-improper (cdr args) lenvars (+ 1 start)))))

(define *prim-proc-names* '(+ - * / add1 sub1 cons = < > <= >= not zero?
    car cadr cdr caar cadar cddar cddr caddr caadr cdddr list null? eq? equal? eqv? atom? length list->vector list? 
    pair? procedure? vector->list vector-list vector make-vector vector-ref vector? number?
    symbol? set-car! set-cdr! vector-set! display newline apply map quotient member list-tail append))

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
            [(cadar) (car (cdr (car args)))]
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
            [(vector-list) (vector-list args)]
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
            [(apply) (apply-proc (car args) (cadr args))]
            [(map) (map (lambda (x) (apply-proc (car args) x)) (map list (cadr args)))]
            [(quotient) (apply quotient args)]
            [(member) (member (1st args) (2nd args))]
            [(list-tail) (list-tail (1st args) (2nd args))]
            [(append) (append (1st args) (2nd args))]
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
  (lambda (x) (eval-exp (syntax-expand (parse-exp x)) init-env)))