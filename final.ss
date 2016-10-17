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
    [if-then-exp 
        (test expression?)
        (true expression?)]
    [let-exp
        (vars (list-of expression?))
        (exps (list-of expression?))
        (bodies (list-of expression?))]
    [let*-exp
        (vars (list-of expression?))
        (exps (list-of expression?))
        (bodies (list-of expression?))]
    [letrec-exp
        (proc-names (list-of symbol?))
        (idss (lambda (x) (or (list-of (list-of symbol?)))))
        (bodies (list-of expression?))
        (letrec-body (lambda (x) (or (expression? x)((list-of expression?) x))))]
    [letrec-exp-improper
        (proc-names (list-of symbol?))
        (idss (lambda (x) (or (list-of (list-of symbol?)))))
        (bodies (list-of expression?))
        (letrec-body (lambda (x) (or (expression? x)((list-of expression?) x))))]
    [lambda-exp 
        (vars (lambda (x) (or (expression? x)((list-of expression?) x))))
        (bodies (lambda (x) (or (expression? x)((list-of expression?) x))))]
    ;(lambda (x y . z))
    [lambda-exp-improper 
        (vars (list-of expression?))
        (extra-vars symbol?)
        (bodies (list-of expression?))]
    [cond-exp
        (exps (list-of expression?))]
    [begin-exp
        (exps (list-of expression?))]
    [set!-exp
        (var (expression?))
        (ex (lambda (x) (or (expression? x) ((list-of expression?) x))))]
    [or-exp
        (exps (list-of expression?))]
    [and-exp
        (exps (list-of expression?))]
    [case-exp
        (eva (lambda (x) (or (expression? x)((list-of expression?) x))))
        (cases (list-of expression?))]
    [while-exp
        (test-exp (lambda (x) (or (expression? x) ((list-of expression?) x))))
        (then-exp expression?)])

  
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

(define parse-exp         
  (lambda (datum)
    (cond
      [(symbol? datum) (var-exp datum)]
      [(number? datum) (lit-exp datum)]
      [(lit? datum) (lit-exp datum)]
      [(pair? datum)
        (cond 
          [(eqv? 'and (1st datum)) 
            (and-exp-p datum)]
          [(eqv? 'or (1st datum)) 
            (or-exp-p datum)]
          [(eqv? 'lambda (1st datum)) 
            (lambda-exp-p datum)]
          [(eqv? 'if (1st datum)) 
            (if-exp-p datum)]
          [(eqv? 'let (1st datum)) 
            (let-exp-p datum 'let)]
          [(eqv? 'letrec (1st datum)) 
            (let-exp-p datum 'letrec)]
          [(eqv? 'let* (1st datum)) 
            (let-exp-p datum 'let*)]
          [(eqv? 'set! (1st datum)) 
            (set-exp-p datum)]
          [(eqv? 'begin (1st datum)) 
            (begin-exp-p datum)]
          [(eqv? 'quote (1st datum)) 
            (quote-exp-p (cadr datum))]
          [(eqv? 'cond (1st datum)) 
            (cond-exp-p datum)]
          [(eqv? 'while (1st datum)) 
            (while-exp-p datum)]
          [(eqv? 'case (1st datum)) 
            (case-exp-p datum)]
          [(not (list? datum)) 
            (eopl:error 'parse-exp "expression ~s is not a proper list" datum)]
         [else (app-exp (parse-exp (1st datum))
           (map parse-exp (cdr datum)))])]
     [else (eopl:error 'parse-exp "bad expression: ~s" datum)])))

;;helper, check whether the list are all symbol
;(define list-of-expression?
;  [lambda (e)
;    (if (list? e) (andmap expression? e) #f)])

;(define lambda-var?
;  (lambda (e)
;    (and (symbol? (car e)) ((list-of expression?) (cdr e)))))

(define all-sym? (lambda (lst)
  (cond [(null? lst) #t]
    [(and (symbol? (car lst)) (symbol? (cdr lst))) 'improper]
    [(symbol? (car lst)) (all-sym? (cdr lst))]
    [else #f])))

(define lit?
  (lambda (e)
    (or (number? e)
      (string? e)
      (symbol? e)
      (boolean? e)
      (char? e)
      (vector? e)
      (list? e))))

;(define lit? (lambda (datum)
;  (ormap 
;       (lambda (pred) (pred datum))
;    (list number? vector? boolean? symbol? string? pair? null?))))

(define cond-exp-list (lambda (ele)
  (list (parse-exp (1st ele)) 
        (parse-exp (2nd ele)))))  

(define while-exp-p (lambda (datum)
  (list 'while-exp (parse-exp (2nd datum)) 
                  (begin-exp-p (cdr datum)))))

(define cond-exp-p (lambda (datum)
  (list 'cond-exp (map cond-exp-list (cdr datum)))))

(define case-exp-list (lambda (ele)
  (if (list? (1st ele)) 
    (list (keys-list-exp (1st ele)) (parse-exp (2nd ele)))
    (list (parse-exp (1st ele)) (parse-exp (2nd ele))))))

(define case-exp-p (lambda (datum)
  (list 'case-exp (parse-exp (2nd datum)) 
    (map case-exp-list (cddr datum)))))

(define and-exp-p (lambda (datum)
  (list 'and-exp (parse-exp-list (cdr datum)))))

(define or-exp-p (lambda (datum)
  (list 'or-exp (parse-exp-list (cdr datum)))))
  
(define begin-exp-p (lambda (datum)
  (list 'begin-exp (parse-exp-list (cdr datum)))))
  
(define quote-exp-p (lambda (datum)
  (list 'quote-exp datum)))
  
(define vec-exp-p (lambda (datum)
  (list 'vec-exp datum)))
   
(define var-exp-p (lambda (datum)
  (list 'var-exp datum)))

(define lit-exp-p (lambda (datum)
  (list 'lit-exp datum)))
  
(define app-exp-p (lambda (func var)
  (list 'app-exp func var)))
  
(define set-exp-p (lambda (datum)
  (cond 
    [(not (eqv? 3 (length datum))) 
          (eopl:error 'parse-exp "set! expression ~s does not have (only) variable and expression" datum)]
    [else (list 'set!-exp (parse-exp (2nd datum)) (parse-exp (3rd datum)))])))

(define let-exp-p (lambda (datum type)
  (cond 
    [(not (>= (length datum) 3)) 
      (eopl:error 'parse-exp "~s-expression has incorrect length ~s" datum)]
    [(not (list? (2nd datum))) 
      (list 'letrec-exp 
          (parse-exp-list (list (2nd datum))) 
          (list (map 1st (3rd datum)))
          (parse-exp-list (cdddr datum))
          (list(parse-exp (cons (2nd datum) (map 2nd (3rd datum))))))]
    [(not (andmap list? (2nd datum))) 
      (eopl:error 'parse-exp "declaration in ~s-exp is not a proper list ~s" datum)]
    [(not (andmap (lambda (lst) (eqv? 2 (length lst))) (2nd datum))) 
      (eopl:error 'parse-exp "declaration in ~s-exp must be a list of length 2 ~s" datum)]
    [(not (andmap (lambda (lst) (symbol? (1st lst))) (2nd datum))) 
      (eopl:error 'parse-exp "vars in ~s-exp must be symbols ~s" datum)]
    [else 
      (cond 
          [(eqv? 'let type)(list 'let-exp (parse-exp-list (map 1st (2nd datum)))(parse-exp-list (map 2nd (2nd datum))) (parse-exp-list (cddr datum)))]
          [(eqv? 'let* type)(list 'let*-exp (parse-exp-list (map 1st (2nd datum)))(parse-exp-list (map 2nd (2nd datum))) (parse-exp-list (cddr datum)))]
          [(eqv? 'letrec type)
            (list 'letrec-exp 
              (parse-exp-list (map 1st (2nd datum)))
              (map 2nd (map 2nd (2nd datum)))
              (parse-exp-list(map 3rd (map 2nd (2nd datum))))
              (parse-exp-list(cddr datum)))]
          [else (eopl:error 'parse-exp "invalid let expression ~s" datum)])]))) 

(define parse-exp-list (lambda (lst)
  (if (null? lst) '() 
  (append (list(parse-exp (1st lst))) (parse-exp-list (cdr lst))))))

(define parse-exp-improper-lambda-args (lambda (lst) 
  (cond
    [(and (symbol? (car lst)) (symbol? (cdr lst))) (parse-exp (car lst))]
    [else (append (list (parse-exp (1st lst)) (parse-exp-improper-lambda-args (cdr lst))))])))

(define parse-exp-improper-lambda-extra (lambda (lst) 
  (cond
    [(and (symbol? (car lst)) (symbol? (cdr lst))) (parse-exp (cdr lst))]
    [else (parse-exp-improper-lambda-extra (cdr lst))])))

(define if-exp-p (lambda (datum) 
  (cond
    [(equal? 3 (length datum)) (list 'if-exp (parse-exp (2nd datum))
     (parse-exp (3rd datum)) (lit-exp (list (void))))]
    [(equal? 4 (length datum)) (list 'if-exp (parse-exp (2nd datum))
      (parse-exp (3rd datum)) (parse-exp (4th datum)))]
    [else (eopl:error 'parse-exp 
      "if-expression ~s does not have the form if-then-else or if-then" datum)])))
  
(define lambda-exp-p (lambda (datum)
  (cond 
    [(not (>= (length datum) 3)) 
      (eopl:error 'parse-exp "lambda-expression: incorrect length ~s" datum)]
    [(symbol? (2nd datum)) (cond ;Case when variable # args allowed
      [(not (>= (length datum) 3)) 
        (eopl:error 'parse-exp "lambda-expression missing body")]
      [else (list 'lambda-exp (parse-exp (2nd datum)) (parse-exp-list (cddr datum)))])]
    [(not (all-sym? (2nd datum))) 
      (eopl:error 'parse-exp "lambda's formal arguments ~s must all be symbols" datum)]
    [(equal? 'improper (all-sym? (2nd datum))) 
      (list 'lambda-exp-improper (parse-exp-improper-lambda-args (2nd datum)) 
                      (parse-exp-improper-lambda-extra (2nd datum)) (parse-exp-list (cddr datum)))]
    [(list? (2nd datum)) 
      (list 'lambda-exp (parse-exp-list (2nd datum)) (parse-exp-list (cddr datum)))])))
;(define tillsym ; gets required args from improper lambda 
;  (lambda (var)
;    (if (symbol? var)
;      '()
;      (cons (car var) (tillsym (cdr var))))))

;(define endsym ; gets optional arg from improper lambda
;  (lambda (var)
;    (if (symbol? var)
;      var
;      (endsym (cdr var)))))

;(define parse-exp
;  (lambda (datum)
;    (cond
;     [(and (list? datum) (eq? 'quote (1st datum)))
;      (if (> (length datum) 2)
;        (eopl:error 'parse-exp "Invalid syntax for quote: ~s" datum)
;        (lit-exp (cadr datum)))]
;   [((lambda (e)
;    (or (number? e)
;      (string? e)
;      (boolean? e)
;      (char? e)
;      (vector? e))) datum) (lit-exp datum)]
;   [(symbol? datum) (var-exp datum)]
;     ;;set! expression
;     [(eqv? (1st datum) 'set!)
;      (cond
;        [(> (length datum) 3)
;          (eopl:error 'parse-exp "Too many parts: ~s" datum)]
;      [(= (length datum) 3)
;        (if (symbol? (2nd datum))
 ;           (set!-exp (parse-exp (2nd datum)) (parse-exp (3rd datum)))
;          (eopl:error 'parse-exp "declaration in set-expression ~s must take a symbol" (2nd datum)))]
;      [else (eopl:error 'parse-exp "set expression ~s has incorrect arguments" datum)])]
;     [(pair? datum)
;      (cond
;        [(not (list? datum))
;          (eopl:error 'parse-exp "expression ~s is an improper list" datum)]
;        ;;lambda expression
;    [(eqv? (car datum) 'lambda)
;          (cond
;            [(< (length datum) 3)
;              (eopl:error 'parse-exp "lambda expression: ~s" datum)]
;            [(symbol? (2nd datum))
;              (lambda-exp (2nd datum) (map parse-exp (cddr datum)))]
;            [(and (not ((list-of symbol?) (2nd datum))) (pair? (2nd datum)))
;              (lambda-exp-improper (tillsym (2nd datum)) (endsym (2nd datum)) (map parse-exp (cddr datum)))]
;            [(list? (2nd datum))
;              (if (andmap symbol? (cadr datum))
;                (lambda-exp (2nd datum) (map parse-exp (cddr datum)))
;                (eopl:error 'parse-exp "lambda argument list: formals must be symbols: ~s" datum))]
;        [else (eopl:error 'parse-exp "Incorrect lambda syntax: ~s" datum)])]
;    ;;if expression
;    [(eqv? 'if (1st datum))
;      (cond
;        [(= 2 (length datum))
;          (eopl:error 'parse-exp "missing then and else parts: ~s" datum)]
;        [(= 3 (length datum))
;          (if-then-exp (parse-exp (2nd datum)) (parse-exp (3rd datum)))]
;        [(= 4 (length datum))
;          (if-else-exp (parse-exp (2nd datum))
;                 (parse-exp (3rd datum))
;                 (parse-exp (4th datum)))]
;        [else
;          (eopl:error 'parse-exp "if-expression: ~s does not have the right format: condition, then, else" datum)])]
 ;   ;;let expression
;    [(or (eqv? 'let (1st datum)) (eqv? 'letrec (1st datum)) (eqv? 'let* (1st datum)));;check whether the 1st datum meeet any let type
;      (cond
;        [(< (length datum) 3) (eopl:error 'parse-exp "let-expression has incorrect length")]
;        [else
;          (letrec ([parse-let
;            (trace-lambda parselet (ls)
;              (trace-let helper ((rest ls))
;                (cond
;                  [(null? rest) (list)]
;                  [(not (list? rest)) (eopl:error 'parse-exp "~s-list is not a proper list" (1st datum) rest)]
;                  [(not (list? (car rest))) (eopl:error 'parse-exp "declaration in ~s-list is not a proper list" (1st datum) (car rest))]
;                  [(not (= 2 (length (car rest)))) (eopl:error 'parse-exp "declaration in ~s-list must be in length of two ~s" (1st datum) (car rest))]
;                  [(not (symbol? (caar rest))) (eopl:error 'parse-exp "variable in ~s must be a symbol ~s" (1st datum) (caar rest))]
;                  [else
;                    (cons (single-let-exp (parse-exp (caar rest))
;                                          (parse-exp (cadar rest)))
;                                          (helper (cdr rest)))])))])
;              (cond
;                [(symbol? (2nd datum))
;                (cond
;                  [(= 3 (length datum)) (eopl:error 'parse-exp "named-let-exp has incorrect length ~s" datum)]
;                  [(not (eqv? 'let (1st datum))) (eopl:error 'parse-exp "declaration in ~s must be a proper list ~s" (1st datum) (2nd datum))]
;                  [else (named-let-exp (var-exp (2nd datum))
;                            (parse-let (3rd datum))
;                            (map parse-exp (cdddr datum)))])]
;                [(eqv? 'let (1st datum))
;                  (let-exp (parse-let (2nd datum)) (map parse-exp (cddr datum)))]
;                [(eqv? 'let* (1st datum))
;                  (let*-exp (parse-let (2nd datum)) (map parse-exp (cddr datum)))]
;                [else
;                  (letrec-exp (parse-let (2nd datum)) (map parse-exp (cddr datum)))]))])]
;          [(eqv? (1st datum) 'or)
;            (or-exp (map parse-exp (cdr datum)))]
;          [(eqv? (1st datum) 'cond)
;            (cond-exp (map parse-exp (map car (cdr datum))) (map parse-exp (map cadr (cdr datum))))]
;          [(eqv? (1st datum) 'begin)
;            (begin-exp (map parse-exp (cdr datum)))]
;          [(eqv? (1st datum) 'and)
;            (and-exp (map parse-exp (cdr datum)))]
;          [(eqv? (1st datum) 'case)
;            (case-exp (cadr datum) (map car (cddr datum)) (map parse-exp (map cadr (cddr datum))))]
;          [(eqv? (1st datum) 'while)
;            (while-exp (parse-exp (cadr datum)) (map parse-exp (cddr datum)))]
;          [else (app-exp (parse-exp (1st datum))
;              (map parse-exp (cdr datum)))])]
;      [else (eopl:error 'parse-exp "bad expression: ~s" datum)]
;      )))

(define unparse-exp (lambda (datum)
  (cond
    [(eqv? (1st datum) 'lambda-exp)
      (cond 
        [(null? (2nd datum)) (append (list 'lambda) (list '()) (unparse-exp-list (3rd datum)))]
        [(eqv? 'var-exp (1st(2nd datum)))(append (list 'lambda) (list (2nd (2nd datum))) (unparse-exp-list (3rd datum)))]
        [else (append (list 'lambda) (list(unparse-exp-list (2nd datum))) (unparse-exp-list (3rd datum)))])]
    [(eqv? (1st datum) 'var-exp)(2nd datum)]
    [(eqv? (1st datum) 'lit-exp)(2nd datum)]
    [(eqv? (1st datum) 'vec-exp)(2nd datum)]
    [(eqv? (1st datum) 'if-exp)
      (append (list 'if) 
              (list(unparse-exp (2nd datum))) 
              (list(unparse-exp (3rd datum))) 
              (list(unparse-exp (4th datum))))]
    [(eqv? (1st datum) 'let-exp)
      (append (list 'let) (list(un-parse-let (2nd datum)(3rd datum)))(unparse-exp-list (4th datum)))]
    [(eqv? (1st datum) 'let*-exp)
      (append (list 'let*)(list(un-parse-let (2nd datum)(3rd datum)))(unparse-exp-list (4th datum)))]
    [(eqv? (1st datum) 'letrec-exp)
      (append (list 'letrec)(list(un-parse-let (2nd datum)(3rd datum)))(unparse-exp-list (4th datum)))]
    [(eqv? (1st datum) 'set!-exp)
      (append (list 'set) (unparse-exp (2nd datum)) (unparse-exp (3rd datum)))]
    [(eqv? (1st datum) 'app-exp)
      (append (list(unparse-exp (1st (2nd datum))))(unparse-exp-list (2nd (2nd datum))))]
    [else 
      (eopl:error 'unparse-exp "invalid unparse expression ~s" datum)])))

(define un-parse-let (lambda (var-lst exp-lst)
  (if 
    (or (null? var-lst) (null? exp-lst))
    '()
    (append
      (list(list 
        (unparse-exp (car var-lst)) 
        (unparse-exp (car exp-lst))))
      (un-parse-let
        (cdr var-lst)
        (cdr exp-lst))))))
    
(define unparse-exp-list (lambda (lst)
  (if 
    (null? lst)
    '()
    (append
      (list (unparse-exp (1st lst)))
      (unparse-exp-list (cdr lst))))))

;-------------------+
;                   |
;   ENVIRONMENTS    |
;                   |
;-------------------+

; Environment definitions for CSSE 304 Scheme interpreter.  Based on EoPL section 2.3

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

(define syntax-expand 
  (lambda (e)
    (cases expression e
      [let-exp 
        (vars exps bodies) 
        (app-exp (lambda-exp vars (map syntax-expand bodies)) exps)]
      [letrec-exp 
        (proc-names idss bodies letrec-body)
        (cond 
          [((list-of (list-of symbol?)) idss)
            (list 'letrec-exp proc-names idss (map syntax-expand bodies)(map syntax-expand letrec-body))]
          [else (list 'letrec-exp-improper proc-names idss (map syntax-expand bodies)(map syntax-expand letrec-body))])]
      [begin-exp (exps) 
        (begin-loop (reverse exps))]
      [if-exp (test-exp then-exp else-exp)
        (if-exp (syntax-expand test-exp) (syntax-expand then-exp) 
        (syntax-expand else-exp))]
      [cond-exp (exps) 
        (cond-expand exps)]
      [let*-exp (vars exps bodies) 
        (let*-expand vars exps bodies)]
      [case-exp (eva cases) 
        (case-expand eva cases)]
      [and-exp (exps) 
        (and-expand exps)]
      [or-exp (exps) 
        (or-expand exps)]
      [else e])))

(define begin-loop (lambda (exps)
  (let loop ([exps exps])
    (if (null? (cdr exps))
      (app-exp (lambda-exp (list) (list (car exps))) (list))
      (app-exp (lambda-exp (list (var-exp '_)) (list (car exps))) 
      (list (loop (cdr exps)))))))) 

(define cond-expand (lambda (exps) (let loop ([exps exps])
  (if (null? (cdr exps))
    (cadr (car exps))
    (if-exp (syntax-expand (car (car exps))) 
        (syntax-expand(cadr (car exps))) 
        (syntax-expand(loop (cdr exps))))))))

(define case-expand (lambda (eva cases) (let loop ([cases cases])
  (if (null? (cdr cases))
    (cadr (car cases))
    (if-exp (app-exp (parse-exp 'memv) (list (syntax-expand eva) (car (car cases)))) 
        (syntax-expand (cadr (car cases))) 
        (syntax-expand(loop (cdr cases))))))))

(define and-expand (lambda (exps)(let loop ([exps exps])
  (if (null? exps) (parse-exp #t) (if (null? (cdr exps))
    (car exps)
    (if-exp (syntax-expand (car exps))
        (loop (cdr exps))
        (lit-exp #f)))))))
  
(define or-expand (lambda (exps)(let loop ([exps exps])
  (if (null? exps) (parse-exp #f) (if (null? (cdr exps))
    (car exps)
    (if-exp (syntax-expand (car exps))
        (syntax-expand (car exps))
        (loop (cdr exps))))))))
        
(define let*-expand (lambda (vars exps bodies)
  (let loop ([vars vars] [exps exps])
    (if (or (null? (cdr exps))(null? (cdr vars)))
      (let-exp (list(car vars))(list (car exps)) bodies)
      (let-exp (list(car vars))(list (car exps)) (list (loop (cdr vars) (cdr exps)))))))) 

(define improper-expand (lambda (idss bodies)
  (let loop ([lst idss][blst bodies][resultID '()][resultBody '()])
    (if (or (null? lst) (null? blst))
      (list resultID resultBody)
      (if (and (not (list? (1st lst)))(pair? (1st lst)))
        (loop (cdr lst)(cdr blst) (cons (1st lst) resultID) (cons (1st blst) resultBody))
        (loop (cdr lst)(cdr blst) resultID resultBody))))))
  
(define proper-expand (lambda (idss bodies)
  (let loop ([lst idss][blst bodies][resultID '()][resultBody '()])
    (if (or (null? lst) (null? blst))
      (list resultID resultBody)
      (if (and (list? (1st lst))(pair? (1st lst)))
        (loop (cdr lst)(cdr blst) (cons (1st lst) resultID) (cons (1st blst) resultBody))
        (loop (cdr lst)(cdr blst) resultID resultBody))))))

;---------------------------------------



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
      [lambda-exp-improper (vars improper-var bodies) 
          (closure-improper (unparse-exp-list vars) (unparse-exp improper-var) bodies env)]
      [lambda-exp (vars bodies) 
          (cond
            [(expression? vars) (closure (unparse-exp vars) bodies env)]
            [((list-of expression?) vars)(closure (unparse-exp-list vars) bodies env)]
            [else (display vars)])]
      [quote-exp (datum) datum]
      [if-exp (test-exp then-exp else-exp)
        (if (eval-exp test-exp env)
            (eval-exp then-exp env)
            (eval-exp else-exp env))]
      [letrec-exp (proc-names idss bodies letrec-body)
        (cond [(and (pair? idss)(list? idss)) (eval-bodies letrec-body (extend-env-recursively
                (unparse-exp-list proc-names) idss bodies env))]
              [else (eopl:error 'eval-exp "Bad idss field: ~a" idss)])]
      [letrec-exp-improper (proc-names improper proper letrec-body)
        (eval-bodies letrec-body (extend-env-recursively-improper
                (unparse-exp-list proc-names) improper proper env))]
      [let-exp (vars exps bodies)
        (let ([new-env (extend-env (unparse-exp-list vars) (eval-rands exps env) env)])
        (eval-bodies bodies new-env))]
      [while-exp (test-exp then-exp) (letrec ([loop (lambda ()
        (if (eval-exp test-exp env) (begin (eval-exp (syntax-expand then-exp) env) (loop))
        (lit-exp (list (void)))))]) (loop))]
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
        [closure (vars bodies env) 
            (cond 
              [((list-of symbol?)vars)(eval-bodies bodies (extend-env vars args env))]
              [else (eval-bodies bodies (extend-env (list vars) (list args) env))])]
        [closure-improper (vars improper-var bodies env) 
            (eval-rands-wo-map bodies (extend-env (append vars (list improper-var))
                (make-improper args (length vars) 1) env))]
        [else (error 'apply-proc
                   "Attempt to apply bad procedure: ~s" 
                    proc-value)])))

;(define (make-improper args lenvars start)
;  (if (equal? lenvars start)
;    (cons (car args) (list (cdr args)))
;    (cons (car args) (make-improper (cdr args) lenvars (+ 1 start)))))

(define *prim-proc-names* '(+ - * / add1 sub1 cons = < > <= >= not zero?
    car cadr cdr caar cadar cddar cddr caddr caadr cdddr list null? eq? equal? eqv? atom? length list->vector list? 
    pair? procedure? vector->list vector-list vector make-vector vector-ref vector? number?
    symbol? set-car! set-cdr! vector-set! display newline apply map))

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
  (lambda (x) (top-level-eval (syntax-expand (parse-exp x)))))
