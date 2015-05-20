#lang eopl
(define empty-env
  (lambda () (list 'empty-env)))  

(define extend-env
(lambda (var val env)
(list 'extend-env var val env)))
(define apply-env1
  (lambda (env search-var)
    (cond
((eqv? (car env) 'empty-env) (report-no-binding-found search-var))
((eqv? (car env) 'extend-env) (let ((saved-var (cadr env))
             (saved-val (caddr env))
(saved-env (cadddr env))) (if (eqv? search-var saved-var)
saved-val
           (apply-env saved-env search-var))))
      (else
(report-invalid-env env)))))
(define apply-env
  (lambda (env search-var)
    (cond
((eqv? (car env) 'empty-env) search-var)
((eqv? (car env) 'extend-env) (let ((saved-var (cadr env))
             (saved-val (caddr env))
(saved-env (cadddr env))) (if (eqv? search-var saved-var)
saved-val
           (apply-env saved-env search-var))))
      (else
(report-invalid-env env)))))
(define report-no-binding-found
  (lambda (search-var)
(eopl:error 'apply-env "No binding for ~s" search-var)))
(define report-invalid-env
  (lambda (env)
(eopl:error 'apply-env "Bad environment: ~s" env)))

#(Citation: the environment part is from the text book)

#(Problem 1)

(define identifier? symbol?)
(define proc?
           (lambda (val)
             (procedure? val)))

(define expval->proc
    (lambda (proc)
      (cases expval proc
(proc-val (proc) proc)
(else ("error")))))

(define-datatype expval expval? (num-val
      (num number?))
    (symbol-val
      (symbol symbol?))
    (proc-val
      (proc proc?)))
(define apply-procedure
           (lambda (proc1 val)
             (proc1 val)))
(define procedure
           (lambda (var body env)
             (lambda (val)
(function body (extend-env var val env)))))


(define-datatype lc-exp lc-exp?
  (var-exp
(var identifier?))
  (lambda-exp
(bound-var identifier?)
(body lc-exp?))
  (app-exp
(rator lc-exp?) (rand lc-exp?)))
(define lambda-exp?
(lambda (x)
(and (pair? x) (eq? (car x) 'lambda-exp))))



(define lambda-interpret
  (lambda (exp)
    (if (symbol? (function (parse-expression exp) (empty-env)))
  (function (parse-expression exp) (empty-env))
  ((eopl:error "#procedure or data structure representing a prodedure" )))))

(define function
  (lambda (exp env)
    (cases lc-exp exp
    (var-exp (var) (apply-env env var))
      (lambda-exp (var body) (proc-val (procedure var body env)))
      (app-exp (rator rand)
               (let ((proc (expval->proc (function rator env)))
(arg (function rand env))) (apply-procedure proc arg)))
      (else "error"))))


(define parse-expression
    (lambda (datum)
      (cond
((symbol? datum) (var-exp datum)) 
((pair? datum)
(if (eqv? (car datum) 'lambda) 
    (lambda-exp
             (car (cadr datum))
(parse-expression (caddr datum))) (app-exp
(parse-expression (car datum))
(parse-expression (cadr datum)))))
(else (report-invalid-concrete-syntax datum)))))
(define report-invalid-concrete-syntax
  (lambda (datum)
"error"))
#(This parser is from the textbook)

#(Problem 2)

(define infix-interpreter
  (lambda (x)
    (value-of (foo x))))

(define foo
  (lambda (pgm)
    (scan&parse pgm)))



(define value-of
  (lambda (exp)
    (cond
      ((Concat-expr? exp)
       (cases Concat-expr exp
         (conc (c1 c2) 
               (if (null? c2)
                   (value-of c1)
                   (string->number (string-append  (number->string (value-of (conc c1 (cdr c2)))) (number->string (value-of (car c2)))))))))
      
      ((Arith-expr? exp)
       (cases Arith-expr exp
         (expr (x op y) 
               (if (null? op)
        (value-of x)
        ((value-of (car op)) (value-of (car y)) (value-of (expr x (cdr op) (cdr y))))))))
      
       ((Arith-term? exp)
       (cases Arith-term exp
         (term (x op y) 
               (if (null? op)
        (value-of x)
        ((value-of (car op)) (value-of (car y)) (value-of (term x (cdr op) (cdr y))))))))
              
        
      ((Arith-factor? exp)
      (cases Arith-factor exp
        (num (num1) num1)
        (cexpr (exp1) (value-of exp1))))
      
       ((Additive-op? exp)
        (cases Additive-op exp
          (sum() +)
          (minus() -)))
       ((Multiplicative-op? exp)
        (cases Multiplicative-op exp
          (multiply() *)
          (divide() /))))))       

(define grammar1
'(

   (Concat-expr (Arith-expr (arbno "concat-int" Arith-expr)) conc)
  (Arith-expr (Arith-term (arbno Additive-op Arith-term )) expr)
  
  (Arith-term (Arith-factor (arbno Multiplicative-op Arith-factor)) term)
                           
  (Arith-factor (number) num)
  
  (Arith-factor ("("Concat-expr")") cexpr)
  
  (Additive-op ("+") sum)
  (Additive-op ("-") minus)
  (Multiplicative-op ("*") multiply)
  (Multiplicative-op ("/") divide)
  ))

#(Problem 3)

(define expval->num
    (lambda (val)
      (cases expval val
(num-val (num) num)
(symbol-val (symbol) symbol)
(else ("error")))))

(define case-interpreter
  (lambda (x)
    (if (eq? 'undefined (value (g0 x) (empty-env)))
    'undefined
    (expval->num (value (g0 x) (empty-env)))
    )))

(define g0
  (lambda (pgm)
    (scan&parse1 pgm)))

(define value
  (lambda (exp env)
    (cases expression exp
      (num0 (num) (num-val num))
      (variable (var) (apply-env1 env var))
      (deduce (exp1 exp2) (let ((val1 (value exp1 env))
                             (val2 (value exp2 env))) 
                         (let ((num1 (expval->num val1))
                               (num2 (expval->num val2))) 
                           (num-val (- num1 num2)))))
      (letexpr (var expl body)
               (let ((val1 (value expl env)))
                 (value body 
                        (extend-env var val1 env))))
      (switchexpr (exp1 exp2 exp3)
                  (if (null? exp2)
                      'undefined
                  (if (eqv? (expval->num (value exp1 env)) (expval->num (value (car exp2) env)))
                       (value (car exp3) env)
                       (value (switchexpr exp1 (cdr exp2) (cdr exp3)) env))
      )))))


(define grammar2
'(                
  (expression (number) num0)
  (expression (identifier) variable)
  (expression ("-" "(" expression "," expression ")") deduce)
  (expression ("let" identifier "=" expression "in" expression) letexpr)
  (expression ("switch" expression "("(arbno "(" "case" expression "->" expression ")" ) ")") switchexpr)
  ))


(define lex0 
'((white-sp (whitespace) skip)
(comment ("%" (arbno (not #\newline))) skip) 
(identifier (letter (arbno (or letter digit))) symbol)
(number (digit (arbno digit)) number)))

(sllgen:make-define-datatypes lex0 grammar1)

(sllgen:make-define-datatypes lex0 grammar2)


(define lex1 
'((white-sp (whitespace) skip)
(comment ("%" (arbno (not #\newline))) skip) 
(identifier (letter (arbno (or letter digit))) symbol)
(number (digit (arbno digit)) number)))

 (define list-the-datatypes
    (lambda ()
(sllgen:list-define-datatypes lex0 grammar2)))

;; build a scanner (optional) 
(define just-scan
(sllgen:make-string-scanner lex0 grammar1))
;; build a parse
(define scan&parse
(sllgen:make-string-parser lex0 grammar1))
(define show-the-datatypes
(lambda () (sllgen:show-define-datatypes lex0 grammar1)))


(define scan&parse1
(sllgen:make-string-parser lex0 grammar2))

#(The SLLGEN part is from the textbook)






