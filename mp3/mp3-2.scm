#lang eopl

;;environment 
(define-datatype environment environment?
  (empty-env)
  (extend-env
   (bvar symbol?)
   (bval reference?)                 ; new for implicit-refs
   (saved-env environment?))
   (extend-env-rec
    (pname (list-of symbol?))
    (proc-bodies (list-of expression?))
    (saved-env environment?)
  ))

#(define apply-env
  (lambda (env search-sym)
    (cases environment env
           (empty-env ()
                      ("error"))
           (extend-env (var val saved-env)
                       (if (eqv? search-sym var)
                           val
                           (apply-env saved-env search-sym)))
           (extend-env-rec (p-name b-var p-body saved-env)
                           (if (eqv? search-sym p-name)
                               (proc-val (procedure b-var p-body env))
                               (apply-env saved-env search-sym))))))
(define apply-env
  (lambda (env search-var)
    (cases environment env
           (empty-env ()
                      ("emptyenv"))
           (extend-env (bvar bval saved-env)
                       (if (eqv? search-var bvar)
                           bval
                           (apply-env saved-env search-var)))
           (extend-env-rec (p-names p-bodies saved-env)
                       (let ((n (location search-var p-names)))
                             
                      (if n
                          (let (( body (list-ref p-bodies n)))
                            (cases expression body
                              (proc-exp (var body)
                                        
                                  (newref
                                   (proc-val
                                    (procedure
                                     var body
                                     ))))
                              (else (apply-env saved-env search-var))))
                            
                                  (apply-env saved-env search-var)))))))
(define location
  (lambda (sym syms)
    (cond
     ((null? syms) #f)
     ((eqv? sym (car syms)) 0)
     ((location sym (cdr syms))
      => (lambda (n)
           (+ n 1)))
     (else #f))))

(define extend-env*
  (lambda (vars vals env)
    (if (null? vars)
        env
        (let ((var1 (car vars))
              (val1 (car vals)))
          (extend-env* (cdr vars) (cdr vals) (extend-env var1 (newref val1) env))))))



(define report-no-binding-found
  (lambda (search-var)
(eopl:error 'apply-env "No binding for ~s" search-var)))
(define report-invalid-env
  (lambda (env)
(eopl:error 'apply-env "Bad environment: ~s" env)))

;;store
(define empty-store
  (lambda () '()))

(define the-store 'uninitialized)

(define get-store
  (lambda () the-store))
 (define initialize-store!
  (lambda ()
    (set! the-store (empty-store))))
(define reference?
  (lambda (v)
    (integer? v)))

(define newref
    (lambda (val)
      (let ((next-ref (length the-store)))
        (set! the-store
              (append the-store (list val)))
        (when (instrument-newref)
            (eopl:printf 
             "newref: allocating location ~s with initial contents ~s~%"
             next-ref val))                     
        next-ref))) 

  (define instrument-newref (make-parameter #f))

(define deref
(lambda (ref)
(list-ref the-store ref)))
(define setref!
    (lambda (ref val)
      (set! the-store
        (letrec
          ((setref-inner
(lambda (store1 ref1)
               (cond
                 ((null? store1)
("error")) ((zero? ref1)
                  (cons val (cdr store1)))
                 (else
                   (cons
                     (car store1)
                     (setref-inner
(cdr store1) (- ref1 1)))))))) (setref-inner the-store ref)))))
;;

(define identifier? symbol?)
(define-datatype proc proc?
  (procedure
   (var (list-of symbol?))
   (body expression?)
   ))

(define-datatype expval expval? (num-val
      (num number?))
    (symbol-val
      (symbol symbol?))
  (bool-val
      (bool boolean?))
    (proc-val
      (proc proc?))
  (ref-val
   (ref reference?)))





(define apply-procedure
  (lambda (proc1 args env)
    (cases proc proc1
           (procedure (vars body)
		      (let ((new-env (extend-env* vars args env)))
			(value body new-env))))))
#(define apply-procedure
  (lambda (proc1 val env)
    (cases proc proc1
           (procedure (var body)
                      (value body (extend-env* var val env))))))


(define eval-rands
  (lambda (rands env)
    (map (lambda (x) (eval-rand x env)) rands)))

(define eval-rand
  (lambda (rand env)
    (value rand env)))


(define expval->num
    (lambda (val)
      (cases expval val
(num-val (num) num)
(symbol-val (symbol) symbol)
(else ("error")))))

(define expval->proc
    (lambda (proc)
      (cases expval proc
(proc-val (proc) proc)
(else ("error")))))

(define expval->bool
    (lambda (val)
      (cases expval val
(bool-val (bool) bool)
(else "error"))))

(define expval->ref
    (lambda (v)
      (cases expval v
	(ref-val (ref) ref)
	(else "error"))))




(define dynamic-interpreter
  (lambda (x)
    
    (let ((value0 (value (g x) (empty-env))))
      (if (eqv? value0 'undefined)
          'undefined
     (cases expval value0
       (num-val(num) num)
       (bool-val(bool) (if (eq? bool #t) 'true
                           'false))
       (ref-val(ref) (expval->num(deref ref)))
       (else 'undefined))))))

(define g
  (lambda (pgm)
    (initialize-store!) 
    (scan&parse1 pgm)))

;;value-of
(define value-of-vals
  (lambda (vals env)
    (if (null? vals)
        '()
        (cons (value (car vals) env)
              (value-of-vals (cdr vals) env)))))
(define value
  (lambda (exp env)
    (cases expression exp
      (num0 (num) (num-val num))
      (variable (var)
                (cases environment env
                  (empty-env() 'undefined)
             (else (deref (apply-env env var)))))
      (errorexpr () 'undefined)
      (trueexpr () (bool-val #t))
      (falseexpr () (bool-val #f))
      (ArithmeticOp (op rands) 
                    (let ((valuess (eval-rands rands env)))
                      (apply-primitive op valuess)))
      
      (ComparisonOp (op exp1 exp2)
                    (apply-comparison op exp1 exp2 env))
      
  

      (letexpr (vars exps body)
		    (value body
			      (extend-env* vars (map (lambda(x)
						       (value x env))
						     exps) env)))
       (letrecexpr (pname exps body)
		    (value body
			      (extend-env-rec pname exps env)))
      
      
      
      (proc-exp (var body)
                     (proc-val (procedure var body)))
      
       (call-exp (rator rands)
                     (let ((proc (expval->proc (value rator env)))
                           (args (map (lambda(x) (value x env))
                                      rands)))
                       (apply-procedure proc args env)))
         
      
      (ifexpr (exp1 exp2 exp3)
              (let ((val1 (value exp1 env)))
                (if (expval->bool val1)
                    (value exp2 env)
                    (value exp3 env))))
      
        (newref-exp (exp1)
                  (let ((v1 (value exp1 env)))
                    (ref-val (newref v1))))
     
       (assign-exp (var exp1)
                  (cases environment env
                    (empty-env() 'undefined)
                    (else (begin
                            (setref!
                             (apply-env env var)
                             (value exp1 env))
                            (num-val 27)))))
      
      (begin-exp (exp1 exps)
          (letrec 
            ((value-of-begins
               (lambda (e1 es)
                 (let ((v1 (value e1 env)))
                   (if (null? es)
                     v1
                     (value-of-begins (car es) (cdr es)))))))
            (value-of-begins exp1 exps)))
      
      
      (switchexpr (exp1 exp2 exp3)
                  (if (null? exp2)
                      'undefined
                  (if (eqv? (expval->num (value exp1 env)) (expval->num (value (car exp2) env)))
                       (value (car exp3) env)
                       (value (switchexpr exp1 (cdr exp2) (cdr exp3)) env))
      )))))
  #(call-exp (rator rands)
                     (let ((proc (expval->proc (value rator env)))
                           (args (map (lambda(x) (value x env))
                                      rands)))
                       (apply-procedure proc args)))
#(compexpr (rator rand)
                (let ((proc (expval->proc (value rator env)))
                      (arg (value rand env))) (apply-procedure proc arg)))
  #(letexpr (var expl body)
                 (if (null? expl)
                 (value body env)
                 (let ((val1 (value (car expl) env)))
                 (value (letexpr (cdr var) (cdr expl) body) (extend-env (car var) val1 env)))))
 #(letexpr (var expl body)
                 (if (null? expl)
                 (value body env)
                 (let ((val1 (value (car expl) env)))
                 (value (letexpr (cdr var) (cdr expl) body) (extend-env (car var) (newref val1) env)))))

#(compexpr (rator rand)
                (if (null? (cdr rand))
                    (let ((proc (expval->proc (value rator env)))
                          (arg (value (car rand) env))) (apply-procedure proc arg))
                (let ((proc (expval->proc (value rator env)))
                      (arg (value (compexpr (car rand) (cdr rand)) env))) (apply-procedure proc arg))))
#(trace value)

(define apply-comparison
  (lambda (prim exp1 exp2 env)
    (let ((e1 (value exp1 env))
      (e2 (value exp2 env)))
    (cases primitivecomp prim
        (equal-prim () (if (= (cases expval e1 (num-val(num) num)(ref-val(ref) (expval->num(deref ref)))(else "error")) 
                                 (cases expval e2 (num-val(num) num)(ref-val(ref) (expval->num (deref ref)))(else "error")))
                           (bool-val #t) (bool-val #f)))
           (greater-prim () (if (> (cases expval e1 (num-val(num) num)(ref-val(ref) (expval->num(deref ref)))(else "error")) 
                                 (cases expval e2 (num-val(num) num)(ref-val(ref) (expval->num (deref ref)))(else "error")))
                                (bool-val #t) (bool-val #f)))
           (less-prim () (if (< (cases expval e1 (num-val(num) num)(ref-val(ref) (expval->num(deref ref)))(else "error")) 
                                 (cases expval e2 (num-val(num) num)(ref-val(ref) (expval->num (deref ref)))(else "error")))
                             (bool-val #t) (bool-val #f)))))))
      
      
      
      
(define apply-primitive
  (lambda (prim args)
    (let ((e1 (car args)))
    (cases primitive prim
           (add-prim ()  
                     (if (null? (cdr args))
                        (cases expval e1 (num-val(num) (num-val num))(ref-val(ref) (num-val (expval->num(deref ref))))(else "error")) 
                      (num-val (+ (cases expval e1 (num-val(num) num) (ref-val(ref) (expval->num(deref ref)))(else "error")) (expval->num(apply-primitive prim (cdr args)))))))
      (substract-prim ()  
                     (if (null? (cdr args))
                        (cases expval e1 (num-val(num) (num-val num))(ref-val(ref) (num-val (expval->num(deref ref))))(else "error")) 
                      (num-val (- (cases expval e1 (num-val(num) num) (ref-val(ref) (expval->num(deref ref)))(else "error")) (expval->num(apply-primitive prim (cdr args)))))))
           (mult-prim ()  
                     (if (null? (cdr args))
                        (cases expval e1 (num-val(num) (num-val num))(ref-val(ref) (num-val (expval->num(deref ref))))(else "error")) 
                      (num-val (* (cases expval e1 (num-val(num) num) (ref-val(ref) (expval->num(deref ref)))(else "error")) (expval->num(apply-primitive prim (cdr args)))))))
          (divide-prim ()  
                     (if (null? (cdr args))
                        (cases expval e1 (num-val(num) (num-val num))(ref-val(ref) (num-val (expval->num(deref ref))))(else "error")) 
                      (num-val (/ (cases expval e1 (num-val(num) num) (ref-val(ref) (expval->num(deref ref)))(else "error")) (expval->num(apply-primitive prim (cdr args)))))))
         ))))


(define grammar2
'(              
  (expression (number) num0)
  (expression (identifier) variable)
  (expression(primitive "(" (separated-list expression ",") ")") ArithmeticOp)
  (expression(primitivecomp "("  expression ","expression ")") ComparisonOp)
  (expression ("let" (arbno identifier "=" expression) "in" expression) letexpr)
   (expression ("letrec" (arbno identifier "=" expression) "in" expression) letrecexpr)
  (expression ("proc" "(" (arbno identifier ) ")" expression) proc-exp)
    (expression ("(" expression (arbno expression) ")") call-exp)
  (expression ("switch" expression "("(arbno "(" "case" expression "->" expression ")" ) ")") switchexpr)
  (expression ("if" expression "then" expression "else" expression) ifexpr)
   (expression("begin" expression (arbno ";" expression) "end")begin-exp)
  (expression ("newref" "(" expression ")") newref-exp)
   (expression ("set" identifier expression) assign-exp)
  (primitive("+")add-prim)
   (primitive("-")substract-prim)
    (primitive("*") mult-prim)
    (primitive("/") divide-prim)
    (primitivecomp("=")equal-prim)
    (primitivecomp(">")greater-prim)
    (primitivecomp  ("<")less-prim)
    (expression ("undefined") errorexpr)
    (expression ("true") trueexpr)
    (expression ("false") falseexpr)
  ))


 (define lex0
    '((whitespace (whitespace) skip)
      (comment ("%" (arbno (not #\newline))) skip)
      (identifier
       (letter (arbno (or letter digit "_" "-" "?")))
       symbol)
      (number (digit (arbno digit)) number)
      (number ("-" digit (arbno digit)) number)
      ))



(sllgen:make-define-datatypes lex0 grammar2)




 (define list-the-datatypes
    (lambda ()
(sllgen:list-define-datatypes lex0 grammar2)))




(define scan&parse1
(sllgen:make-string-parser lex0 grammar2))





#(i "letrec factorial = proc (x) if =(x , 0) then 1 else *(x , (factorial -(x , 1))) in (factorial 5)")

