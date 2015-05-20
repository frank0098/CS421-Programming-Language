#lang eopl
;;With Steve Sekowski
(define i (lambda(x)
  (object-interpreter x)))
;;environment 
(define-datatype environment environment?
  (empty-env)
  (extend-env
   (bvar symbol?)
   (bval reference?)                 
   (saved-env environment?))
   (extend-env-rec
    (pname (list-of symbol?))
    (proc-bodies (list-of expression?))
    (saved-env environment?)
  )(extend-env-with-self-and-super
      (self myclass?)
      (super-name symbol?)
      (saved-env environment?)))

(define apply-env
  (lambda (env search-var)
    (cases environment env
           (empty-env ()
                      (empty-env))
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
                            
                                  (apply-env saved-env search-var))))
      (extend-env-with-self-and-super(a b c) "error"))))

(define replace-env
  (lambda (procguy newenv)
    (define pro (expval->proc procguy))
    (cases proc pro
      (procedure (vars body) (proc-val (procedure vars body))))))

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

(define extend-letenv*
  (lambda (vars exps env)
    (if (null? vars)
        env
        (let ((var1 (car vars))
              (val1 (value (car exps) env)))
          (extend-letenv* (cdr vars) (cdr exps) (extend-env var1 (newref val1) env))))))

(define get-last-env
  (lambda (vars exprs env)
    (cond
      ((equal? vars '())
        env)
      (else
        (let ([value0 (value (car exprs) env )])
          (get-last-env (cdr vars) (cdr exprs) (extend-env (car vars) (newref value0) env)))))))


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
                  ("error"))
                 ((zero? ref1)
                  (cons val (cdr store1)))
                 (else
                   (cons
                     (car store1)
                     (setref-inner
                      (cdr store1) (- ref1 1)))))))) (setref-inner the-store ref)))))

(define identifier? symbol?)

(define-datatype proc proc?
  (procedure
   (var (list-of symbol?))
   (body expression?)))

(define-datatype expval expval? 
  (num-val
   (num number?))
  (symbol-val
   (symbol symbol?))
  (bool-val
   (bool boolean?))
  (proc-val
   (proc proc?))
  (ref-val
   (ref reference?))
  (undef-val
   (undef symbol?))
  (class-val
   (myclass myclass?)))

(define apply-procedure
  (lambda (proc1 args env)
    (cases proc proc1
           (procedure (vars body)
		      (let ((new-env (extend-env* vars args env)))
			(value body new-env))))))

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
        (else (undef-val 'undefined)))))

(define expval->proc
    (lambda (proc)
      (cases expval proc
        (proc-val (proc) proc)
        (else (undef-val 'undefined)))))

(define expval->bool
    (lambda (val)
      (cases expval val
        (bool-val (bool) bool)
        (else (undef-val 'undefined)))))

(define expval->ref
    (lambda (v)
      (cases expval v
	(ref-val (ref) ref)
	(else (undef-val 'undefined)))))

(define expval->class
    (lambda (class)
      (cases expval class
        (class-val (class) class)
        (else (undef-val 'undefined)))))

(define objid->id
    (lambda (object)
      (cases expval object
        (class-val (object) object)
        (else ('undefined)))))

(define object-interpreter
  (lambda (x)  
    (let ((value0 (value (g x) 
                         (empty-env))))
      (if (eqv? value0 'undefined)
          'undefined
          (cases expval value0
            (num-val(num) num)
            (bool-val(bool)  (if (eq? bool #t) 'true
                           'false))
            (else 'undefined))))))

(define static-interpreter
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

;;;;;;;;;CLASS;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define lookup-class                    
    (lambda (name)
      (let ((maybe-pair (assq name the-class-env)))
        (if maybe-pair (cadr maybe-pair)
          (report-unknown-class name)))))

(define report-unknown-class
  (lambda (name)
    (eopl:error 'lookup-class "Unknown class ~s" name)))

(define-datatype method method?
    (a-method
      (vars (list-of symbol?))
      (body expression?)
      (super-name symbol?)
      (field-names (list-of symbol?))))

  (define method-environment?
    (list-of 
      (lambda (p)
        (and 
          (pair? p)
          (symbol? (car p))
          (reference? (cadr p))))))

(define maybe
  (lambda (pred)
    (lambda (v)
      (or (not v) (pred v)))))

(define the-class-env '())
    (define add-to-class-env!
    (lambda (class-name class)
      (set! the-class-env
        (cons
          (list class-name class)
          the-class-env))))


(define fresh-identifier
  (let ((sn 0))
    (lambda (identifier)  
      (set! sn (+ sn 1))
      (string->symbol
       (string-append
        (symbol->string identifier)
        "%"             ; this can't appear in an input identifier
        (number->string sn))))))

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

(define-datatype myclass myclass?
    (my-class
     (super-name (maybe identifier?))
     (method-env environment?)))

(define getvars
  (lambda (members)
    (if (null? members)
        '()
        (cons 
         (cases memberdecl (car members)
           (pub (id exp)  (pub% id))
           (pri (id exp) (pri% id)))
         (getvars (cdr members))))))

(define getvals
  (lambda (members)
    (if (null? members)
        '()
        (cons 
         (cases memberdecl (car members)
           (pub (id exp) exp)
           (pri (id exp) exp))
         (getvals (cdr members))))))

;;;TODO: set-exp
(define value
  (lambda (exp env)
    (cases expression exp
      (errorexpr () 'undefined)
      (trueexpr () (bool-val #t))
      (falseexpr () (bool-val #f))
      (num0 (num) (num-val num)) 
       (object-exp (object member) 
                  (if (null? member)
                  (obj-value object env)
                  (let ((objectvalue 
                         (expval->class (obj-value object 
                             env))))
                    (cases myclass objectvalue
                      (my-class (super-name method-env)
                          (cases objectexp object
                            (obj-id (id) 
                               (let ((member2 (string-append "%pub" (symbol->string (car member)))))   
                                    (let ((result (apply-env method-env (string->symbol member2))))
                                      (if (equal? (empty-env) result)
                                          'undefined
                                  (let ((result (deref result)))
                                    (cases expval result
                                    (class-val (class) 
                                        ( cases myclass class
                                           (my-class (super-name method1-env)
                                             (let ((new-val (object-exp (obj-id (string->symbol (string-append "%pub" (symbol->string (car member))))) (cdr member))))
                                             (value new-val method-env)))))(else result)))))))
                            (else
                             (let ((member1 (string-append "%pub" (symbol->string (car member)))))   
                                    (let ((result  (apply-env method-env (string->symbol member1))))
                                      (if (equal? (empty-env) result)
                                       (let ((member1 (string-append "%pri" (symbol->string (car member)))))
                                         (let ((result (apply-env method-env (string->symbol member1))))
                                      (if (equal? (empty-env) result)
                                          'undefined
                                           (let ((result (deref result))) 
                                           (cases expval result
                                    (class-val (class) 
                                        ( cases myclass class
                                           (my-class (super-name method1-env)
                                             (let ((new-val (object-exp (obj-id (string->symbol (string-append "%pri" (symbol->string (car member))))) (cdr member))))
                                             (value new-val method-env)))))
                                             (else result))))))
                                   (let ((result (deref result)))       
                                  (cases expval result
                                    (class-val (class) 
                                        ( cases myclass class
                                           (my-class (super-name method1-env)
                                             (let ((new-val (object-exp (obj-id (string->symbol (string-append "%pri" (symbol->string (car member))))) (cdr member))))
                                             (value new-val method-env)))))
                                    (else result)))))))))))))
      (proc-exp (var body)
                    (proc-val (procedure var body)))
      (add-exp (term termList) (value-of-add term termList env))
      (subtract-exp (term termList) (value-of-sub term termList env))
      (multiply-exp (term termList) (value-of-mult term termList env))
      (divide-exp (term termList) (value-of-div term termList env))
      (greater-exp (term1 term2) (value-of-gr term1 term2 env))
      (less-exp (term1 term2) (value-of-lt term1 term2 env))
      (equal-exp (term1 term2) (value-of-eq term1 term2 env))
      
       (set-exp (exp exp1)
                  (cases environment env
                    (empty-env() 'undefined)
                    (else 
                     (cases expression exp
                       (object-exp (class member)
                            (cases objectexp class
                              (obj-id (id)
                         (if (null? member)
                      (begin
                            (setref!
                             (apply-env env id)
                             (value exp1 env))
                            (num-val 27))
                      (let ((newobj (deref (apply-env env id))))
                        (cases expval newobj
                          (class-val (class)
                            ( cases myclass class
                             (my-class (super method-env)
                                (begin
                                  (setref!
                                   (let ((toset (apply-env method-env (string->symbol (string-append "%pub" (symbol->string (car member)))))))
                                     (if (equal? toset (empty-env))
                                         (apply-env method-env (string->symbol (string-append "%pri" (symbol->string (car member)))))
                                         toset))
                                   (value exp1 env))
                                  (num-val 27)))))
                          (else 'undefined)))))
                              
                              
                              (self-exp ()
                               (let ((self (apply-env env '%self)))
                    (if (equal? self (empty-env))
                                'undefined
                                (let ((newobj (deref self)))
                                  (cases expval newobj
                                    (class-val (class)
                                        (cases myclass class
                                         (my-class (super method-env)
                                (begin
                                  (setref!
                                   (let ((toset (apply-env method-env (string->symbol (string-append "%pub" (symbol->string (car member)))))))
                                     (if (equal? toset (empty-env))
                                         (apply-env method-env (string->symbol (string-append "%pri" (symbol->string (car member)))))
                                         toset))
                                   (value exp1 env))
                                  (num-val 27)))))
                          (else 'undefined))))) )
                              
                               (super-exp ()
                               (let ((self (apply-env env '%self)))
                    (if (equal? self (empty-env))
                                'undefined
                                (let ((newobj (deref self)))
                                  (cases expval newobj
                                    (class-val (class)
                                        (cases myclass class
                                         (my-class (super method-env)
                                (begin
                                  (setref!
                                   (let ((toset (apply-env method-env (string->symbol (string-append "%pub" (symbol->string (car member)))))))
                                     (if (equal? toset (empty-env))
                                         (apply-env method-env (string->symbol (string-append "%pri" (symbol->string (car member)))))
                                         toset))
                                   (value exp1 env))
                                  (num-val 27)))))
                          (else 'undefined))))) )
                                      
                        
                              
                              
                              (else 'wtf)))
                       (else 'undefined)))))
      )))



(define value-of-set
  (lambda (exp1 exp2 env)
    (cond 
      [(eqv? (apply-env env (value exp1 env)) 'undefined) (undef-val 'undefined)]
      [#t (setref!
           (expval->ref (apply-env env (value exp1 env)))
           (value exp2 env))])))

(define value-of-add
  (lambda (term term-list env)
    (cond
        [(not (check-all-num (cons term term-list) env)) (undef-val 'undefined)]
        [(null? term-list) (value term env)]
        [#t (add-recurse (cons term term-list) env)])))

(define add-recurse 
  (lambda (terms env)
    (if (null? (cdr terms))
        (value (car terms) env)
        (num-val (+ (expval->num (value (car terms) env)) (expval->num(add-recurse (cdr terms) env)))))))

(define value-of-sub
  (lambda (term term-list env)
    (cond
        [(not (check-all-num (cons term term-list) env)) (undef-val 'undefined)]
        [(null? term-list) (num-val (- 0 (expval->num (value term env))))]
        [#t (subtract-recurse (reverse (cons term term-list)) env)])))

(define subtract-recurse 
  (lambda (terms env)
    (if (null? (cdr terms))
        (value (car terms) env)
        (num-val (- (expval->num(subtract-recurse (cdr terms) env)) (expval->num (value (car terms) env)))))))

(define value-of-mult
  (lambda (term term-list env)
    (cond 
        [(not (check-all-num (cons term term-list) env)) (undef-val 'undefined)]
        [(null? term-list) (value term env)]
        [#t (multiply-recurse (cons term term-list) env)])))

(define multiply-recurse 
  (lambda (terms env)
    (if (null? (cdr terms))
        (value (car terms) env)
        (num-val (* (expval->num (value (car terms) env)) (expval->num(multiply-recurse (cdr terms) env)))))))

(define value-of-div
  (lambda (term term-list env)
    (cond
        [(not (check-all-num (cons term term-list) env)) (undef-val 'undefined)]
        [(null? term-list) (num-val (/ 1 (expval->num (value term env))))]
        [#t (num-val (/ (expval->num (value term env)) (expval->num (multiply-recurse term-list env))))])))

(define check-all-num
  (lambda (stuff env)
    (if (null? stuff)
        #t
        (and (number? (expval->num (value (car stuff) env))) (check-all-num (cdr stuff) env)))))

(define value-of-gr
  (lambda (exp1 exp2 env)
    (if (check-all-num (list exp1 exp2) env)
        (bool-val (> (expval->num (value exp1 env)) (expval->num (value exp2 env))))
        (undef-val 'undefined))))

(define value-of-lt
  (lambda (exp1 exp2 env)
    (if (check-all-num (list exp1 exp2) env)
        (bool-val (< (expval->num (value exp1 env)) (expval->num (value exp2 env))))
        (undef-val 'undefined))))

(define value-of-eq
  (lambda (exp1 exp2 env)
    (if (check-all-num (list exp1 exp2) env)
        (bool-val (= (expval->num (value exp1 env)) (expval->num (value exp2 env))))
        (undef-val 'undefined))))

;;;TODO: Letrec
(define obj-value
  (lambda (exp env)
    (cases objectexp exp
       (let-exp (vars exps body)
		    (value body (extend-letenv* vars exps env)))
      
      	(empty-obj () (class-val (my-class #f (empty-env))))
      
        (objextend(exp memdc) 
                (let ((result (expval->class (value exp env))))
                  (let ((vars (getvars memdc))
                        (vals (getvals memdc)))
                      (cases environment env
                        (empty-env ()
                          (let ((env (extend-env 'EmptyObj (newref result) env)))
                      (let ((new-super (cases environment env
                                       (extend-env (bvar bval saved-env)
                                                   bvar)
                                       (else "error"))))
                  (cases myclass result
                     (my-class (super-name method-env)   
                          (class-val (my-class new-super (extend-letenv* vars vals method-env))))))))
                        (else 
                      (let ((new-super (cases environment env
                                       (extend-env (bvar bval saved-env)
                                                   bvar)
                                       (else "error"))))
                  (cases myclass result
                     (my-class (super-name method-env)   
                          (class-val (my-class new-super (extend-letenv* vars vals method-env)))))))))))
       (call-exp (rator rands)
                     (let ((proc (expval->proc (value rator  
                       env)))
                           (args (map (lambda(x) (value x env))
                                      rands)))
                 (cases expression rator
                   (object-exp (object member)
                       (cases objectexp object
                         (obj-id (id)
                       (let ((newval (obj-value object env)))
                       (cases expval newval
                         (class-val (class) (apply-procedure proc args  (extend-env '%self (newref (obj-value object env)) env)))
                         (else (if (null? rands)
                                   (apply-procedure proc args env)
                                   (cases expression (car rands)
                         (object-exp (object1 member1)
                        (let ((newval2 (obj-value object1 env)))
                       (cases expval newval2
                         (class-val (class) (apply-procedure proc args  (extend-env '%self (newref newval2) env)))
                         (else (apply-procedure proc args env))))) (else (apply-procedure proc args env)))
                                   )))))
                         (self-exp ()
                       (let ((newval (obj-value object env)))
                       (cases expval newval
                         (class-val (class) (apply-procedure proc args  (extend-env '%self (newref (obj-value object env)) env)))
                         (else (if (null? rands)
                                   (apply-procedure proc args env)
                                   (cases expression (car rands)
                         (object-exp (object1 member1)
                        (let ((newval2 (obj-value object1 env)))
                       (cases expval newval2
                         (class-val (class) (apply-procedure proc args  (extend-env '%self (newref newval2) env)))
                         (else (apply-procedure proc args env))))) (else (apply-procedure proc args env))))))))
                         (else (apply-procedure proc args env))))
                   (else (apply-procedure proc args env)))))
      
      (obj-id (id)  (deref (apply-env env id)))
      
     (self-exp () (let ((self (apply-env env '%self)))
                    (if (equal? self (empty-env))
                                'undefined
                                (deref self))))
                    
       (super-exp () (let ((self (apply-env env '%self)))
                       (if (equal? self (empty-env))
                               'undefined
                       (let ((self (expval->class (deref self))))
                               (cases myclass self
                                 (my-class (super-name method-env)
                                           (deref (apply-env env super-name))))))))
      (ifexpr (check then else) (value-of-if check then else env))
      (begin-exp (exp-list) (value-of-begin exp-list env))
     (letrecexpr (pname exps body)
		    (value body
			      (extend-env-rec pname exps env)))
      
      (else 'undefined))))

(define value-of-begin 
  (lambda (exp-list env)
    (cond
      [(null? (cdr exp-list)) (value (car exp-list) env)]
      [#t 
       (value (car exp-list) env)
       (value-of-begin (cdr exp-list) env)])))

(define value-of-if
  (lambda (exp0 exp1 exp2 env) 
    (define check (expval->bool (value exp0 env)))
    (cond 
      [(not (boolean? check)) (undef-val 'undefined)]
      [check (value exp1 env)]
      [#t (value exp2 env)])))

(define value-of-letrec
  (lambda (id-list proc-list body env)
    (value body
              (extend-env-rec id-list (letrec-proc-helper proc-list env) env))))

(define letrec-proc-helper
  (lambda (procs env)
    (if (null? procs)
        '()
        (cons (value (car procs) env) (letrec-proc-helper (cdr procs) env)))))

#(trace obj-value)


(define grammar2
'(  
  
  (expression (number) num0)
     (class-decl                         
        ("class" identifier 
          "extends" identifier                   
          (arbno "field" identifier)
          (arbno method-decl)
          )
        a-class-decl)

      (method-decl
        ("method" identifier 
          "("  (separated-list identifier ",") ")" ; method formals
          expression 
          )
        a-method-decl)
      
      (objectexp ("begin" (arbno expression ";") "end")begin-exp)
      (objectexp ("if" expression "then" expression "else" expression "end") ifexpr)
      (objectexp ("let" (arbno identifier "=" expression) "in" expression "end") let-exp)
      (objectexp ("letrec" (arbno identifier "=" expression) "in" expression "end") letrecexpr)
      (objectexp ("EmptyObj") empty-obj)
      (objectexp (identifier) obj-id)
      (objectexp ("extend" expression "with" (arbno memberdecl) ) objextend)     
      (objectexp ("(" expression (arbno expression) ")") call-exp)
      (objectexp ("self") self-exp)
      (objectexp ("super") super-exp)
      
      (expression ("+" "(" expression (arbno "," expression) ")") add-exp)
      (expression ("-" "(" expression (arbno "," expression) ")") subtract-exp)
      (expression ("*" "(" expression (arbno "," expression) ")") multiply-exp)
      (expression ("/" "(" expression (arbno "," expression) ")") divide-exp)
      (expression (">" "(" expression "," expression ")") greater-exp)
      (expression ("<" "(" expression "," expression ")") less-exp)
      (expression ("=" "(" expression "," expression ")") equal-exp)
      (expression ("proc" "(" (arbno identifier ) ")" expression "end") proc-exp)
      (expression (objectexp (arbno "." identifier)) object-exp)
      (expression ("(set" expression expression ")") set-exp)
      (expression ("undefined") errorexpr)
      (expression ("true") trueexpr)
      (expression ("false") falseexpr)
       
      (memberdecl ("public" identifier "=" expression ";") pub)
      (memberdecl ("protected" identifier "=" expression ";") pri)
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

(define extract
  (lambda (sym)
    (string->symbol (string-tail sym 4))))
(define pub%
  (lambda (sym)
    (string->symbol(string-append "%pub"(symbol->string sym)))))
(define pri%
  (lambda (sym)
    (string->symbol(string-append "%pri"(symbol->string sym)))))

(define (string-tail string start)
  (substring string start (string-length string)))
#(trace extract)
#(object-interpreter "let ob = extend EmptyObj with	
	public foo = proc(y) let  x = 1	in +(x,y) end end;
	 in (ob.foo 2)
	end ")

#(object-interpreter
"let ob = extend EmptyObj with protected x=1;
in ob.x end")


#(display "expected: true; actual:")
#(object-interpreter
"let node = extend EmptyObj with
protected next = 0 ;
protected element = 0 ;
public setElement = proc (x) (set self.element x) end;
public setNext = proc (x) (set self.next x) end;
public getElement = proc () self.element end;
public apply = proc (f)
begin
(set self.element (f self.element)) ;
if =(self.next, 0) then 0 else (self.next.apply f) end ;
end
end;
in let head = extend node with
a = extend node with
b = extend node with
in
begin
(head.setNext a) ;
(a.setNext b) ;
(head.apply proc (x) +(x, 1) end) ;
(b.getElement) ;
end
end
end")
#(newline)
#(object-interpreter "let obj = 
          extend 
              extend 
                  extend EmptyObj with public getVal = proc() 3 end; 
              with public getVal = proc() 5 end; public getSuper = proc() (super.getVal) end; 
          with public getSuper = proc() (super.getSuper) end; 
      in (obj.getSuper) end" )
#(object-interpreter
"let node = extend EmptyObj with
public next = 0 ;
public element = 0 ;
public setNext = proc (x) (set self.next x) end;
in let head = extend node with
a = extend node with
b = extend node with
in
begin
(head.setNext 3) ;
head.next;
end
end
end")

