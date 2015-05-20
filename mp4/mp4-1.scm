#lang eopl
(require "types-from-staff.scm")


 (define-datatype expval expval?
    (num-val
      (value number?))
    (bool-val
      (boolean boolean?))
    (proc-val 
      (proc proc?)))

;;; extractors:

  (define expval->num
    (lambda (v)
      (cases expval v
	(num-val (num) num)
	(else (expval-extractor-error 'num v)))))

  (define expval->bool
    (lambda (v)
      (cases expval v
	(bool-val (bool) bool)
	(else (expval-extractor-error 'bool v)))))

  (define expval->proc
    (lambda (v)
      (cases expval v
	(proc-val (proc) proc)
	(else (expval-extractor-error 'proc v)))))

  (define expval-extractor-error
    (lambda (variant value)
      (eopl:error 'expval-extractors "Looking for a ~s, found ~s"
	variant value)))

;;;;;;;;;;;;;;;; procedures ;;;;;;;;;;;;;;;;

  (define-datatype proc proc?
    (procedure
      (bvar symbol?)
      (body expression?)
      (env environment?)))
  
  (define-datatype environment environment?
    (empty-env)
    (extend-env 
      (bvar symbol?)
      (bval expval?)
      (saved-env environment?))
    (extend-env-rec
      (p-name symbol?)
      (b-var symbol?)
      (p-body expression?)
      (saved-env environment?)))

  (define init-env 
    (lambda ()
      (extend-env 
       'i (num-val 1)
       (extend-env
        'v (num-val 5)
        (extend-env
         'x (num-val 10)
         (empty-env))))))

;;;;;;;;;;;;;;;; environment constructors and observers ;;;;;;;;;;;;;;;;

  (define apply-env
    (lambda (env search-sym)
      (cases environment env
        (empty-env ()
          (eopl:error 'apply-env "No binding for ~s" search-sym))
        (extend-env (bvar bval saved-env)
	  (if (eqv? search-sym bvar)
	    bval
	    (apply-env saved-env search-sym)))
        (extend-env-rec (p-name b-var p-body saved-env)
          (if (eqv? search-sym p-name)
             (proc-val (procedure b-var p-body env))          
             (apply-env saved-env search-sym))))))
    
    (define equal-types?
    (lambda (ty1 ty2)
      (equal-up-to-gensyms? ty1 ty2)))

  ;; S-exp = Sym | Listof(S-exp)
  ;; A-list = Listof(Pair(TvarTypeSym, TvarTypesym))
  ;; a tvar-type-sym is a symbol ending with a digit.

  ;; equal-up-to-gensyms? : S-exp * S-exp -> Bool
  ;; Page: 271
  (define equal-up-to-gensyms?
    (lambda (sexp1 sexp2)
      (equal?
        (apply-subst-to-sexp (canonical-subst sexp1) sexp1)
        (apply-subst-to-sexp (canonical-subst sexp2) sexp2))))

  ;; canonicalize : S-exp -> A-list
  ;; usage: replaces all tvar-syms with tvar1, tvar2, etc.
  ;; Page: 271
  (define canonical-subst
    (lambda (sexp)
        ;; loop : sexp * alist -> alist
        (let loop ((sexp sexp) (table '()))
          (cond
            ((null? sexp) table)
            ((tvar-type-sym? sexp) 
             (cond
               ((assq sexp table) ; sexp is already bound, no more to
                                  ; do 
                table)
               (else 
                 (cons 
                   ;; the length of the table serves as a counter!
                   (cons sexp (ctr->ty (length table))) 
                   table))))
            ((pair? sexp)
             (loop (cdr sexp)
               (loop (car sexp) table)))
            (else table)))))

  ;; tvar-type-sym? : Sym -> Bool
  ;; Page: 272
  (define tvar-type-sym?
    (lambda (sym)
      (and (symbol? sym)
        (char-numeric? (car (reverse (symbol->list sym)))))))

  ;; symbol->list : Sym -> List
  ;; Page: 272
  (define symbol->list
    (lambda (x) (string->list (symbol->string x))))

  ;; apply-subst-to-sexp : A-list * S-exp -> S-exp
  ;; Page: 272
  (define apply-subst-to-sexp
    (lambda (subst sexp)
      (cond
        ((null? sexp) sexp)
        ((tvar-type-sym? sexp)
         (cdr (assq sexp subst)))
        ((pair? sexp)
         (cons
           (apply-subst-to-sexp subst (car sexp))
           (apply-subst-to-sexp subst (cdr sexp))))
        (else sexp))))

  ;; ctr->ty : N -> Sym
  ;; Page: 272
  (define ctr->ty
    (lambda (n)
      (string->symbol
        (string-append
          "tvar"
          (number->string n)))))
  (define-datatype answer answer?
    (an-answer                       
      (type type?)
      (subst substitution?)))

  ;; type-of-program : Program -> Type
  ;; Page: 267
  (define type-of-program
    (lambda (pgm)
      (cases program pgm
        (a-program (exp1)
          (cases answer (type-of-app exp1 (init-tenv) (empty-subst))
            (an-answer (ty subst)
              (apply-subst-to-type ty subst)))))))

  ;; type-of : Exp * Tenv * Subst -> Type
  ;; Page: 267--270

  (define type-of-app
    (lambda (exp tenv subst)
      (cases expression exp
        (trueexpr () (an-answer (bool-type) subst))
        (falseexpr () (an-answer (bool-type) subst))
        (const-exp (num) (an-answer (int-type) subst))
        
        (new-exp (exp1 exp2)
                 (let ((argtype (fresh-tvar-type)))
                   
                  (cases answer (type-of-app exp1 tenv subst)
            (an-answer (type1 subst1)
              (let ((subst1 (unifier type1 argtype subst1 exp1)))
                (cases answer (type-of-app exp2 tenv subst1)
                  (an-answer (type2 subst2)
                    (let ((subst2
                            (unifier type1 argtype subst1 exp2)))
                      (an-answer (pair-type type1 type2) subst2)))))))))
        (first-exp (exp)
                   (let ((firsttype (fresh-tvar-type)) (secondtype (fresh-tvar-type)))
            (cases answer (type-of-app exp tenv subst)
                     (an-answer (type1 subst1)
                                (if (eqv? subst1 "error")
                          (an-answer (bad-type) subst)
                        (let ((subst1 (unifier type1 (pair-type firsttype secondtype) subst1 exp)))
                          (if (eqv? subst1 "error")
                          (an-answer (bad-type) subst)
                                 (an-answer firsttype subst1)
                          )))))))
                                 
                                         
       (second-exp (exp)
                   (let ((firsttype (fresh-tvar-type)) (secondtype (fresh-tvar-type)))
            (cases answer (type-of-app exp tenv subst)
                     (an-answer (type1 subst1)
                                (if (eqv? subst1 "error")
                          (an-answer (bad-type) subst)
                        (let ((subst1 (unifier type1 (pair-type firsttype secondtype) subst1 exp)))
                          (if (eqv? subst1 "error")
                          (an-answer (bad-type) subst)
                                 (an-answer secondtype subst1)
                          )))))))

        (begin-exp (exp1 exps)
                   
                   (if (null? exps)
                       (type-of-app exp1 tenv subst)
                       (cases answer (type-of-app exp1 tenv subst)
                               (an-answer (type1 subst)
                                           (if (equal? type1 (bad-type))
                          (an-answer (bad-type) subst)
                                    (type-of-app (begin-exp (car exps) (cdr exps)) tenv subst))))))
         
                                
        
        (zero?-exp (exp1)
          (cases answer (type-of-app exp1 tenv subst)
            (an-answer (type1 subst1)
              (let ((subst2 (unifier type1 (int-type) subst1 exp)))
                (an-answer (bool-type) subst2)))))

        (diff-exp (primitive exps)
              (let ((subst1 (diffhelper exps tenv subst)))
                  (if (eqv? subst1 "error")
                          (an-answer (bad-type) subst)
                      (an-answer (int-type) subst1))))
        
        
        (comp-exp (op exp1 exp2)
          (cases answer (type-of-app exp1 tenv subst)
            (an-answer (type1 subst1)
              (let ((subst1 (unifier type1 (int-type) subst1 exp1)))
                (if (eqv? subst1 "error")
                          (an-answer (bad-type) subst)
                (cases answer (type-of-app exp2 tenv subst1)
                  (an-answer (type2 subst2)
                    (let ((subst2
                            (unifier type2 (int-type) subst2 exp2)))
                      (if (eqv? subst2 "error")
                          (an-answer (bad-type) subst)
                      (an-answer (bool-type) subst2))))))))))
        

        (if-exp (exp1 exp2 exp3)
          (cases answer (type-of-app exp1 tenv subst)
            (an-answer (ty1 subst1)
              (let ((subst1 (unifier ty1 (bool-type) subst1
                             exp1)))
                (if (eqv? subst1 "error")
                          (an-answer (bad-type) subst)
                (cases answer (type-of-app exp2 tenv subst1)
                  (an-answer (ty2 subst1)
                    (cases answer (type-of-app exp3 tenv subst1)
                      (an-answer (ty3 subst1)
                        (let ((subst1 (unifier ty2 ty3 subst1 exp)))
                          (if (eqv? subst1 "error")
                          (an-answer (bad-type) subst)
                          (an-answer ty2 subst1))))))))))))

        (var-exp (var) (an-answer (apply-tenv tenv var) subst))
;(let-exp (var exp1 body)
         ; (cases answer (type-of-app (car exp1) tenv subst)
          ;  (an-answer (rhs-type subst)
           ;   (type-of-app body
           ;;     (extend-tenv (car var)  rhs-type tenv)
              ; subst))))
       (let-exp (vars exps body)
                (if (null? vars)
                    (type-of-app body tenv subst)
                    (cases answer (type-of-app (car exps) tenv subst)
                      (an-answer (rhs-type subst)
                    (type-of-app (let-exp (cdr vars) (cdr exps) body)
                             (extend-tenv (car vars) rhs-type tenv) subst)))))
                               
        (proc-exp (var body)
          (let ((arg-type (map (lambda (x) (fresh-tvar-type)) var)))
            (cases answer (type-of-app body
                            (extend-tenv* var arg-type tenv)
                            subst)
              (an-answer (result-type subst)
                (an-answer
                  (proc-type arg-type result-type)
                  subst)))))

        (call-exp (rator rand)
          (let ((result-type (fresh-tvar-type)))
            (cases answer (type-of-app rator tenv subst)
              (an-answer (rator-type subst1)
                         (if (eqv? subst1 "error")
                          (an-answer (bad-type) subst)
                    (let ((subst2
                            (unifier rator-type
                              (proc-type (helpcall rand tenv subst1) result-type)
                              subst1
                              exp)))
                      (if (eqv? subst2 "error")
                          (an-answer (bad-type) subst)
                      (an-answer result-type subst2))))))))

        (letrec-exp (proc-name procexp letrec-body)
                    (if (null? proc-name)
                     (type-of-app letrec-body tenv subst)
                     (cases expression  (car procexp)
                       (proc-exp (bvars proc-body)
                         (let ((proc-result-type  (fresh-tvar-type) ) 
                           (proc-arg-type (map (lambda (x) (fresh-tvar-type)) bvars)))
                            (let ((tenv-for-letrec-body
                                 (extend-tenv*
                                   proc-name
                                 (map (lambda(x) (proc-type proc-arg-type proc-result-type)) procexp) tenv)))
                              
                              (cases answer (type-of-app proc-body
                              (extend-tenv*
                                bvars proc-arg-type tenv-for-letrec-body)
                              subst)
                (an-answer (proc-body-type subst)
                  (let ((subst 
                          (unifier proc-body-type proc-result-type subst
                            proc-body))) 
                    (type-of-app letrec-body
                      tenv-for-letrec-body
                      subst))))))
                       )(else "error")))))))
(trace type-of-app)
(define diffhelper 
    (lambda(exps tenv subst)
      (if (eqv? subst "error")
               "error"
            (if (null? exps)
                 subst
              (diffhelper (cdr exps) tenv 
                    (cases answer (type-of-app (car exps) tenv subst)
                   (an-answer (type1 subst1)
                             
                         (let ((subst1 (unifier type1 (int-type) subst1 (car exps))))subst1))))))))
(define helpcall(lambda(rand tenv subst)
                  (if (null? rand)
                      '()
                      (cons (cases answer (type-of-app (car rand) tenv subst)
                        (an-answer (rand-type subst) rand-type)) 
                            (helpcall (cdr rand) tenv subst)))))


    ;;;;;;;;;;;;;;;; type environments ;;;;;;;;;;;;;;;;
    
  ;; why are these separated?

  (define-datatype type-environment type-environment?
    (empty-tenv-record)
    (extended-tenv-record
      (sym symbol?)
      (type type?)
      (tenv type-environment?)))
    
  (define empty-tenv empty-tenv-record)
  (define extend-tenv extended-tenv-record)

(define extend-tenv*
  (lambda (vars vals env)
    (if (null? vars)
        env
        (extend-tenv (car vars)  (car vals)
                    (extend-tenv* (cdr vars) (cdr vals) env)))))


    
  (define apply-tenv 
    (lambda (tenv sym)
      (cases type-environment tenv
        (empty-tenv-record ()
          (eopl:error 'apply-tenv "Unbound variable ~s" sym))
        (extended-tenv-record (sym1 val1 old-env)
          (if (eqv? sym sym1) 
            val1
            (apply-tenv old-env sym))))))
  
  (define init-tenv
    (lambda ()
      (extend-tenv 'x (int-type) 
        (extend-tenv 'v (int-type)
          (extend-tenv 'i (int-type)
            (empty-tenv))))))

  ;; fresh-tvar-type : () -> Type
  ;; Page: 265  
  (define fresh-tvar-type
    (let ((sn 0))
      (lambda ()
        (set! sn (+ sn 1))
        (tvar-type 
         (string->symbol (string-append "t" (number->string sn)))))))

  ;; otype->type : OptionalType -> Type
  ;; Page: 265
  #(define otype->type
    (lambda (otype)
      (cases optional-type otype
        (no-type () (fresh-tvar-type))
        (a-type (ty) ty))))



  ;; value-of : Exp * Env -> ExpVal


  ;; apply-procedure : Proc * ExpVal -> ExpVal

  
    (define the-lexical-spec
    '((whitespace (whitespace) skip)
      (comment ("%" (arbno (not #\newline))) skip)
      (identifier
        (letter (arbno (or letter digit "_" "-" "?")))
        symbol)
      (number (digit (arbno digit)) number)
      (number ("-" digit (arbno digit)) number)
      ))
  
  (define the-grammar
    '((program (expression) a-program)

      (expression (number) const-exp)
      (expression
        (primitive "(" (separated-list expression ",") ")")
        diff-exp)
      
      (expression
        ("zero?" "(" expression ")")
        zero?-exp)

      (expression
        ("if" expression "then" expression "else" expression)
        if-exp)

      (expression (identifier) var-exp)

      (expression
        ("let" (arbno identifier "=" expression) "in" expression)
        let-exp)   

      (expression
        ("proc" "(" (arbno identifier) ")" expression)
        proc-exp)

      (expression
        ("(" expression (arbno expression) ")")
        call-exp)
      (expression
        (compsign "(" expression "," expression ")")
        comp-exp)
      (expression 
       ("newpair" "("expression "," expression")") new-exp)
      (expression 
       ("first" "("expression")") first-exp)
      (expression 
       ("second" "("expression ")") second-exp)
      
        (expression("begin" expression (arbno ";" expression) "end")begin-exp)

      (expression
        ("letrec"  (arbno identifier "=" expression)  "in" expression)
        letrec-exp)
      (expression ("true") trueexpr)
      (expression ("false") falseexpr)


     
      (primitive("+")add-prim)
   (primitive("-")substract-prim)
    (primitive("*") mult-prim)
    (primitive("/") divide-prim)
    (compsign ("=") equal-sign)
    (compsign ("<") smaller-sign)
    (compsign (">") larger-sign)

      ))

  ;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;
  
  (sllgen:make-define-datatypes the-lexical-spec the-grammar)
  
  (define show-the-datatypes
    (lambda () (sllgen:list-define-datatypes the-lexical-spec the-grammar)))
  
  (define scan&parse
    (sllgen:make-string-parser the-lexical-spec the-grammar))
  
  (define just-scan
    (sllgen:make-string-scanner the-lexical-spec the-grammar))
  
  

  ;;;;;;;;;;;;;;;; syntactic tests and observers ;;;;;;;;;;;;;;;;

  (define atomic-type?
    (lambda (ty)
      (cases type ty
        (proc-type (ty1 ty2) #f)
        (tvar-type (sn) #f)
        (else #t))))

  (define proc-type?
    (lambda (ty)
      (cases type ty
        (proc-type (t1 t2) #t)
        (else #f))))

  (define tvar-type?
    (lambda (ty)
      (cases type ty
        (tvar-type (serial-number) #t)
        (else #f))))

  (define pair-type?
    (lambda (ty)
      (cases type ty
        (pair-type (t1 t2) #t)
        (else #f))))


  (define proc-type->arg-typed
    (lambda (ty)
      (cases type ty
        (proc-type (arg-type result-type)  arg-type)
        (else (eopl:error 'proc-type->arg-type
                "Not a proc type: ~s" ty)))))

  (define proc-type->result-type
    (lambda (ty)
      (cases type ty
        (proc-type (arg-type result-type) result-type)
        (else (eopl:error 'proc-type->result-types
                "Not a proc type: ~s" ty)))))

  ;; type-to-external-form : Type -> List
  ;; Page: 266

  
    (define apply-one-subst
    (lambda (ty0 tvar ty1)
      (cases type ty0
        (bad-type () (bad-type))
        (int-type () (int-type))
        (bool-type () (bool-type))
        (pair-type (first second)
                   (pair-type 
                    (apply-one-subst first tvar ty1)
                    (apply-one-subst second tvar ty1)))
        ;;;;;;;;;asdfasf;;
        (proc-type (arg-type result-type)
          (proc-type
          
              (helpsub arg-type tvar ty1)
            (apply-one-subst result-type tvar ty1)))
        (tvar-type (sn)
          (if (equal? ty0 tvar) ty1 ty0)))))
(define helpsub (lambda(arg-type tvar ty1)
                (if (null? arg-type)
                    '()
                    (cons (apply-one-subst (car arg-type) tvar ty1) (helpsub (cdr arg-type) tvar ty1)))))
#(trace helpsub)
#(trace apply-one-subst)
;;;;;;;;;;;;;;;; Substitutions ;;;;;;;;;;;;;;;;

  ;; a substitution is a map from unknown types to types.
  ;; we'll represent this as an association list.

  (define pair-of
    (lambda (pred1 pred2)
      (lambda (val)
        (and (pair? val) (pred1 (car val)) (pred2 (cdr val))))))

  (define substitution? 
    (list-of (pair-of tvar-type? type?)))

  ;; basic observer: apply-subst-to-type
  ;; this is sometimes written ty1.subst 

  ;; apply-subst-to-type : Type * Subst -> Type
  ;; Page: 261
  (define apply-subst-to-type
    (lambda (ty subst)
      (cases type ty
        (bad-type () (bad-type))
        (int-type () (int-type))
        (bool-type () (bool-type))
        (pair-type (first second) 
                   (pair-type
            (apply-subst-to-type  first subst)
            (apply-subst-to-type second subst)))
        (proc-type (t1 t2)
          (proc-type
            (combine t1 subst)
            (apply-subst-to-type t2 subst)))
        (tvar-type (sn)
          (let ((tmp (assoc ty subst)))
            (if tmp
              (cdr tmp)
              ty))))))
(define combine(lambda (x subst)
                 (if (null? x)
                     '()
                     (cons (apply-subst-to-type (car x) subst) (combine (cdr x) subst)))))
#(trace apply-subst-to-type)
  ;; empty-subst : () -> Subst
  ;; produces a representation of the empty substitution.

  ;; extend-subst : Subst * Tvar * Type -> Subst

  ;; (extend-subst s tv t) produces a substitution with the property
  ;; that for all t0,
  
  ;;   (apply-subst t0 (extend-subst s tv t))
  ;;   = (apply-one-subst (apply-subst t0 s) tv t)

  ;; i.e.,  t0.(s[tv=t]) = (t0.s)[tv=t]

  ;; this means that for any type variable tv0 in the domain of s,

  ;;   (apply-subst tv0 (extend-subst s tv t))
  ;;   = (apply-one-subst (apply-subst tv0 s) tv t)

  ;; so we extend the substitution with a new element, and apply [t/v] to every
  ;; element already in the substitution. 


  ;; empty-subst : () -> Subst
  ;; Page 262
  (define empty-subst (lambda () '()))

  ;; extend-subst : Subst * Tvar * Type -> Subst
  ;; usage: tvar not already bound in subst.
  ;; Page: 262
  (define extend-subst
    (lambda (subst tvar ty)
      (cons
        (cons tvar ty)
        (map 
          (lambda (p)
            (let ((oldlhs (car p))
                  (oldrhs (cdr p)))
              (cons
                oldlhs
                (apply-one-subst oldrhs tvar ty))))
          subst))))
#(trace extend-subst)
    (define unifier
    (lambda (ty1 ty2 subst exp)
      (let ((ty1 (apply-subst-to-type ty1 subst))
            (ty2 (apply-subst-to-type ty2 subst)))
        (cond
          ((equal? ty1 ty2) subst)            
          ((tvar-type? ty1)
           (if (no-occurrence? ty1 ty2)
             (extend-subst subst ty1 ty2)
             (report-no-occurrence-violation ty1 ty2 exp)))
          ((tvar-type? ty2)
           (if (no-occurrence? ty2 ty1)
             (extend-subst subst ty2 ty1)
             (report-no-occurrence-violation ty2 ty1 exp)))
          
          ((and (proc-type? ty1) (proc-type? ty2))
           (let ((subst (helpunifier ty1 ty2
                          subst exp)))
             (if (eqv? subst "error")
                 "error"
              (let ((subst (unifier
                            (proc-type->result-type ty1)
                            (proc-type->result-type ty2)
                            subst exp)))
               subst))))
          ((and (pair-type? ty1) (pair-type? ty2))
           (let ((f1 (cases type ty1
                         (pair-type (first second) first)(else "error")))
                 (f2 (cases type ty1
                         (pair-type (first second) second)(else "error")))
                 (s1 (cases type ty2
                         (pair-type (first second) first)(else "error")))
                 (s2 (cases type ty2
                         (pair-type (first second) second)(else "error"))))
             (let((subst (unifier f1 s1 subst exp)))
               (let ((subst (unifier f2 s2 subst exp))) subst))))
             
           
          (else "error")))))
(define helpunifier (lambda (ty1 ty2 subst exp)
                    (let (( tys1 (cases type ty1
                      (proc-type (arg-types result-types) arg-types)(else "error")))
                          ( tys2 (cases type ty2
                      (proc-type (arg-types result-types) arg-types)(else "error"))))
                      (helper2 tys1 tys2 subst exp))))
(define helper2 (lambda (tys1 tys2 subst exp)
                  
                  (if (null? tys1)
                      subst
                      
                       (helper2 (cdr tys1) (cdr tys2) 
                                (unifier  (car tys1) (car tys2) subst exp) exp))))
#(trace helpunifier)
  
  (define proc-type->arg-type
    (lambda (ty)
      (cases type ty
        (proc-type (arg-type result-type)  arg-type)
        (else (eopl:error 'proc-type->arg-type
                "Not a proc type: ~s" ty)))))


  (define report-unification-failure
    (lambda (ty1 ty2 exp) 
      (eopl:error 'unification-failure)))

  (define report-no-occurrence-violation
    (lambda (ty1 ty2 exp)
      (eopl:error 'check-no-occurence!)))

  ;; no-occurrence? : Tvar * Type -> Bool
  ;; usage: Is there an occurrence of tvar in ty?
  ;; Page: 265
  (define no-occurrence?
    (lambda (tvar ty)
      (cases type ty
        (bad-type () (bad-type))
        (int-type () #t)
        (bool-type () #t)
        (pair-type (first second) #t)
        (proc-type (arg-type result-type)
          (and
            (no-occurrence? tvar (car arg-type))
            (no-occurrence? tvar result-type)))
        (tvar-type (serial-number) (not (equal? tvar ty))))))
#(trace no-occurrence?)

#(trace unifier)



 (define type-of
    (lambda (string)
     
        (type-of-program (scan&parse string))))
  
(provide type-of)