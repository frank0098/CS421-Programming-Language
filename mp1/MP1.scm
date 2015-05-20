#lang eopl
#(1)
(define insert (lambda (lst n)
    (if (null? lst)
        (cons n '())
        (cons (car lst) (insert (cdr lst) n)))))

#(2)
(define insertAtN(lambda (lst n val)
             (if(null? lst)
                (cons val '())
             (h (insert (g lst n) val)  (f lst n)))))
(define f (lambda (lst x)     
              (if(null? lst)
                 lst
               (if (> x 0)
              (f (cdr lst) (- x 1))
              lst))))              
(define g (lambda (lst x)
              (if (< x 0)
                  '()
                  (if (null? lst)
                      '()
                  (if (zero? x)
                      '()
                      (cons (car lst) (g (cdr lst) (- x 1))))))))


(define h (lambda (lst1 lst2) 
              (if(null? lst1)
                 lst2
              (cons (car lst1) (h (cdr lst1) lst2))))) 
#(3)
(define pairSums (lambda (lst)
              (if (null? lst)
                  '()
                  (cons (help3 (car lst)) (pairSums (cdr lst))))))	
                  
(define help3 (lambda (lst)	
		(if(null? lst)
			0
			(+  (car lst) (help3 (cdr lst))))))
#(4)
(define pairSums2 (lambda (lst)
              (if (null? lst)
                  '()
                  (cons (apply + (car lst))
                         
                          (pairSums2 (cdr lst)
                           
                           )))))

#(5)
(define funcMap (lambda (lst1 lst2)
    (if (null? lst1)
        '()
        (cons (map (car lst1) lst2) (funcMap (cdr lst1) lst2)))))


#(6)
(define empty (lambda()
                '()))
(define bitree (lambda (value left right)
               (list value left right)))
(define makeSTree (lambda(x)
                    (if (integer? x)
                    (bitree x (empty) (empty))
                    "error")))

#(7)

(define insertLeaf (lambda (x lst)
                     (if (integer? x)
              (cond
                ((null? lst)
                (makeSTree x))
                ((< x (car lst))
                (bitree (car lst) (insertLeaf x (cadr lst)) (caddr lst)))
                ((> x (car lst))
                (bitree (car lst) (cadr lst) (insertLeaf x (caddr lst))))
                (else lst)
                )
              "error")))
                
    #(insertLeaf 3 (insertLeaf 8 (insertLeaf 2 (makeSTree 5))))        
           

#(8)
(define existBST
  (lambda (x lst)
    (if (null? lst)
        #f
               
    (if (< x (car lst))
        (existBST x (cadr lst))
        
         (if (= x (car lst))
             #t
          (existBST x (caddr lst)))))))


#(9)
(define-datatype Stack Stack?
  (empty-stack
   )
  (nonempty
   (first number?)
   (rest Stack?)))

(define emptystack (lambda x
                     (empty-stack)))

(define push (lambda (x stack)
               (nonempty x stack)))

(define pop
         (lambda (s)
             (cases Stack s
                 (empty-stack () '())
                 (nonempty (val s1) s1))))
(define top
         (lambda (s)
             (cases Stack s
                 (empty-stack () '())
                 (nonempty (val s1) val))))


(define grammar2
'(
  (Concat-expr (Arith-expr (arbno "concat-int" Arith-expr)) conc)
  
  (Arith-expr (Arith-term (arbno Additive-op Arith-term )) expr)
  
  (Arith-term (Arith-factor (arbno Multiplicative-op Arith-factor)) term)
                           
  (Arith-factor (number) num)
  
  (Arith-factor ("("Concat-expr")") cexpr)
  
  (Additive-op ("+") add-up)
  (Additive-op ("-") min-down)
  (Multiplicative-op ("*") multiply)
  (Multiplicative-op ("/") divide)
  
  
 
)
  )
