(define pi 3.14159)

(define piFunc
    (lambda x  pi))

(define simpleFun(lambda(x) (* 4 (+ 3 x))))

(define mediumFun (lambda(x) (write"CS")(write"421")(+ 3 x)))

(define hardFun
    (lambda (x)
      (if(null? x) (write"wrong")
         (if(negative? x) (write"a")
            (if(zero? x) (write"b")
               (write"c"))))))

(define F(lambda(x y)
             (if(null? x)
                '()
            (cons (+ y (car x) (- 3 (length x)) (F (cdr x) y)))))

(define simpleCurry (lambda (x)
    (lambda (y)
      (lambda (z)
        (* x (+ y z))))))

(define oneCurry (lambda (x y)
              (* 3 (+ x y))))

(define myAdd1 (lambda (l1)
    (if (null? l1)
        '()
        (cons  (add1(car l1)) (myAdd1(cdr l1))))))

(define myFlexAdd1 (lambda x
             (myAdd1
                    
              (if (null? (cdr x))
                  '(car x)
                  (cons (car x) (myAdd1 (cdr x)))))))
