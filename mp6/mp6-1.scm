#lang racket
(require eopl)
(require racket/include)
;(include "homies.rkt")
(require "message-type.scm")
;;With Steve Sekowski

(define file "")
(define change-file
  (lambda (filename)
    (set! file (read-string 1000000 (open-input-file filename)))
    ))

(define identifier? string?)
(define-datatype environment environment?
    (empty-env)
    (extend-env 
      (bvar symbol?)
      (bval (list-of symbol?))
      (saved-env environment?)))
  (define apply-env
    (lambda (env search-sym)
      (cases environment env
        (empty-env ()
          '())
        (extend-env (bvar bval saved-env)
	  (if (eqv? search-sym bvar)
	    bval
	    (apply-env saved-env search-sym))))))

(define (the-thread) 
  (thread
   (lambda ()
     (let ([other 0])
       (let loop ()
         (let ([value (thread-receive)])
           (cond 
             ([thread? value]
              (set! other value))
             (else 
              (cases message-type value
               (filename-msg(filename) (change-file filename))
               (query-msg(names depth id reply-to) 
                         (let ((list (generate (string->symbol (car names)) (string->symbol (cdr names)) depth)))
                           (let ((responsemessage (response-msg id (list->list-of-string list))))
                             (thread-send reply-to responsemessage))))
                           
               (response-msg (id result) 
                             value)
               ;  (response-msg (id result) 
                ;             (let ((result (cons id result)))
                 ;            (printf "~a~n"  result)))
              
              
              )))) (loop))))))


;(processmessage 'Alex 1 (buildenv (parse file) (empty-env)))


;;unification function

(define the-recipient (the-thread))
;(define b (the-thread))
;(define id 1)
;(define level 1)
;(define names (cons "Minas" "Sihan"))
;(thread-send the-recipient (query-msg names level id (current-thread)))
;(thread-send the-recipient b)
;(thread-send b the-recipient)
;(thread-receive)
;(thread-receive)

 (sleep 0.1)

(define parse
  (lambda (pgm)
    (scan&parse1 pgm)))


        

(define grammar2
'(      
  
  (Friendships ((arbno identifier ":" (arbno identifier) ";")) friend)
 
    
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
(define delete
  (lambda (item list)
    (cond
     ((equal? item (car list)) (cdr list))
     (else (cons (car list) (delete item (cdr list)))))))

(define generate
  (lambda (name1 name2 depth)
    (let ((env (buildenv (parse file) (empty-env))))
    (let ((list1 (firstguy name1 depth env)))
      (let ((list2 (secondguy name2 depth env)))
        (unification (delete name1 list1) (delete name2 list2)))))))
  
(define firstguy 
  (lambda (name depth env)
    (let ((queue '()))
    (set! queue (append queue (list name)))
    (processmessage depth env queue 1))))

(define secondguy 
  (lambda (name depth env)
    (let ((queue '()))
    (set! queue (append queue (list name)))
    (processmessage depth env queue 1))))
                   
(define unification
  (lambda (list1 list2)
    (if (null? list2)
    '()
    (if (memq (car list2) list1) 
        (cons (car list2) (unification list1 (cdr list2)))
        (unification list1 (cdr list2))))))
  
  
(define processmessage 
  (lambda(depth env queue tmplength)
    
   (cond ((equal? depth 0)
       queue) 
       (else       
        (let ((newlist (build-a-list queue env)))
          
          (let ((new-queue (remove-duplicates (append queue newlist))))
            (let ((new-length (length new-queue)))
          ;(printf "~a~n"  depth)
          ;(printf "~a~n"  queue)
             (if (eq? new-length tmplength)
                 new-queue
        (processmessage (- depth 1) env new-queue new-length)))))))))

(define list->list-of-string
  (lambda (list)
    (if (null? list)
        '()
        (cons (symbol->string (car list)) (list->list-of-string (cdr list))))))



(define build-a-list
  (lambda(tmpqueue env)
    (if (null? tmpqueue)
        '()
        (append (apply-env env (car tmpqueue)) (build-a-list (cdr tmpqueue) env)))))


(define build-a-list2
  (lambda(tmpqueue env)
    (if (null? tmpqueue)
        '()
        (append (apply-env env (car tmpqueue)) (build-a-list2 (cdr tmpqueue) env)))))

                             
                                     
;;setup environment up
(define buildenv (lambda (file env)
  (cases Friendships file
    (friend(name names)
           (if (null? name)
               env
               (let ((file (friend (cdr name) (cdr names))))
                 (let ((env (extend-env (car name) (car names) env)))
                   (buildenv file env))))))))
;(thread-send the-recipient (filename-msg "/Users/Frank/Desktop/homies.txt"))
(provide the-recipient)
;(define file "Minas : Steven Sihan Alex ;
;Steven : Minas Sihan Mario ;
;Sihan : Minas Steven Peter ;
;Peter : Sihan John ;
;Alex : Minas ;
;Mario : Peter ;")
;(define file rip)