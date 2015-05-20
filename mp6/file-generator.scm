; Written by Minas Charalambides
; for CS421 Spring 2015, MP6.
;
; Commercial use is explicitly prohibited.
; Using the code in this file for ANY purpose requires explicit citation.
; and inclusion of this note.

#lang racket

(define name-count 2500)
(define connectivity 20)

; Returns a new list which is a copy of lst
; but with the elements at positions i and j
; swapped.
(define (swap lst i j)
  (cond
    ((= i j) lst)
    ((> i j) (swap lst j i))
    (else
      (define list-i (list (list-ref lst i)))
      (define list-j (list (list-ref lst j)))
      (define-values (before-i i-and-beyond) (split-at lst i))
      (define-values (i-till-before-j j-and-beyond) (split-at i-and-beyond (- j i)))
      (append before-i list-j i-till-before-j list-i (cdr j-and-beyond)))))

; Returns a random number in the interval [i, j)
(define (random-in-interval i j)
  (+ i (random (- j i))))

; Returns a random permutation of the list lst
; up till the index n.
(define (random-permutation lst [n (length lst)])
  (let loop ([i 0]
             [lst lst])
    (if (= i n)
      lst
      (loop (add1 i) (swap lst i (random-in-interval i (length lst)))))))

; Generates a list containing the numbers from i to j inclusive.
(define (genlist i j)
  (let loop ([j j]
             [acc '()])
    (if (= i j)
      (cons i acc)
      (loop (sub1 j) (cons j acc)))))

; A list containing Name0 ... NameX where X = name-count.
(define people (map string-append (make-list name-count "Name")
                                  (map number->string (genlist 1 name-count))))

; Formats the elements of the list as a string that fits the assumed file format.
(define (format-for-printing lst)
  (let loop ([lst lst]
             [acc ""])
    (if (null? lst)
      acc
      (loop (cdr lst) (string-append acc (car lst) " ")))))

; Generate all lines in the file.
(for ([i name-count])
  (define current (list-ref people i))
  (define lst (random-permutation people connectivity))
  (printf  "~a : ~a ;~n" current (format-for-printing (remove current (take lst connectivity)))))

