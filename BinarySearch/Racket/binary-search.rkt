#lang racket

(define (binary-search-left-most f vs low high)
  (let* ([mid (quotient (+ low high) 2)])
    (if (< low high)
        (if (f (vector-ref vs mid))
            (binary-search-left-most f vs (+ mid 1) high)
            (binary-search-left-most f vs low mid))
	low)))
  
(define (binary-search-left-partial t vs)
  (let* ([len (vector-length vs)]
         [low 0]
         [high len]
         [ind (binary-search-left-most (lambda (x) (< x t)) vs low high)])
    (if (and (< ind high)
             (eq? (vector-ref vs ind) t))
        ind
        'None)))

(define (binary-search-left-total def-ind t vs)
  (let ([ind (binary-search-left-partial t vs)])
    (match ind
      ['None def-ind]
      [else ind])))


(define (binary-search-right-most f vs low high)
  (let* ([mid (quotient (+ low high) 2)])
    (if (< low high)
        (if (f (vector-ref vs mid))
            (binary-search-right-most f vs low mid)
            (binary-search-right-most f vs (+ mid 1) high))
        (- low 1))))

(define (binary-search-right-partial t vs)
  (let* ([len (vector-length vs)]
         [low 0]
         [high len]
         [ind (binary-search-right-most (lambda (x) (> x t)) vs low high)])
    (if (and (> (+ ind 1) 0)
             (eq? (vector-ref vs ind) t))
        ind
        'None)))
    
(define (binary-search-right-total def-ind t vs)
  (let ([ind (binary-search-right-partial t vs)])
    (match ind
      ['None def-ind]
      [else ind])))


(define vs '#(1 1 4 4 4 6 6 7 9 10))
(binary-search-left-partial 40  vs)
(binary-search-left-total -1 40 vs)
(binary-search-left-partial 1 vs)
(binary-search-left-total -1 9 vs)
(binary-search-right-partial 40  vs)
(binary-search-right-total -1 40 vs)
(binary-search-right-partial 1 vs)
(binary-search-right-total -1 9 vs)
;; some property to prove that if element is present only one time then
;; left search and right search would give same index.
;; Trying proving it in Coq.
