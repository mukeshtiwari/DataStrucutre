#lang racket

(provide pop-stack-partial pop-stack-total push-stack)

(define create-stack empty)

(define (pop-stack-partial stack)
  (if (empty? stack)
      (error "empty stack")
      (values (car stack) (cdr stack))))

(define (pop-stack-total def-value stack)
  (if (empty? stack)
      (values def-value empty)
      (values (car stack) (cdr stack))))
      

(define (push-stack v stack)
  (cons v stack))