#lang racket

(provide create-stack pop-stack-partial pop-stack-total push-stack)

(define-struct cons-stack (v))

(define create-stack (cons-stack empty))

(define (pop-stack-partial stack)
  (match stack
    [(cons-stack v)
     (if (empty? v)
         (error "empty stack")
         (values (car v) (cons-stack (cdr v))))]))

(define (pop-stack-total def-value stack)
  (match stack
    [(cons-stack v)
     (if (empty? v)
         (values def-value (cons-stack empty))
         (values (car v) (cons-stack (cdr stack))))]))
      

(define (push-stack v stack)
  (match stack
    [(cons-stack s) (cons-stack (cons v s))]))