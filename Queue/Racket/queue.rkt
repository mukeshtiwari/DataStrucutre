#lang racket

(provide create-queue pop-queue-partial pop-queue-total push-queue)

;; data structure for queue implemented by two list
(define-struct queue (u v))

;; create empty queue
(define create-queue (queue empty empty))

;; pop element from queue. It's partial function
(define (pop-queue-partial que)
  (match que
    [(queue v w)
     (cond
       [(and (empty? v) (empty? w) (error "queue is empty"))]
       [(empty? v) (let* ([rev-w (reverse w)]
                          [ret-val (car rev-w)])
                     (values ret-val (queue (cdr rev-w) empty)))]
       [else (values (car v) (queue (cdr v) w))])]))

;; pop element from empty queue. It's total function
(define (pop-queue-total def-value que)
  (match que
    [(queue v w)
     (cond
       [(and (empty? v) (empty? w)) def-value]
       [(empty? v) (let* ([rev-w (reverse w)]
                          [ret-val (car rev-w)])
                     (values ret-val (queue (cdr rev-w) empty)))]
       [else (values (car v) (queue (cdr v) w))])]))

;; push element val in queue 
(define (push-queue val que)
  (match que
    [(queue v w) (queue v (cons val w))]))