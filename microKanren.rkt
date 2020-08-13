#lang racket

;; https://github.com/jasonhemann/microKanren-DLS-16/blob/master/mk.rkt

#| Nat -> Var |#
(define (var n) n)

#| Term -> Bool |#
(define (var? t) (number? t))

#| Term x Subst -> Term |#
(define (find u s)
  (let ([pr (and (var? u) (assv u s))])
    (if pr (find (cdr pr) s) u)))

#| Var x Term x Subst -> Bool |#
(define (occurs? x u s)
  (cond
    [(var? u) (eqv? x u)]
    [(pair? u) (or (occurs? x (find (car u) s) s)
                   (occurs? x (find (cdr u) s) s))]
    [else #f]))
  
#| Var x Term x Subst -> Maybe Subst |#
(define (ext-s x v s)
  (cond
    [(occurs? x v s) #f]
    [else (cons `(,x . ,v) s)]))

(define (unify u v s)
  (cond
    [(eqv? u v) s]
    [(var? u) (ext-s u v s)]
    [(var? v) (unify v u s)]
    [(and (pair? u) (pair? v))
     (let ([s (unify (find (car u) s) (find (car v) s) s)])
       (and s (unify (find (cdr u) s) (find (cdr v) s) s)))]
    [else #f]))


(define ((== u v) s/c)
  (let* ([s (car s/c)]
         [s (unify (find u s) (find v s) s)])
    (if s (list `(,s . ,(cdr s/c))) `())))

((== '#t 'z) '((). 0))
((== '(#t . #f) '(#t . #f)) '(() . 0))
((== '(#t . #f) '(#f . #t)) '(() . 0))

#| (Var -> Goal) -> Var |#
(define ((call/fresh f) s/c)
  (let ([c (cdr s/c)])
    ((f (var c)) `(,(car s/c) . ,(+ c 1)))))

((call/fresh
  (lambda (x)
    (== x 'a)))
 '(() . 0))


(define-syntax-rule (define-relation (defname . args) g)
  (define ((defname . args) (delay/name (g s/c)))))

(define ($append $1 $2)
  (cond
    [(null? $1) $2]
    [(promise? $1) (delay/name ($append $2 (force $1)))]
    [else (cons (car $1) (append (cdr $1) $2))]))

(define ($append-map g $)
  (cond
    [(null? $) '()]
    [(promise? $) (delay/name ($append-map g (force $)))]
    [else ($append (g (car $)) ($append-map g (cdr $)))]))


(define ((disj g1 g2) s/c)
  ($append (g1 s/c) (g1 s/c)))

(define ((conj g1 g2) s/c)
  ($append-map g2 (g1 s/c)))

((disj
  (call/fresh
   (lambda (x)
     (== 'z x)))
  (call/fresh
   (lambda (x)
     (== '(s z) x)))) '(() . 0))


((call/fresh
  (lambda (x)
    (call/fresh
     (lambda (y)
       (conj
        (== y x)
        (== 'z x)))))) '(() . 0))

((call/fresh
  (lambda (x)
    (call/fresh
     (lambda (y)
       (== x y))))) '(() . 0))


