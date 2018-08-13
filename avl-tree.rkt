#lang racket


(define-struct avl-tree
  (value left-tree right-tree)
  #:transparent)


(define (height-of-avl-tree a-tree)
  (match a-tree
    ['Empty 0]
    [(avl-tree _ left-tree right-tree)
     (+ 1 (max (height-of-avl-tree left-tree)
               (height-of-avl-tree right-tree)))]))


(define (search-avl-tree a-tree x)
  (match a-tree
    ['Empty #f]
    [(avl-tree y left-tree right-tree)
     (cond
       [(eq? x y) #t] ;; value is present 
       [(< x y) (search-avl-tree left-tree x)] ;; x < y go left
       [else (search-avl-tree right-tree x)])])) ;; else go right


;; Idea here is you perform insertion in same way as bst
;; and then perform rotation on tree

; https://upload.wikimedia.org/wikipedia/commons/c/c4/Tree_Rebalancing.gif
;; right-rotation
(define (left-left-case a-tree)
  (match a-tree
    [(avl-tree x (avl-tree y left-left-tree left-right-tree) right-tree)
     (avl-tree y left-left-tree (avl-tree x left-right-tree right-tree))]))

;; left-rotation
(define (right-right-case a-tree)
  (match a-tree
    [(avl-tree x left-tree (avl-tree y right-left-tree right-right-tree))
     (avl-tree y (avl-tree x left-tree right-left-tree) right-right-tree)]))

;; Two rotations
;; Left rotation -> right-rotation
(define (left-right-case a-tree)
  (match a-tree
    [(avl-tree x left-tree right-tree)
     (left-left-case (avl-tree x (right-right-case left-tree) right-tree))]))
    

;; Two rotations
;; right-rotation -> left-rotation
(define (right-left-case a-tree)
  (match a-tree
    [(avl-tree x left-tree right-tree)
     (right-right-case (avl-tree x left-tree (left-left-case right-tree)))]))

  


