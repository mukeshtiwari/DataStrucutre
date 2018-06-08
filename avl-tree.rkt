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
(define (left-left-rotation a-tree)
  (match a-tree
   [(avl-tree x (avl-tree y left-left-tree left-right-tree) right-tree)
    (avl-tree y left-left-tree (avl-tree x left-right-tree right-tree))]))

(define (right-right-rotation a-tree)
  (match a-tree
    [(avl-tree x left-tree (avl-tree y right-left-tree right-right-tree))
     (avl-tree y (avl-tree left-tree right-left-tree) right-right-tree)]))
                              
(define (left-right-rotation a-tree)
  (match a-tree
    [(avl-tree x (avl-tree y ll-tree
                          (avl-tree z lll-tree llr-tree)) right-tree)
     (avl-tree z
               (avl-tree y ll-tree lll-tree)
               (avl-tree x llr-tree right-tree))]))
                             
(define (right-left-rotation a-tree)
  (match a-tree
    [(avl-tree x left-tree (avl-tree y (avl-tree z rrl-tree rrr-tree) rr-tree))
     (avl-tree z
               (avl-tree x left-tree rrl-tree)
               (avl-tree y rrr-tree rr-tree))]))


