#lang racket

(define-struct avl-tree
  (left-tree value bal right-tree)
  #:transparent)



(define (depth-avl-tree a-tree)
  (match a-tree
    [(avl-tree _ _ bal _) bal]))

(define (balance-factor left-tree right-tree)
  (- (depth-avl-tree right-tree) (depth-avl-tree left-tree)))

(define (search-avl-tree a-tree x)
  (match a-tree
    [(avl-tree 'Empty y _ 'Empty) (eq? x y)] ;; I am at root node
    [(avl-tree left-tree y _ right-tree)
     (cond
       [(eq? x y) #t] ;; value is present 
       [(< x y) (search-avl-tree left-tree x)] ;; x < y go left
       [else (search-avl-tree right-tree x)])])) ;; else go right


;; Idea here is you perform insertion in same way as bst
;; and then perform rotation on tree

(define (rotate-avl-tree a-tree)
  a-tree)

(define (avl-tree-insertion a-tree x)
  (match a-tree
    ['Empty (avl-tree 'Empty x 0 'Empty)]
    [(avl-tree left-tree y b right-tree)
     (cond
       [(eq? x y) a-tree]
       [(< x y) (rotate-avl-tree (avl-tree (avl-tree-insertion left-tree x) y b right-tree))]
       [else (rotate-avl-tree (avl-tree left-tree y b (avl-tree-insertion right-tree x)))])]))
      