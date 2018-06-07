#lang racket

(define-struct avl-tree
  (left-tree value height right-tree)
  #:transparent)



(define (height-avl-tree a-tree)
  (match a-tree
    ['Empty 0]
    [(avl-tree _ _ height _) height]))

(define (balance-factor left-tree right-tree)
  (- (height-avl-tree right-tree) (height-avl-tree left-tree)))

(define (search-avl-tree a-tree x)
  (match a-tree
    ['Empty #f]
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
    [(avl-tree left-tree y height right-tree)
     (cond
       [(eq? x y) a-tree]
       [(< x y)
        (match-let ([(avl-tree ll-tree lx lh lr-tree)
                     (avl-tree-insertion left-tree x)])
          (rotate-avl-tree
           (avl-tree (avl-tree ll-tree lx lh lr-tree)
                     y
                     (+ 1 (max lh (height-avl-tree right-tree)))
                     right-tree)))]
       [(> x y)
        (match-let ([(avl-tree rl-tree rx rh rr-tree)
                     (avl-tree-insertion right-tree x)])
          (rotate-avl-tree
           (avl-tree left-tree
                     y
                     (+ 1 (max (height-avl-tree left-tree) rh))
                     (avl-tree rl-tree rx rh rr-tree))))])]))


(define (tree-from-list lst)
  (foldl (λ(x acc) (avl-tree-insertion acc x)) 'Empty lst))

