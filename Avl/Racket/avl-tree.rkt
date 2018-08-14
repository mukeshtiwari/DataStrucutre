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


(define (search-avl-tree x a-tree)
  (match a-tree
    ['Empty #f]
    [(avl-tree y left-tree right-tree)
     (cond
       [(eq? x y) #t] ;; value is present 
       [(< x y) (search-avl-tree x left-tree)] ;; x < y go left
       [else (search-avl-tree x right-tree)])])) ;; else go right


;; Idea here is you perform insertion in same way as bst
;; and then perform rotation on tree

; https://upload.wikimedia.org/wikipedia/commons/c/c4/Tree_Rebalancing.gif
;; right-rotation
(define (left-left-case a-tree)
  (match a-tree
    [(avl-tree x (avl-tree y left-left-tree left-right-tree) right-tree)
     (avl-tree y left-left-tree (avl-tree x left-right-tree right-tree))]))

(left-left-case (avl-tree 4 (avl-tree 3 (avl-tree 2 'Empty 'Empty) 'Empty) 'Empty)) 

;; left-rotation
(define (right-right-case a-tree)
  (match a-tree
    [(avl-tree x left-tree (avl-tree y right-left-tree right-right-tree))
     (avl-tree y (avl-tree x left-tree right-left-tree) right-right-tree)]))

(right-right-case (avl-tree 1 'Empty (avl-tree 2 'Empty (avl-tree 3 'Empty 'Empty))))

;; Two rotations
;; Left rotation -> right-rotation
(define (left-right-case a-tree)
  (match a-tree
    [(avl-tree x left-tree right-tree)
     (left-left-case (avl-tree x (right-right-case left-tree) right-tree))]))
    
(left-right-case (avl-tree 4 (avl-tree 2 'Empty (avl-tree 3 'Empty 'Empty)) 'Empty))

;; Two rotations
;; right-rotation -> left-rotation
(define (right-left-case a-tree)
  (match a-tree
    [(avl-tree x left-tree right-tree)
     (right-right-case (avl-tree x left-tree (left-left-case right-tree)))]))

(right-left-case (avl-tree 5 'Empty (avl-tree 8 (avl-tree 6 'Empty 'Empty) 'Empty)))

(define (balance-factor a-tree)
  (match a-tree
    ['Empyt 0]
    [(avl-tree _ left-tree right-tree)
     (- (height-of-avl-tree right-tree) (height-of-avl-tree left-tree))]))

;; rotate the tree if balance factor is not +1, 0, -1
;; -2 => left heavy  => Two case +1 or -1.
;; 2 => Right heavy => Two case +1 or -1
(define (rotate-avl-tree a-tree)
  (match a-tree
    ['Empty 'Empty]
    [(avl-tree x left-tree right-tree)
     (let ([root-bal (balance-factor a-tree)])
       (cond
         [(= 2 root-bal)
          (if (= 1 (balance-factor right-tree))
              (right-right-case a-tree)
              (right-left-case a-tree))]
         [(= -2 root-bal)
          (if (= 1 (balance-factor left-tree))
              (left-right-case a-tree)
              (left-left-case a-tree))]
         [else a-tree]))]))
          

;; same as binary search tree insertion, but followed by rotation
(define (insert-v-into-tree v a-tree)
  (match a-tree
    ['Empty (avl-tree v 'Empty 'Empty)]
    [(avl-tree x left-tree right-tree)
     (rotate-avl-tree
      (cond
        [(eq? x v) (avl-tree x left-tree right-tree)]
        [(< v x) (avl-tree x (insert-v-into-tree v left-tree) right-tree)]
        [else (avl-tree x left-tree (insert-v-into-tree v right-tree))]))]))

     
(time (foldl (λ(x acc) (insert-v-into-tree x acc)) 'Empty (range 1 20)))

