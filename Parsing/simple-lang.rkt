#lang racket
;http://matt.might.net/articles/lexers-in-racket/
;https://gist.github.com/danking/1068185

(require parser-tools/lex
         (prefix-in : parser-tools/lex-sre)
         parser-tools/yacc)

(define-empty-tokens emp
  (PLUS MINUS MULT DIV EOF LET IN EQ))
(define-tokens a (NUM VAR))

(define-lex-trans number
  (syntax-rules ()
    [(_ digit)
     (:: (:? (:-or "-" "+")) (uinteger digit)
         (:? (:: "." (:? (uinteger digit)))))]))

(define-lex-trans uinteger
  (syntax-rules ()
    [(_ digit) (:+ digit)]))

(define math-lexer
  (lexer
   ["-" (token-MINUS)]
   ["+" (token-PLUS)]
   ["*" (token-MULT)]
   ["/" (token-DIV)]
   ["let" (token-LET)]
   ["in" (token-IN)]
   ["=" (token-EQ)]
   [(:+ (char-range "0" "9")) (token-NUM (string->number lexeme))]
   ((:+ (char-range "A" "z")) (token-VAR lexeme))
   [whitespace (math-lexer input-port)]
   [(eof) (token-EOF)]))

(define-struct let-exp (var num exp) #:transparent)
(define-struct arith-exp (op exp-one exp-two) #:transparent)
(define-struct num-exp (n) #:transparent)
(define-struct var-exp (i) #:transparent)

(define math-parser
  (parser
   [start exp]
   [end EOF]
   [error void]
   [tokens emp a]
   [precs
    (left PLUS MINUS)
    (left MULT DIV)]
   [grammar
    [exp ((NUM) (num-exp $1))
         ((VAR) (var-exp $1))
         ((exp PLUS exp) (arith-exp 'Plus $1 $3))
         ((exp MINUS exp) (arith-exp 'Minus $1 $3))
         ((exp MULT exp) (arith-exp 'Mult $1 $3))
         ((exp DIV exp) (arith-exp 'Div $1 $3))
         ((LET VAR EQ NUM IN exp)
          (let-exp $2 (num-exp $4) $6))]]))
   




(define in (open-input-string "let x = 3 in let y = x * x in y + y"))
(math-lexer in)
(math-lexer in)
(math-lexer in)
(math-lexer in)
(math-lexer in)
(math-lexer in)
(math-lexer in)
(math-lexer in)
(math-lexer in)
(math-lexer in)
(math-lexer in)
(math-lexer in)
(math-lexer in)
(math-lexer in)
(math-lexer in)
(math-lexer in)

(define (lex-this lexer input) (lambda () (lexer input)))

(let ((input (open-input-string "3 - 3 + 6")))
  (math-parser (lex-this math-lexer input)))


(let ((input (open-input-string "let foo = 6 in 3 - 3 + foo")))
(math-parser (lex-this math-lexer input)))