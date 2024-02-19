#lang racket
(require racket/set racket/stream)
(require racket/fixnum) (require "interp-Lint.rkt") (require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Cvar.rkt")
(require "utilities.rkt")
(require "interp.rkt")
(provide (all-defined-out))

(define (uniquify-exp env)    ;; TODO: this function currently does nothing. Your code goes here
  (lambda (e)
    (match e
      [(Var x) (Var (dict-ref env x))]
      [(Int n) (Int n)]
      [(Let x e body) 
	   (let ([sub-env (dict-set env x (gensym x))])
		 (Let (dict-ref sub-env x) ((uniquify-exp env) e) ((uniquify-exp sub-env) body)))]
      [(Prim op es)
       (Prim op (for/list ([e es]) ((uniquify-exp env) e)))])))

; uniquify : Lvar -> Lvar
 (define (uniquify p)
   (match p
     [(Program info e) (Program info ((uniquify-exp '()) e))]))

(define (remove-complex-opera-exp env)    ;; TODO: this function currently does nothing. Your code goes here
  (lambda (e)
    (match e
      [(Var x) (Var x)]
      [(Int n) (Int n)]
      [(Let x e body) (Let x ((remove-complex-opera-exp env) e) ((remove-complex-opera-exp env) body))]
      [(Prim op es)
	   (cond
		 [(eq? (length es) 1) (if (atm? (first es))
								(Prim op es)
								(let ([x (gensym 'tmp)]) 
										   (Let x ((remove-complex-opera-exp env) (first es)) (Prim op (list (Var x))))))]
		 [(eq? (length es) 2) 
		  (cond
			[(not (atm? (first es))) (let ([x (gensym 'tmp)])
									   (Let x ((remove-complex-opera-exp env) (first es)) ((remove-complex-opera-exp env) (Prim op (cons (Var x) (cdr es))))))]
			[(not (atm? (last es))) (let ([x (gensym 'tmp)])
									   (Let x ((remove-complex-opera-exp env) (last es)) ((remove-complex-opera-exp env) (Prim op (list (car es) (Var x))))))]
			[else (Prim op es)])
		  ]
		 [else (Prim op es)]
		 )])))

(define (explicate_tail e)
	(match e
		[(Var x) (Return (Var x))]
		[(Int n) (Return (Int n))]
		[(Let x rhs body) (explicate_assign rhs x (explicate_tail body))]
		[(Prim op es) (Return (Prim op es))]
		[else (error "explicate_tail unhandled case" e)]))

(define (explicate_assign e x cont)
	(match e
		[(Var y) (Seq (Assign (Var x) (Var y)) cont)]
		[(Int n) (Seq (Assign (Var x) (Int n)) cont)]
		[(Let y rhs body) (explicate_assign rhs y (explicate_assign body x cont))]
		[(Prim op es) (Seq (Assign (Var x) (Prim op es)) cont)]
		[else (error "explicate_assign unhandled case" e)]))

;; remove-complex-opera* : Lvar -> Lvar^mon
(define (remove-complex-opera* p)
   (match p
     [(Program info e) (Program info ((remove-complex-opera-exp '()) e))]))


;; explicate-control : Lvar^mon -> Cvar
(define (explicate-control p)
   (match p
     [(Program info e) (CProgram info (list (cons 'start (explicate_tail e))))]))

(define (select-tail e)
  (match e
	[(Seq s t) (append (select-stmt s) (select-tail t))]
	[(Return t) (select-stmt (Assign (Reg 'rax) t))])
  )
(define (select-atm e)
  (match e
	[(Var x) e]
	[(Int x) (Imm x)])
  )
(define (select-stmt e)
  (match e 
	[(Assign x e)
	 	(if (atm? e)
		  (list (Instr 'movq (list (select-atm e) x)))
			(match e
				[(Prim 'read '()) (list (Callq 'read_int 1) (Instr 'movq (list (Reg 'rax) x)))]
				[(Prim '- (list a)) (list (Instr 'movq (list (select-atm a) x)) (Instr 'negq (list x)))]
				[(Prim '+ (list a b)) (cond
									[(equal? x a) (list (Instr 'addq (list (select-atm b) a)))]
									[(equal? x b) (list (Instr 'addq (list (select-atm a) b)))]
									[(list (Instr 'movq (list (select-atm a) x)) (Instr 'addq (list (select-atm b) x)))]
									)]
				[(Prim '- (list a b)) (cond
									[(equal? x a) (list (Instr 'addq (list (select-atm b) a)))]
									[(list (Instr 'movq (list (select-atm a) x)) (Instr 'subq (list (select-atm b) x)))])]))]))

;; select-instructions : Cvar -> x86var
(define (select-instructions p)
  (match p 
	[(CProgram info (list (cons 'start e))) (X86Program info (list (cons 'start (Block '() (select-tail e)))))]))

;; assign-homes : x86var -> x86var
(define (assign-homes p)
  (error "TODO: code goes here (assign-homes)"))

;; patch-instructions : x86var -> x86int
(define (patch-instructions p)
  (error "TODO: code goes here (patch-instructions)"))

;; prelude-and-conclusion : x86int -> x86int
(define (prelude-and-conclusion p)
  (error "TODO: code goes here (prelude-and-conclusion)"))

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `(
     ;; Uncomment the following passes as you finish them.
     ("uniquify" ,uniquify ,interp-Lvar ,type-check-Lvar)
     ("remove complex opera*" ,remove-complex-opera* ,interp-Lvar ,type-check-Lvar)
     ("explicate control" ,explicate-control ,interp-Cvar ,type-check-Cvar)
     ("instruction selection" ,select-instructions, interp-x86-0)
     ;; ("assign homes" ,assign-homes ,interp-x86-0)
     ;; ("patch instructions" ,patch-instructions ,interp-x86-0)
     ;; ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
     ))
