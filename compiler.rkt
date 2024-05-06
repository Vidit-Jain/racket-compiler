#lang racket
(require racket/set
         racket/stream
         graph
         data/queue)
(require racket/fixnum)
(require "interp-Lint.rkt")
(require "interp-Lfun.rkt")
(require "interp-Lfun-prime.rkt")
(require "interp-Lvar.rkt")
(require "interp-Lif.rkt")
(require "interp-Lwhile.rkt")
(require "interp-Cwhile.rkt")
(require "interp-Cvar.rkt")
(require "interp-Cfun.rkt")
(require "interp-Cif.rkt")
(require "interp-Lvec.rkt")
(require "interp-Lvec-prime.rkt")
(require "interp-Cvec.rkt")

(require "type-check-Lvec.rkt")
(require "type-check-Lfun.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Lwhile.rkt")
(require "type-check-Cvar.rkt")
(require "type-check-Cfun.rkt")
(require "type-check-Lif.rkt")
(require "type-check-Cif.rkt")
(require "type-check-Cwhile.rkt")
(require "type-check-Cvec.rkt")

(require "utilities.rkt")
(require "interp.rkt")
(require "multigraph.rkt")
(require "priority_queue.rkt")
(provide (all-defined-out))

(define all-free-vars (set))
(define all-left-vars (set))

(define (uniquify-exp env)
  (lambda (e)
    (match e
	  [(Apply f c) (Apply ((uniquify-exp env) f) (map (uniquify-exp env) c))]
      [(Var x) (Var (dict-ref env x))]
      [(If a b c) (If ((uniquify-exp env) a) ((uniquify-exp env) b) ((uniquify-exp env) c))]
      [(Let x e body)
       (let ([sub-env (dict-copy env)])
		 (dict-set! sub-env x (gensym x))
         (Let (dict-ref sub-env x) ((uniquify-exp env) e) ((uniquify-exp sub-env) body)))]
      [(SetBang x exp) (SetBang (dict-ref env x) ((uniquify-exp env) exp))]
      [(Begin es body) (Begin (for/list ([e es])
                  ((uniquify-exp env) e)) ((uniquify-exp env) body))]
      [(WhileLoop exp1 exp2) (WhileLoop ((uniquify-exp env) exp1) ((uniquify-exp env) exp2))]
      [(Prim op es)
       (Prim op
             (for/list ([e es])
               ((uniquify-exp env) e)))]
      [_ e])))

(define (extract-var var)
  (match var
	[(quasiquote [,var : ,type]) var]
	)
  )


(define (uniquify-fun env)
  (lambda (fun)
	(match fun
	  [(Def f param type info exp)
	   (let [(sub-env (dict-copy env))]
		(for [(p param)]
		  (dict-set! sub-env (extract-var p) (gensym (extract-var p))))
		; (println sub-env)
		(Def (dict-ref env f) (for/list [(p param)]
							   (match p [(quasiquote [,var : ,type]) `[,(dict-ref sub-env var) : ,type]]))
			 type info ((uniquify-exp sub-env) exp))
		 )])))
  

(define (uniquify p)
  (match p
    [(ProgramDefs info defs) 
	 (let [(env (make-hash))]
	   (for [(def defs)]
		 (match def [(Def f param type info exp) (dict-set! env f (if (equal? f 'main) f (gensym f)))]))
	   (ProgramDefs info (map (uniquify-fun env) defs)))]))

(define (free-vars-exp params)
  (lambda (e)
    (match e
      [(Int _) (void)]
      [(Bool _) (void)]
      [(Void) (void)]
      [(Var x) (if (set-member? params x) (void) (set-add! all-free-vars x))]
      [(Let x e body) ((free-vars-exp (set-add params x)) e) ((free-vars-exp (set-add params x)) body)]
      [(If a b c) (map (free-vars-exp params) (list a b c))]
      [(SetBang x exp) ((free-vars-exp params) exp)]
      [(Begin es body) (map (free-vars-exp params) (append es (list body)))]
      [(WhileLoop exp1 exp2) ((free-vars-exp params) exp1) ((free-vars-exp params) exp2)]
      [(Prim op es) (map (free-vars-exp params) es)]
      [(Apply f es) (map (free-vars-exp params) es)] ;;; NOT SURE ABOUT THIS f could BE A VAR
      [(Lambda (list ^params ...) ^type ^exp) (free-vars-exp (list->set (map extract-var ^params)) ^exp)]
    )
  )
)

(define (left-vars-exp e)
  (match e
    [(SetBang x exp) (set-add! all-left-vars x)]
    [(Let x e body)
     (left-vars-exp e)
     (left-vars-exp body)]
    [(If a b c) (map left-vars-exp (list a b c))]
    [(Begin es body) (map left-vars-exp (append es (list body)))]
    [(WhileLoop exp1 exp2)
     (left-vars-exp exp1)
     (left-vars-exp exp2)]
    [(Prim op es) (map left-vars-exp es)]
    [(Apply f es) (map left-vars-exp es)]
    [(Lambda (list ^params ...) ^type ^exp) (left-vars-exp ^exp)]))

(define (assignment-conversion-exp boxed-vars)
  (lambda (e)
    (match e
      [(Let x e body)
       (if (set-member? boxed-vars x)
           (Let x
                (Prim 'vector ((assignment-conversion-exp boxed-vars) e))
                (assignment-conversion-exp boxed-vars body))
           (Let x
                (assignment-conversion-exp boxed-vars e)
                (assignment-conversion-exp boxed-vars body)))]
      [(SetBang x exp)
       (if (set-member? boxed-vars x)
           (Prim 'vector-set (list (Var x) (Int 0) (assignment-conversion-exp boxed-vars exp)))
           (SetBang x (assignment-conversion-exp boxed-vars exp)))]
      [(If a b c)
       (If (assignment-conversion-exp boxed-vars a)
           (assignment-conversion-exp boxed-vars b)
           (assignment-conversion-exp boxed-vars c))]
      [(Begin es body)
       (Begin (for/list ([e es])
                (assignment-conversion-exp boxed-vars e))
              (assignment-conversion-exp boxed-vars body))]
      [(WhileLoop exp1 exp2)
       (WhileLoop (assignment-conversion-exp boxed-vars exp1)
                  (assignment-conversion-exp boxed-vars exp2))]
      [(Prim op es)
       (Prim op
             (for/list ([e es])
               (assignment-conversion-exp boxed-vars e)))]
      [(Apply f es)
       (Apply f
              (for/list ([e es])
                (assignment-conversion-exp boxed-vars e)))]
      [(Var x) (if (set-member? boxed-vars x) (Prim 'vector-ref (list (Var x) (Int 0))) e)]
      [(Int _) e]
      [(Bool _) e]
      [(Void) e])))


(define (assignment-conversion-def def)
  (match def
    [(Def f params type info exp)
     (free-vars-exp (list->set (map extract-var params)) exp)
     (left-vars-exp exp)
     (Def f params type info exp)])
  (match def
    [(Def f params type info exp) (assignment-conversion-exp exp)]))


(define (assignment-conversion p)
  (match p
    [(ProgramDefs info defs) (map assignment-conversion-def defs)]))

(define (shrink-exp e)
  (match e
    [(Prim 'and (list a b)) (If (shrink-exp a) (shrink-exp b) (Bool #f))]
    [(Prim 'or (list a b)) (If (shrink-exp a) (Bool #t) (shrink-exp b))]
    [(If a b c) (If (shrink-exp a) (shrink-exp b) (shrink-exp c))]
    [(Let x e body) (Let x (shrink-exp e) (shrink-exp body))]
    [(SetBang var exp) (SetBang var (shrink-exp exp))]
    [(Begin es body) (Begin (for/list ([e es])
                (shrink-exp e)) (shrink-exp body))]
    [(WhileLoop exp1 exp2) (WhileLoop (shrink-exp exp1) (shrink-exp exp2))]
    [(Prim op es)
     (Prim op
           (for/list ([e es])
             (shrink-exp e)))]
    [_ e]))

(define (shrink p)
  (match p
    [(ProgramDefsExp info defs exp) 
	 (ProgramDefs info 
		(append (for/list ([def defs])
				  (match def [(Def f param type info exp) (Def f param type info (shrink-exp exp))]))
				(list (Def 'main '() 'Integer '() (shrink-exp exp)))))]
	))
		
(define ((reveal-functions-exp f-arity-map) e)
	(match e
	  [(Apply (Var f) c) (Apply (if (dict-has-key? f-arity-map f) (FunRef f (length c)) (Var f)) (map (reveal-functions-exp f-arity-map) c))]
	  [(Var x) (if (dict-has-key? f-arity-map x) (FunRef x (dict-ref f-arity-map x)) e)]
	  [(If a b c) (If ((reveal-functions-exp f-arity-map) a) ((reveal-functions-exp f-arity-map) b) ((reveal-functions-exp f-arity-map) c))]
	  [(Let x e body)
	   (Let x ((reveal-functions-exp f-arity-map) e) ((reveal-functions-exp f-arity-map) body))]
	  [(SetBang x exp) (SetBang x ((reveal-functions-exp f-arity-map) exp))]
	  [(Begin es body) (Begin (for/list ([e es])
				  ((reveal-functions-exp f-arity-map) e)) ((reveal-functions-exp f-arity-map) body))]
	  [(WhileLoop exp1 exp2) (WhileLoop ((reveal-functions-exp f-arity-map) exp1) ((reveal-functions-exp f-arity-map) exp2))]
	  [(Prim op es)
	   (Prim op
			 (for/list ([e es])
			   ((reveal-functions-exp f-arity-map) e)))]
	  [_ e]))

(define (reveal-functions-def def f-arity-map)
  (match def
	[(Def f param type info exp)
	 (Def f param type info ((reveal-functions-exp f-arity-map) exp))]))

(define (reveal-functions p)
  (let ([dicty (make-hash)])
    (match p
      [(ProgramDefs info defs)
        (match defs
          [(list (Def f-list param-list _ _ _) ...)
           (for/list ([f f-list]
             [p param-list])
             (dict-set! dicty f (length p)))])
        (ProgramDefs info (map (curryr reveal-functions-def dicty) defs))])))





(define (collect-set! e)
  (match e
  [(Let x rhs body) (set-union (collect-set! rhs) (collect-set! body))]
  [(SetBang var rhs) (set-union (set var) (collect-set! rhs))]
    [(If a b c) (set-union (collect-set! a) (collect-set! b) (collect-set! c))]
  [(Begin es body) (set-union (foldr (lambda (item acc)
                     (set-union acc (collect-set! item))) (set) es) (collect-set! body))]
    [(WhileLoop exp1 exp2) (set-union (collect-set! exp1) (collect-set! exp2))]
    [(Prim op es)
     (foldl (lambda (item acc)
          (set-union acc (collect-set! item))) (set) es)]
  [_ (set)]))

(define ((uncover-get!-exp set!-vars) e)
  (match e
  [(Var x)
   (if (set-member? set!-vars x)
     (GetBang x)
     e)]  
    [(If a b c) (If ((uncover-get!-exp set!-vars) a) ((uncover-get!-exp set!-vars) b) ((uncover-get!-exp set!-vars) c))]
    [(Let x e body) (Let x ((uncover-get!-exp set!-vars) e) ((uncover-get!-exp set!-vars) body))]
    [(SetBang var exp) (SetBang var ((uncover-get!-exp set!-vars) exp))]
    [(Begin es body) (Begin (for/list ([e es])
                ((uncover-get!-exp set!-vars) e)) ((uncover-get!-exp set!-vars) body))]
    [(WhileLoop exp1 exp2) (WhileLoop ((uncover-get!-exp set!-vars) exp1) ((uncover-get!-exp set!-vars) exp2))]
    [(Apply f es) (Apply f (for/list ([e es]) ((uncover-get!-exp set!-vars) e)))]
    [(Prim op es)
     (Prim op
           (for/list ([e es])
             ((uncover-get!-exp set!-vars) e)))]
  [_ e]))
(define (uncover-get!-def def)
  (match def
     [(Def f params ret-type info exp) (Def f params ret-type info ((uncover-get!-exp (collect-set! exp)) exp))]))

(define (uncover-get! p)
  (match p
    [(ProgramDefs info defs) (ProgramDefs info (map uncover-get!-def defs))]))

(define (limit-functions p)
  (match p
    [(ProgramDefs info defs) (ProgramDefs info (for/list ([def defs]) (limit-functions-def def)))])
)

(define (limit-functions-def def)
  (match def
    [(Def f params ret-type info body)
     (let ([extra-param-tup (gensym 'tup)] [param-tup-map (make-hash)])
       (cond
         [(> (length params) 6)
          (match params
            [(list `(,var-names : ,var-types) ...)
             (for ([i (in-range 5 (length params))])
               (dict-set! param-tup-map (list-ref var-names i) (Prim 'vector-ref (list (Var extra-param-tup) (Int (- i 5))))))
             (let ([extra-tup-type (cons 'Vector
                                          (for/list ([i (in-range 5 (length params))])
                                            (list-ref var-types i)))])
               (Def f
                    (append (take params 5) (list `(,extra-param-tup : ,extra-tup-type)))
                    ret-type
                    info
                    (limit-functions-exp body param-tup-map)))])]
         [else (Def f params ret-type info (limit-functions-exp body param-tup-map))]))]
    [_
     error
     ("limit-functions-def unhandled case" def)]))


(define (limit-functions-exp exp tuple-param-map)
  (match exp
    [(Int _) exp]
    [(Bool _) exp]
    [(Void) exp]
    [(Var x) (if (dict-has-key? tuple-param-map x) (dict-ref tuple-param-map x) exp)]
    [(FunRef f n) (if (dict-has-key? tuple-param-map f) (dict-ref tuple-param-map f) exp)]
    [(Prim op es)
     (Prim op
           (for/list ([e es])
             (limit-functions-exp e tuple-param-map)))]
    [(Let x e body)
     (Let x (limit-functions-exp e tuple-param-map) (limit-functions-exp body tuple-param-map))]
    [(If a b c)
     (If (limit-functions-exp a tuple-param-map)
         (limit-functions-exp b tuple-param-map)
         (limit-functions-exp c tuple-param-map))]
    [(SetBang x e) (SetBang x (limit-functions-exp e tuple-param-map))]
    [(GetBang x) (GetBang (limit-functions-exp x tuple-param-map))]
    [(Begin es body)
     (Begin (for/list ([e es])
              (limit-functions-exp e tuple-param-map))
            (limit-functions-exp body tuple-param-map))]
    [(WhileLoop exp1 exp2)
     (WhileLoop (limit-functions-exp exp1 tuple-param-map)
                (limit-functions-exp exp2 tuple-param-map))]
    [(Def f params ret-type info body) (limit-functions-def (Def f params ret-type info body))]
    [(Apply f es)
     ; ( printf "Apply: ~a\n" es)
     ; ( printf "Length: ~a\n" (length es))
     (cond
       [(> (length es) 5)
        (let ([extra-param-tup (gensym 'extra-param-tup)])
          (Let extra-param-tup
               (Prim 'vector
                     (map (curryr limit-functions-exp tuple-param-map)
                          (for/list ([i (in-range 5 (length es))])
                            (list-ref es i))))
               (Apply f (append (take es 5) (list (Var extra-param-tup))))))]

       [else
        (Apply f
               (for/list ([e es])
                 (limit-functions-exp e tuple-param-map)))])]))



(define (expose-allocation-def def)
  (match def
     [(Def f params ret-type info exp) (Def f params ret-type info ((expose-allocation-exp '()) exp))]))
(define (expose-allocation p)
  (match p
    [(ProgramDefs info defs) (ProgramDefs info (map expose-allocation-def defs))]))

(define (gen-tuple-init temp-vars-list vector-name index)
  (if (empty? temp-vars-list)
    (Var vector-name)
    (Let '_ (Prim 'vector-set! (list (Var vector-name) (Int index) (Var (car temp-vars-list)))) (gen-tuple-init (cdr temp-vars-list) vector-name (+ index 1)))))

(define (gen-let-exps vals-for-init vals-for-bind temp-vars-list type)
  (if (empty? vals-for-bind)
      (let ([bytes (* 8 (+ (length vals-for-init) 1))] [vector-name (gensym 'vector)])
        (Let
         '_
         (If (Prim '< (list (Prim '+ (list (GlobalValue 'free_ptr) (Int bytes))) (GlobalValue 'fromspace_end))) (Void) (Collect bytes))
         (Let vector-name
              (Allocate (length vals-for-init) type)
              (gen-tuple-init temp-vars-list vector-name 0))))
      (let ([temp-var (gensym 'x)])
        (Let temp-var
             (car vals-for-bind)
             (gen-let-exps vals-for-init
                           (rest vals-for-bind)
                           (append temp-vars-list (list temp-var))
                           type)))))

(define (expose-allocation-exp env)
  (lambda (e)
    (match e
      [(HasType (Prim 'vector es) type)
       (let ([list-vals (for/list ([e es])
                          ((expose-allocation-exp env) e))])
         (gen-let-exps list-vals list-vals '() type))]
      [(Let x e body)
       (let ([e^ ((expose-allocation-exp env) e)]) (Let x e^ ((expose-allocation-exp env) body)))]
      [(SetBang var exp) (SetBang var ((expose-allocation-exp env) exp))]
      [(If a b c)
       (If ((expose-allocation-exp env) a)
           ((expose-allocation-exp env) b)
           ((expose-allocation-exp env) c))]
      [(Begin es body)
       (Begin (for/list ([e es])
                ((expose-allocation-exp env) e))
              ((expose-allocation-exp env) body))]
      [(WhileLoop exp1 exp2)
       (WhileLoop ((expose-allocation-exp env) exp1) ((expose-allocation-exp env) exp2))]
      [(Apply f es) (Apply f (for/list ([e es]) ((expose-allocation-exp env) e)))]
      [(Prim op es)
       (Prim op
             (for/list ([e es])
               ((expose-allocation-exp env) e)))]
      [(Void) e]
      [(Int n) e]
      [(Bool n) e]
      [(Var x) e]
      [(Prim 'vector es) e]
      [_ e])))

(define (remove-complex-opera-exp
         env) ;; TODO: this function currently does nothing. Your code goes here
  (lambda (e)
    (match e
      [(Begin es body)
       (Begin (for/list ([e es])
                ((remove-complex-opera-exp env) e))
              ((remove-complex-opera-exp env) body))]
      [(WhileLoop exp1 exp2)
       (WhileLoop ((remove-complex-opera-exp env) exp1) ((remove-complex-opera-exp env) exp2))]
      [(SetBang var exp) (SetBang var ((remove-complex-opera-exp env) exp))]
      [(GetBang x) (Var x)]
      [(If a b c)
	   (match a
		[(Apply _ _) (let ([x (gensym 'tmp)])
					   (Let x ((remove-complex-opera-exp env) a)
							(If (Var x)
								((remove-complex-opera-exp env) b)
								((remove-complex-opera-exp env) c)
							)
						))]
		[_ (If ((remove-complex-opera-exp env) a)
           ((remove-complex-opera-exp env) b)
           ((remove-complex-opera-exp env) c))])]
      ; [(If a b c)
      ;  (rco_helper (If a b c) env '() (list a b c))]
      [(Let x e body)
       (Let x ((remove-complex-opera-exp env) e) ((remove-complex-opera-exp env) body))]
      [(Prim op es)
       (rco_helper (Prim op es) env '() es)]
      [(Def f params ret-type info exp)
       (Def f params ret-type info ((remove-complex-opera-exp env) exp))]
      [(Apply f c) (rco_helper (Apply f c) env '() c)]
      [_ e])))

(define (rco_helper exp rco-env env operands)
  (match exp
    [(Prim op es)
     (if (empty? operands)
         (Prim op
               (for/list ([e es])
                 (dict-ref env e)))
         (match (first operands)
           [(? atm? op) (rco_helper exp rco-env (dict-set env op op) (rest operands))]
           [op
            (let ([x (gensym 'tmp)])
              (Let x ((remove-complex-opera-exp rco-env) op) (rco_helper exp rco-env (dict-set env op (Var x)) (rest operands))))]))]
    [(Apply f c)
     (if (empty? operands)
       (let ([fun (gensym 'fun)])
         (Let fun f 
                    (Apply (Var fun)
                    (for/list ([e c])
                      (dict-ref env e)))))
         (match (first operands)
           [(? atm? f) (rco_helper exp rco-env (dict-set env f f) (rest operands))]
           [f
            (let ([x (gensym 'tmp)])
              (Let x ((remove-complex-opera-exp rco-env) f) (rco_helper exp rco-env (dict-set env f (Var x)) (rest operands))))]))]
    [_ (error "rco_helper unhandled case" exp)]))

;; remove-complex-opera* : Lvar -> Lvar^mon
(define (remove-complex-opera* p)
  (match p
    [(ProgramDefs info defs) (ProgramDefs info (for/list ([def defs]) ((remove-complex-opera-exp (make-hash)) def)))]))
    ;;; [(Program info e) (Program info ((remove-complex-opera-exp '()) e))]))

(define (explicate_tail e)
  (match e
    [(Var x) (Return (Var x))]
    [(Int n) (Return (Int n))]
    [(Bool n) (Return (Bool n))]
    [(Let x rhs body) (explicate_assign rhs x (explicate_tail body))]
    [(Prim op es) (Return (Prim op es))]
    [(If a b c) (explicate_pred a (explicate_tail b) (explicate_tail c))]
    [(Begin es body) #:when (empty? es) (explicate_tail body)]
    [(Begin es body) (explicate-effect (first es) (explicate_tail (Begin (rest es) body)))]
    [(SetBang y rhs) (explicate_assign rhs y (Return (Void)))]
    [(WhileLoop cnd body) 
       (let [(loop (gensym 'loop))]
         (set! basic-blocks (cons (cons loop (explicate_pred cnd (explicate-effect body (Goto loop)) (Return (Void)))) basic-blocks))
         (Goto loop))]
    [(GlobalValue x) (Return (GlobalValue x))]
    [(Allocate n type) (Return (Allocate n type))]
    [(Collect n) (Return (Collect n))]
    [(Apply f es) (TailCall f es)]
    [(FunRef f n) (Return (FunRef f n))]
    [_ (error "explicate_tail unhandled case" e)])                                 
    )

(define (explicate_assign e x cont)
  (match e
    [(Var y) (Seq (Assign (Var x) (Var y)) cont)]
    [(Int n) (Seq (Assign (Var x) (Int n)) cont)]
    [(Bool n) (Seq (Assign (Var x) (Bool n)) cont)]
    [(Let y rhs body) (explicate_assign rhs y (explicate_assign body x cont))]
    [(Prim op es) (Seq (Assign (Var x) (Prim op es)) cont)]
    [(Begin es body) #:when (empty? es) (explicate_assign body x cont)]
    [(Begin es body) (explicate-effect (first es) (explicate_assign (Begin (rest es) body) x cont))]
    [(If a b c) (explicate_pred a (explicate_assign b x cont) (explicate_assign c x cont))]
    [(SetBang y rhs) (explicate_assign rhs y (Assign (Var x) (Void)))]
    [(GlobalValue y) (Seq (Assign (Var x) (GlobalValue y)) cont)]
    [(Allocate n type) (Seq (Assign (Var x) (Allocate n type)) cont)]
    [(Apply f es) (Seq (Assign (Var x) (Call f es)) cont)]
    [(FunRef f n) (Seq (Assign (Var x) (FunRef f n)) cont)]
    [(Collect n) (Seq (Collect n) cont)]
    [(Void) (Seq (Assign (Var x) (Void)) cont)]
    [(WhileLoop cnd body) 
     (Seq 
       (Assign (Var x) (Void))
       (let [(loop (gensym 'loop))]
         (set! basic-blocks (cons (cons loop (explicate_pred cnd (explicate-effect body (Goto loop)) cont)) basic-blocks))
         (Goto loop)))]
    [else (error "explicate_assign unhandled case" e)]))

(define (explicate_pred cnd thn els)
  (match cnd
    [(Var x) (IfStmt (Prim 'eq? (list (Var x) (Bool #t))) (create_block thn) (create_block els))]
    [(Let x rhs body) (explicate_assign rhs x (explicate_pred body thn els))]
    [(Apply f es) (IfStmt (Prim 'eq? (list (Call f es) (Bool #t))) (create_block thn) (create_block els))]
    [(Prim 'not (list e))
     (IfStmt (Prim 'eq? (list e (Bool #t))) (create_block els) (create_block thn))]
    [(Prim op es)
     #:when (or (eq? op 'eq?) (eq? op '<) (eq? op '>) (eq? op '<=) (eq? op '>=))
     (IfStmt (Prim op es) (create_block thn) (create_block els))]
    [(Prim op es) #:when (or (eq? op 'vector-set!) (eq? op 'vector-ref))
      (let ([cnd-tmp (gensym 'tmp)])
      (explicate_assign cnd cnd-tmp (IfStmt (Prim 'eq? (list (Var cnd-tmp) (Bool #t))) (create_block thn) (create_block els))))]      
    [(Bool b) (if b thn els)]
    [(Begin es body) #:when (empty? es) (explicate_pred body thn els)]
    [(Begin es body) (explicate-effect (first es) (explicate_pred (Begin (rest es) body) thn els))]
    [(If cnd^ thn^ els^)
     (explicate_pred cnd^ (explicate_pred thn^ thn els) (explicate_pred els^ thn els))]))

(define (explicate-effect e cont)
  (match e
    [(SetBang x rhs) (explicate_assign rhs x cont)]
    [(Begin es body) #:when (empty? es) (explicate-effect body cont)]
    [(Begin es body) (explicate-effect (first es) (explicate-effect (Begin (rest es) body) cont))]
    [(WhileLoop cnd body) 
     (let [(loop (gensym 'loop))]
       (set! basic-blocks (cons (cons loop (explicate_pred cnd (explicate-effect body (Goto loop)) cont)) basic-blocks))
     (Goto loop)
     )]
    [(Let x rhs body) (explicate_assign rhs x (explicate-effect body cont))]
    [(If cnd thn els) (explicate_pred cnd (explicate-effect thn cont) (explicate-effect els cont))]
    [(Prim 'vector-set! (list a b c)) (Seq e cont)]
    [(Collect n) (Seq (Collect n) cont)]
    [(Apply f es) (Seq (Call f es) cont)]
    [_ cont]
  )
)


(define basic-blocks '())

(define (create_block tail)
  (match tail
    [(Goto label) (Goto label)]
    [else
     (let ([label (gensym 'block)])
       (set! basic-blocks (cons (cons label tail) basic-blocks))
       (Goto label))]))

(define (explicate-def def)
  (set! basic-blocks '())
	(match def
	  [(Def f param type info exp) 
     (set! basic-blocks (cons (cons (symbol-append f '_start) (explicate_tail exp)) basic-blocks))
     (Def f param type info basic-blocks)]
	  )
  )
;; explicate-control : Lvar^mon -> Cvar
(define (explicate-control p)
  (set! basic-blocks '())
  (match p
    [(ProgramDefs info defs) (ProgramDefs info (map explicate-def defs))]))


(define (select-move-args es)
  (for/list ([i (in-range (length es))])
    (Instr 'movq (list (select-atm (list-ref es i)) (Reg (vector-ref arg-registers i))))))

(define (select-tail e)
  (match e
    [(Seq s t) (append (select-stmt s) (select-tail t))]
    [(Return t) (append (select-stmt (Assign (Reg 'rax) t)) (list (Jmp 'conclusion)))]
    [(Goto l) (list (Jmp l))]
    [(IfStmt (Prim cmp (list (? atm? a) (? atm? b))) (Goto thn) (Goto els))
     #:when (equal? cmp 'eq?)
     (list (Instr 'cmpq (list (select-atm b) (select-atm a))) (JmpIf 'e thn) (Jmp els))]
    [(IfStmt (Prim cmp (list (? atm? a) (? atm? b))) (Goto thn) (Goto els))
     #:when (equal? cmp '<)
     (list (Instr 'cmpq (list (select-atm b) (select-atm a))) (JmpIf 'l thn) (Jmp els))]
    [(IfStmt (Prim cmp (list (? atm? a) (? atm? b))) (Goto thn) (Goto els))
     #:when (equal? cmp '>)
     (list (Instr 'cmpq (list (select-atm b) (select-atm a))) (JmpIf 'g thn) (Jmp els))]
    [(IfStmt (Prim cmp (list (? atm? a) (? atm? b))) (Goto thn) (Goto els))
     #:when (equal? cmp '<=)
     (list (Instr 'cmpq (list (select-atm b) (select-atm a))) (JmpIf 'le thn) (Jmp els))]
    [(IfStmt (Prim cmp (list (? atm? a) (? atm? b))) (Goto thn) (Goto els))
     #:when (equal? cmp '>=)
     (list (Instr 'cmpq (list (select-atm b) (select-atm a))) (JmpIf 'ge thn) (Jmp els))]
    [(TailCall f es) (append (select-move-args es) (list (TailJmp f (length es))))] 
    ))

(define (gen-vector-tag types)
  (define list-types (match types [`(Vector ,a ...) a]))
  (define mask 0)

  (for ([t list-types] [i (in-range (length list-types))])
    (let ([tag (if (eq? t 'Vector) 1 0)])
      (set! mask (bitwise-ior mask (arithmetic-shift tag i)))))

  (bitwise-ior (bitwise-ior (arithmetic-shift mask 7) (arithmetic-shift (length list-types) 1)) 1)  
)

(define (select-atm e)
  (match e
    [(Var x) e]
    [(Int x) (Imm x)]
    [(Bool x) (Imm (if x 1 0))]
    [(Void) (Imm 0)]
    [(GlobalValue x) (Global x)]
  ))
(define (select-stmt e)
  (match e
    [(Prim 'read '()) (list (Callq 'read_int 0))]
    [(Prim 'vector-set! (list (? atm? tup) (Int n) (? atm? rhs)))
     (list (Instr 'movq (list (select-atm tup) (Reg 'r11)))
           (Instr 'movq (list (select-atm rhs) (Deref 'r11 (* 8 (+ n 1))))))]
    [(Collect bytes)
     (list (Instr 'movq (list (Reg 'r15) (Reg 'rdi)))
           (Instr 'movq (list (Imm bytes) (Reg 'rsi)))
           (Callq 'collect 0))]
    [(Assign x e)
     (if (atm? e)
         (list (Instr 'movq (list (select-atm e) x)))
         (match e
           [(Call f es)
            (append (select-move-args es)
                    (list (IndirectCallq f (length es)) (Instr 'movq (list (Reg 'rax) x))))]
           [(FunRef f n) (list (Instr 'leaq (list (Global f) x)))]
           [(GlobalValue x^) (list (Instr 'movq (list (Global x^) x)))]
           [(Allocate n type)
            (list (Instr 'movq (list (Global 'free_ptr) (Reg 'r11)))
                  (Instr 'addq (list (Imm (* 8 (+ 1 n))) (Global 'free_ptr)))
                  (Instr 'movq (list (Imm (gen-vector-tag type)) (Deref 'r11 0)))
                  (Instr 'movq (list (Reg 'r11) x)))]
           [(Prim 'read '()) (list (Callq 'read_int 0) (Instr 'movq (list (Reg 'rax) x)))]
           [(Prim '- (list a)) (list (Instr 'movq (list (select-atm a) x)) (Instr 'negq (list x)))]
           [(Prim '+ (list a b))
            (cond
              [(equal? x a) (list (Instr 'addq (list (select-atm b) a)))]
              [(equal? x b) (list (Instr 'addq (list (select-atm a) b)))]
              [(list (Instr 'movq (list (select-atm a) x)) (Instr 'addq (list (select-atm b) x)))])]
           [(Prim '- (list a b))
            (cond
              [(equal? x a) (list (Instr 'subq (list (select-atm b) a)))]
              [(list (Instr 'movq (list (select-atm a) x)) (Instr 'subq (list (select-atm b) x)))])]
           [(Prim 'not (list (== x))) (list (Instr 'xorq (list (Imm 1) x)))]
           [(Prim 'not (list (? atm? a)))
            (list (Instr 'movq (list (select-atm a) x)) (Instr 'notq (list x)))]
           [(Prim 'eq? (list (? atm? a) (? atm? b)))
            (list (Instr 'cmpq (list (select-atm b) (select-atm a)))
                  (Instr 'set (list 'e (ByteReg 'al)))
                  (Instr 'movzbq (list (ByteReg 'al) x)))]
           [(Prim '< (list (? atm? a) (? atm? b)))
            (list (Instr 'cmpq (list (select-atm b) (select-atm a)))
                  (Instr 'set (list 'l (ByteReg 'al)))
                  (Instr 'movzbq (list (ByteReg 'al) x)))]
           [(Prim '> (list (? atm? a) (? atm? b)))
            (list (Instr 'cmpq (list (select-atm b) (select-atm a)))
                  (Instr 'set (list 'g (ByteReg 'al)))
                  (Instr 'movzbq (list (ByteReg 'al) x)))]
           [(Prim '<= (list (? atm? a) (? atm? b)))
            (list (Instr 'cmpq (list (select-atm b) (select-atm a)))
                  (Instr 'set (list 'le (ByteReg 'al)))
                  (Instr 'movzbq (list (ByteReg 'al) x)))]
           [(Prim '>= (list (? atm? a) (? atm? b)))
            (list (Instr 'cmpq (list (select-atm b) (select-atm a)))
                  (Instr 'set (list 'ge (ByteReg 'al)))
                  (Instr 'movzbq (list (ByteReg 'al) x)))]
           [(Prim 'vector-ref (list (? atm? tup) (Int n)))
            (list (Instr 'movq (list (select-atm tup) (Reg 'r11)))
                  (Instr 'movq (list (Deref 'r11 (* 8 (+ n 1))) x)))]
           [(Prim 'vector-set! (list (? atm? tup) (Int n) (? atm? rhs)))
            (list (Instr 'movq (list (select-atm tup) (Reg 'r11)))
                  (Instr 'movq (list (select-atm rhs) (Deref 'r11 (* 8 (+ n 1)))))
                  (Instr 'movq (list (Imm 0) x)))]
           [(Prim 'vector-length (list (? atm? tup)))
            (list (Instr 'movq (list (select-atm tup) (Reg 'r11)))
                  (Instr 'movq (list (Deref 'r11 0) (Reg 'rax)))
                  (Instr 'sarq (list (Imm 1) (Reg 'rax)))
                  (Instr 'andq (list (Imm 63) (Reg 'rax)))
                  (Instr 'movq (list (Reg 'rax) x)))]))]))

(define (move-params-to-reg body params func-name block-name)
  (if (equal? (symbol-append func-name '_start) block-name)
      (append (for/list ([i (in-range (length params))])
                (Instr 'movq (list (Reg (vector-ref arg-registers i)) (Var (extract-var (list-ref params i))))))
              body)
      body))

(define (select-instructions-def def)
  (match def
    [(Def f param type info (list (cons label-list tail-list) ...))
    (Def f '() 'Integer (dict-set info 'num-params (length param)) (for/list ([label label-list] [tail tail-list])
          (cons label (Block '() (move-params-to-reg (select-tail tail) param f label)))))]))

(define (select-instructions p)
  (match p 
    [(ProgramDefs info defs)
      (X86ProgramDefs info (map select-instructions-def defs))
    ]
  )
)
(define (assign-var-offset var-list)
  (match var-list
    ['() (values '() 0)]
    [(list (cons var 'Integer) rest ...)
     (let-values ([(var-map offset) (assign-var-offset rest)])
       (values (dict-set var-map var (+ offset 8)) (+ offset 8)))]))

(define (assign-homes-var env)
  (lambda (var)
    (match var
      [(Imm i) (Imm i)]
      [(Reg r) (Reg r)]
      [(Var x) (Deref 'rbp (- (dict-ref env x)))])))

(define (assign-homes-instr env)
  (lambda (instr)
    (match instr
      [(Instr name args)
       (Instr name
              (for/list ([arg args])
                ((assign-homes-var env) arg)))]
      [_ instr])))

;; assign-homes : x86var -> x86var
(define (assign-homes p)
  (match p
    [(X86Program info (list (cons label (Block block-info instrs))))
     (let ([var-list (dict-ref info 'locals-types)])
       (let-values ([(var-map total-space) (assign-var-offset var-list)])
         (X86Program (dict-set info 'stack-space total-space)
                     (list (cons label
                                 (Block block-info
                                        (for/list ([instr instrs])
                                          ((assign-homes-instr var-map) instr))))))))]))

;(error "TODO: code goes here (assign-homes)"))

(define (big-int? x)
  (> x (expt 2 16)))

(define (patch-instruction instr)
  (match instr
    [(Instr 'movq (list a a)) (list)]
    [(Instr 'cmpq (list a (Imm b)))
     (list (Instr 'movq (list (Imm b) (Reg 'rax))) (Instr 'cmpq (list a (Reg 'rax))))]
    [(Instr name (list (Imm (? big-int? i)) (Deref reg offset)))
     (list (Instr 'movq (list (Imm i) (Reg 'rax))) (Instr name (list (Reg 'rax) (Deref reg offset))))]
    [(Instr name (list (Deref reg offset) (Imm (? big-int? i))))
     (list (Instr 'movq (list (Imm i) (Reg 'rax))) (Instr name (list (Deref reg offset) (Reg 'rax))))]
    [(Instr name (list (Deref reg1 offset1) (Deref reg2 offset2)))
     (list (Instr 'movq (list (Deref reg1 offset1) (Reg 'rax)))
           (Instr name (list (Reg 'rax) (Deref reg2 offset2))))]
    [(TailJmp var fun)
     #:when (not (equal? var (Reg 'rax)))
     (list (Instr 'movq (list var (Reg 'rax))) (TailJmp (Reg 'rax) fun))]
    [_ (list instr)]))

;;; (define (patch-instructions-def def)
;;; 	(match def
;;; 	  [(Def f param type info (list (cons label-list (Block block-info-list instrs-list)) ...))
;;; 	   (Def f param type info (for/list ([label label-list] [block-info block-info-list] [instrs instrs-list])
;;;                    (cons label
;;;                          (Block block-info
;;;                                 (apply append (for/list ([instr instrs])
;;;                                                  (patch-instruction instr)))))))]))

(define (patch-instructions-def def)
  (match def
    [(Def f param type info (list block-lst ...))
     (Def f
          param
          type
          info
          (for/list ([block block-lst])
            (printf "rainy-bess-block: ~a\n" block)
            (match block
              [(cons label (Block info instrs))
               (cons label
                     (Block info
                            (apply append
                                   (for/list ([instr instrs])
                                     (patch-instruction instr)))))])))]))
;; patch-instructions : x86var -> x86int

(define (patch-instructions p)
  (match p
    [(X86ProgramDefs info defs) (X86ProgramDefs info (map patch-instructions-def defs))]))

(define (compute-delta C S)
  (Imm (- (align (+ C S) 16) C))
  )

(define (align-16 x)
  (if (zero? (remainder x 16))
      x
      (+ x 8)))

(define (prelude-and-conclusion-def def) ;;; STEP 5 of book not implemented yet
  (match def
    [(Def f param type info (list block-list ...))
     (append
      (list (cons f
                  (Block
                   '()
                   (append
                    (list (Instr 'pushq (list (Reg 'rbp))) (Instr 'movq (list (Reg 'rsp) (Reg 'rbp))))
                    (for/list ([reg (dict-ref info 'callee-used)])
                      (Instr 'pushq (list (Reg (color->register reg)))))
                    (list (Instr 'subq
                                 (let ([C (* 8 (length (dict-ref info 'callee-used)))]
                                       [S (dict-ref info 'stack-space)])
                                   (list (compute-delta C S) (Reg 'rsp)))))
                    (if (equal? f 'main)
                        (list (Instr 'movq (list (Imm 65536) (Reg 'rdi)))
                              (Instr 'movq (list (Imm 65536) (Reg 'rsi)))
                              (Callq 'initialize 2)
                              (Instr 'movq (list (Global 'rootstack_begin) (Reg 'r15)))
                              (Instr 'movq (list (Imm 0) (Deref 'r15 0)))
                              (Instr 'addq (list (Imm (dict-ref info 'root-stack-space)) (Reg 'r15))))
                        (list (Instr 'addq
                                     (list (Imm (dict-ref info 'root-stack-space)) (Reg 'r15)))))
                    (list (Jmp (symbol-append f '_start)))))))
      (map (curryr translate-tailjmp-block f info) block-list)
      (list (cons (symbol-append f '_conclusion)
                  (Block '() (append (gen-conclude-def f info) (list (Retq)))))))]))


(define (gen-conclude-def f info)
  (append (list (Instr 'addq
                       (let ([C (* 8 (length (dict-ref info 'callee-used)))]
                             [S (dict-ref info 'stack-space)])
                         (list (compute-delta C S) (Reg 'rsp)))))
          (for/list ([reg (reverse (dict-ref info 'callee-used))])
            (Instr 'popq (list (Reg (color->register reg)))))
          (list (Instr 'subq (list (Imm (dict-ref info 'root-stack-space)) (Reg 'r15)))
                (Instr 'popq (list (Reg 'rbp))))))


(define (translate-tailjmp-block block f info)
  (match block
    [(cons label (Block ^info instrs))
     (match (last instrs)
       [(TailJmp var n)
        (cons label (Block ^info (append (take instrs (- (length instrs) 1)) (gen-conclude-def f info) (list (IndirectJmp var)))))  
      ]
      [(Jmp 'conclusion) (cons label (Block ^info (append (take instrs (- (length instrs) 1)) (list (Jmp (symbol-append f '_conclusion))))))]
       [_ block])]))

(define (prelude-and-conclusion p)
  (match p
    [(X86ProgramDefs info defs)
     (X86Program info (apply append (map prelude-and-conclusion-def defs)))]))

(define caller-saved (set 'rax 'rcx 'rdx 'rsi 'rdi 'r8 'r9 'r10 'r11))
(define callee-saved (set 'rsp 'rbp 'rbx 'r12 'r13 'r14 'r15))
(define (decomp-bytereg byte)
	(match byte
	  ['al 'rax]))
(define (locations-appear args)
  (if (empty? args)
      (set)
      (match (first args)
        [(Reg a) (set-add (locations-appear (rest args)) a)]
        [(ByteReg a) (set-add (locations-appear (rest args)) (decomp-bytereg a))]
        [(Var a) (set-add (locations-appear (rest args)) a)]
        [(Imm a) (locations-appear (rest args))]
        [(Global a) (locations-appear (rest args))]
        [(Deref a b) (set-add (locations-appear (rest args)) a)])))

(define (locations-read-by-instr instr)
  (match instr
    [(Instr 'addq (list arg1 arg2)) (locations-appear (list arg1 arg2))]
    [(Instr 'leaq (list arg1 arg2)) (locations-appear (list arg1))]
    [(Instr 'subq (list arg1 arg2)) (locations-appear (list arg1 arg2))]
    [(Instr 'negq (list arg)) (locations-appear (list arg))]
    [(Instr 'movq (list arg1 arg2)) (locations-appear (list arg1))]
    [(Instr 'pushq (list arg)) (locations-appear (list arg (Reg 'rsp)))]
    [(Instr 'popq (list arg)) (locations-appear (list (Reg 'rsp)))]
    [(Instr 'cmpq (list arg1 arg2)) (locations-appear (list arg1 arg2))]
    [(Instr 'xorq (list arg1 arg2)) (locations-appear (list arg1 arg2))]
    [(Instr 'set (list arg1 arg2)) (set)]
    [(Instr 'movzbq (list arg1 arg2)) (locations-appear (list arg1))]
    [(Callq name num) (list->set (vector->list (vector-take arg-registers num)))]
    [(IndirectCallq name num) (set-union (locations-appear (list name)) (list->set (vector->list (vector-take arg-registers num))))]
    [(TailJmp name num) (set-union (locations-appear (list name)) (list->set (vector->list (vector-take arg-registers num))))]
    [_ (set)]))

;;; still dont know what to do with jmp, callq, retq

(define (locations-write-by-instr instr)
  (match instr
    [(Instr 'addq (list arg1 arg2)) (locations-appear (list arg2))]
    [(Instr 'leaq (list arg1 arg2)) (locations-appear (list arg2))]
    [(Instr 'subq (list arg1 arg2)) (locations-appear (list arg2))]
    [(Instr 'negq (list arg)) (locations-appear (list arg))]
    [(Instr 'movq (list arg1 arg2)) (locations-appear (list arg2))]
    [(Instr 'pushq (list arg)) (locations-appear (list (Reg 'rsp)))]
    [(Instr 'popq (list arg)) (locations-appear (list arg (Reg 'rsp)))]
    [(Callq name num) (locations-appear (list (Reg 'rax) (Reg 'rcx) (Reg 'rdx) (Reg 'rsi) (Reg 'rdi) (Reg 'r8)(Reg 'r9)(Reg 'r10)(Reg 'r11)))]
    [(Instr 'cmpq (list arg1 arg2)) (set)]
    [(Instr 'xorq (list arg1 arg2)) (locations-appear (list arg2))]
    [(Instr 'set (list arg1 arg2)) (locations-appear (list arg2))]
    [(Instr 'movzbq (list arg1 arg2)) (locations-appear (list arg2))]
    [(Callq name num) caller-saved]
    [(IndirectCallq name num) caller-saved]
    [(TailJmp name num) caller-saved]
    [_ (set)]))

(define live-before-label (make-hash))
(define (uncover-live-instrs instrs init-live-after)
  (foldr
   (lambda (instr acc)
     (match instr
       [(JmpIf _ label) (cons (set-union (dict-ref live-before-label label) (first acc)) acc)]
       [(Jmp label) 
        (cons (dict-ref live-before-label label) acc)]
       [_
        (cons (set-union (set-subtract (first acc) (locations-write-by-instr instr))
                         (locations-read-by-instr instr))
              acc)]))
   init-live-after
   instrs))
 (define ((do-uncover dict-label-block) block-label init-live-after)
   (match (dict-ref dict-label-block block-label) 
     [(Block block-info instrs)
      (let ([live-sets (uncover-live-instrs instrs init-live-after)])
       (dict-set! dict-label-block block-label (Block (dict-set block-info 'live-after (rest live-sets)) instrs))
         (first live-sets))]))
(define (uncover-live-def def)
  (dict-clear! live-before-label)
  (match def
  [(Def f param type info dict-label-block-temp) 
   (define dict-label-block (make-hash dict-label-block-temp))
   (let ([label-list (hash-keys dict-label-block)] [block-list (hash-values dict-label-block)])
 		(match block-list
 		  [(list (Block block-info-list instrs-list) ...)
 			(dict-set! live-before-label 'conclusion (set 'rax 'rsp))
           (analyze_dataflow (transpose (gen-cfg label-list instrs-list)) (do-uncover dict-label-block) (set) set-union)
             (Def f param type (dict-set info 'live live-before-label) (hash->list dict-label-block))]))]))

 (define (uncover-live p)
   (dict-clear! live-before-label)
   (match p
     [(X86ProgramDefs pinfo defs)
      (X86ProgramDefs pinfo (map uncover-live-def defs))]))

(define (analyze_dataflow G transfer bottom join)
  (for ([v (in-vertices G)])
    (dict-set! live-before-label v bottom))
  (define worklist (make-queue))
  (for ([v (in-vertices G)])
    (enqueue! worklist v))
  (define trans-G (transpose G))
  (while (not (queue-empty? worklist))
    (define node (dequeue! worklist))
    (define input (for/fold ([state bottom])
            ([pred (in-neighbors trans-G node)])
      (join state (dict-ref live-before-label pred))))
  (define output (transfer node (list input)))
  (cond [(not (equal? output (dict-ref live-before-label node)))
    (dict-set! live-before-label node output)
    (for ([v (in-neighbors G node)])
    (enqueue! worklist v))])))

(define (gen-cfg block-label-list instrs-list)
  (define graph (directed-graph '()))
  (for ([label block-label-list])
    (add-vertex! graph label))
  (for ([label block-label-list] [instrs instrs-list])
    (for ([instr instrs])
      (match instr
        [(Jmp label^) #:when(not (equal? label^ 'conclusion)) (add-directed-edge! graph label label^)]
        [(JmpIf _ label^) #:when(not (equal? label^ 'conclusion))(add-directed-edge! graph label label^)]
        [_ (void)])))
  graph)

(define (temp lst1 lst2)
  (cond
    [(or (empty? lst1) (empty? lst2)) '()]
    [else
     (filter (lambda (x) (not (equal? (first x) (last x))))
             (for*/list ([x (set->list lst1)] [y (set->list lst2)])
               (list x y)))]))

(define (decompose a)
  (match a
    [(Reg b) b]
    [(Var b) b]
    [(Deref b c) b]
    [(Global b) b]
    [(Imm b) '()]
    [(ByteReg b) (decomp-bytereg b)]
    [_ a]))

(define (collect-edges-live-after live-after locals-types)
  (foldr (lambda (var prev)
           (cond
             [(set-member? (set-union callee-saved caller-saved) var)(append (temp (set (decompose var)) caller-saved) prev)]
             [else 
              (match (dict-ref locals-types var)
                [`(Vector ,a ...)
                 (append (temp (set (decompose var)) (set-union callee-saved caller-saved)) prev)]
                [else (append (temp (set (decompose var)) caller-saved) prev)])]))
         '()
         (set->list live-after)))


(define (build-interference-block instrs live-after-list locals-types)
  (define edge-list '())
  (for ([instr instrs] [live-after live-after-list])
    (match instr
      [(Instr 'movq (list arg1 arg2))
       (set! edge-list
             (append (temp (set (decompose arg2)) (set-subtract live-after (set (decompose arg1))))
                     edge-list))]
      [(Instr 'movzbq (list arg1 arg2))
       (set! edge-list
             (append (temp (set (decompose arg2)) (set-subtract live-after (set (decompose arg1))))
                     edge-list))]
      [(Callq 'collect _) (set! edge-list (append (collect-edges-live-after live-after locals-types) edge-list))]
      [(IndirectCallq arg int) (set! edge-list (append (collect-edges-live-after live-after locals-types) edge-list))]
      [_ (set! edge-list (append (temp (locations-write-by-instr instr) live-after) edge-list))]))
  edge-list)


(define (build-graph block-info-list instrs-list locals-types)
  (define graph (undirected-graph '()))
  (for/list ([block-info block-info-list] [instrs instrs-list])
    (for ([edge (build-interference-block instrs (dict-ref block-info 'live-after) locals-types)])
      (add-edge! graph (first edge) (last edge))))
  graph)
(define (build-interference-def def)
  (match def
    [(Def f param type info dict-label-block-temp) 
     (define dict-label-block (make-hash dict-label-block-temp))
     (let ([label-list (hash-keys dict-label-block)] [block-list (hash-values dict-label-block)])
		(match block-list
		  [(list (Block block-info-list instrs-list)...)
			 (Def f param type (dict-set info 'conflicts (build-graph block-info-list instrs-list (dict-ref info 'locals-types)))
						 (for/list ([label label-list] [block-info block-info-list] [instrs instrs-list])
						   (cons label (Block block-info instrs))))
		   ]))]))

(define (build-interference p)
  (match p
	[(X86ProgramDefs info defs) (X86ProgramDefs info (map build-interference-def defs))]))

(define (calc-offset num)
  (- (* (- num 6) 8)))

(define stack-spills 0)
(define root-stack-spills 0)
(define root-stack-assignment (make-hash))
(define stack-assignment (make-hash))

(define (allocate-reg reg color locals-types)
  (match reg
    [(Var a)
     (let ([num (dict-ref color a)])
       (if (>= num 11)
           (match (dict-ref locals-types a)
             ;;;  ['(Vector ,a ...) (Deref 'r15 (- (calc-offset num)))]
             ;;;  [_ (Deref 'rbp (calc-offset num))])
             [`(Vector ,a^ ...)
              (let ([root-offset (cond
                                   [(not (dict-has-key? root-stack-assignment a))
                                    (set! root-stack-spills (+ 1 root-stack-spills))
                                    (dict-set! root-stack-assignment a (- root-stack-spills 1))
                                    (dict-ref root-stack-assignment a)]
                                   [else (dict-ref root-stack-assignment a)])])
                ; (print "Assigning root stack offset: ") (print a) (print " ") (println root-offset)
                (Deref 'r15 (* 8 root-offset)))]
             [_
              (let ([stack-offset (cond
                                    [(not (dict-has-key? stack-assignment a))
                                     (set! stack-spills (+ 1 stack-spills))
                                     (dict-set! stack-assignment a (- stack-spills))
                                     (dict-ref stack-assignment a)]
                                    [else (dict-ref stack-assignment a)])])
                ; (print "Assigning stack offset: ") (print a) (print " ") (println stack-offset)
                (Deref 'rbp (* 8 stack-offset)))])
           (Reg (color->register (dict-ref color a)))))]
    [_ reg]))




(define (allocate-instr instr color locals-types)
  (match instr
    [(TailJmp name num) (TailJmp (allocate-reg name color locals-types) num)]
    [(IndirectCallq name num) (IndirectCallq (allocate-reg name color locals-types) num)]
    [(Instr name arg*)
     (Instr name
            (for/list ([a arg*])
              (allocate-reg a color locals-types)))]
    [_ instr]))

(define (allocate-block instrs color locals-types)
  (for/list ([instr instrs])
    (allocate-instr instr color locals-types)))

(define (allocate-def def)
  (match def
	[(Def f param type info (list (cons label-list (Block block-info-list instrs-list)) ...)) 
     (define-values (color callee-used)
       (graph-coloring (dict-ref info 'conflicts) (dict-ref info 'locals-types)))
      ;;;  (println color)
       (let ([new-blocks
              (for/list ([label label-list] [block-info block-info-list] [instrs instrs-list])
                (cons label
                      (Block block-info (allocate-block instrs color (dict-ref info 'locals-types)))))])
         (Def f param type (dict-set (dict-set (dict-set info 'callee-used (set->list callee-used))
                                         'stack-space
                                         (* 8 stack-spills))
                               'root-stack-space
                               (* 8 root-stack-spills))
                     new-blocks))]))

(define (allocate-registers p)
  (match p
    [(X86ProgramDefs info defs) (X86ProgramDefs info (map allocate-def defs))]))


(define (max-color ls)
  (foldl (lambda (a b) (max (cdr a) b)) 0 ls))

(define (graph-coloring graph var-list)
  (define color (make-hash))
  (define pq-handle (make-hash))
  (define used (make-hash))
  (define callee-used (mutable-set))
  (define pq
    (make-pqueue (lambda (a b) (>= (set-count (hash-ref used a)) (set-count (hash-ref used b))))))
  (define (find-color st c)
    (if (set-member? st c) (find-color st (+ c 1)) c))
  (for ([v var-list])
    (let ([var (car v)])
      (add-vertex! graph var)
      (hash-set! used var (set))
      (for ([n (get-neighbors graph var)])
        (cond
          [(set-member? registers n)
           (hash-set! used var (set-add (hash-ref used var) (register->color n)))]))
      (hash-set! pq-handle var (pqueue-push! pq var))))

  (while (> (pqueue-count pq) 0)
         (let ([c (pqueue-pop! pq)])
           (hash-set! color c (find-color (hash-ref used c) 0))

           (let ([num (hash-ref color c)])
             (cond
               [(and (<= num 10) (>= num 7)) (set-add! callee-used num)]))

           (for ([u (get-neighbors graph c)])
             (cond
               [(not (set-member? registers u))
                (hash-set! used u (set-add (hash-ref used u) (hash-ref color c)))
                (pqueue-decrease-key! pq (hash-ref pq-handle u))]))))
  (values (hash->list color) callee-used))
;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"

(define compiler-passes
  ;; Uncomment the following passes as you finish them.
  `(
    ("shrink" ,shrink ,interp-Lfun,type-check-Lfun)
    ("uniquify" ,uniquify ,interp-Lfun, type-check-Lfun)
    ("reveal functions" ,reveal-functions,interp-Lfun-prime, type-check-Lfun)
    ("limit functions", limit-functions, interp-Lfun-prime, type-check-Lfun-has-type)
    ("expose-allocation" ,expose-allocation ,interp-Lfun-prime, type-check-Lfun)
    ("uncover-get!" ,uncover-get!,interp-Lfun-prime, type-check-Lfun)
    ("remove complex opera*" ,remove-complex-opera* ,interp-Lfun-prime,type-check-Lfun)
    ("explicate control" ,explicate-control ,interp-Cfun,type-check-Cfun)
    ("instruction selection" ,select-instructions ,interp-pseudo-x86-3)
    ("uncover live" ,uncover-live ,interp-pseudo-x86-3)
    ("build interference" ,build-interference ,interp-pseudo-x86-3)
    ("allocate registers", allocate-registers ,interp-x86-3)
    ("patch instructions" ,patch-instructions ,interp-x86-3)
    ("prelude-and-conclusion" ,prelude-and-conclusion ,#f)
    ))




