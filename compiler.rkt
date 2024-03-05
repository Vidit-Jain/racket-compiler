#lang racket
(require racket/set
         racket/stream
         graph)
(require racket/fixnum)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Cvar.rkt")
(require "utilities.rkt")
(require "interp.rkt")
(require "multigraph.rkt")
(require "priority_queue.rkt")
(provide (all-defined-out))

(define (uniquify-exp env) ;; TODO: this function currently does nothing. Your code goes here
  (lambda (e)
    (match e
      [(Var x) (Var (dict-ref env x))]
      [(Int n) (Int n)]
      [(Let x e body)
       (let ([sub-env (dict-set env x (gensym x))])
         (Let (dict-ref sub-env x) ((uniquify-exp env) e) ((uniquify-exp sub-env) body)))]
      [(Prim op es)
       (Prim op
             (for/list ([e es])
               ((uniquify-exp env) e)))])))

; uniquify : Lvar -> Lvar
(define (uniquify p)
  (match p
    [(Program info e) (Program info ((uniquify-exp '()) e))]))

(define (remove-complex-opera-exp
         env) ;; TODO: this function currently does nothing. Your code goes here
  (lambda (e)
    (match e
      [(Var x) (Var x)]
      [(Int n) (Int n)]
      [(Let x e body)
       (Let x ((remove-complex-opera-exp env) e) ((remove-complex-opera-exp env) body))]
      [(Prim op es)
       (cond
         [(eq? (length es) 1)
          (if (atm? (first es))
              (Prim op es)
              (let ([x (gensym 'tmp)])
                (Let x ((remove-complex-opera-exp env) (first es)) (Prim op (list (Var x))))))]
         [(eq? (length es) 2)
          (cond
            [(not (atm? (first es)))
             (let ([x (gensym 'tmp)])
               (Let x
                    ((remove-complex-opera-exp env) (first es))
                    ((remove-complex-opera-exp env) (Prim op (cons (Var x) (cdr es))))))]
            [(not (atm? (last es)))
             (let ([x (gensym 'tmp)])
               (Let x
                    ((remove-complex-opera-exp env) (last es))
                    ((remove-complex-opera-exp env) (Prim op (list (car es) (Var x))))))]
            [else (Prim op es)])]
         [else (Prim op es)])])))

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
    [(Return t) (select-stmt (Assign (Reg 'rax) t))]))
(define (select-atm e)
  (match e
    [(Var x) e]
    [(Int x) (Imm x)]))
(define (select-stmt e)
  (match e
    [(Assign x e)
     (if (atm? e)
         (list (Instr 'movq (list (select-atm e) x)))
         (match e
           [(Prim 'read '()) (list (Callq 'read_int 1) (Instr 'movq (list (Reg 'rax) x)))]
           [(Prim '- (list a)) (list (Instr 'movq (list (select-atm a) x)) (Instr 'negq (list x)))]
           [(Prim '+ (list a b))
            (cond
              [(equal? x a) (list (Instr 'addq (list (select-atm b) a)))]
              [(equal? x b) (list (Instr 'addq (list (select-atm a) b)))]
              [(list (Instr 'movq (list (select-atm a) x)) (Instr 'addq (list (select-atm b) x)))])]
           [(Prim '- (list a b))
            (cond
              [(equal? x a) (list (Instr 'subq (list (select-atm b) a)))]
              [(list (Instr 'movq (list (select-atm a) x))
                     (Instr 'subq (list (select-atm b) x)))])]))]))

;; select-instructions : Cvar -> x86var
(define (select-instructions p)
  (match p
    [(CProgram info (list (cons 'start e)))
     (X86Program info (list (cons 'start (Block '() (select-tail e)))))]))

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
    [(Instr name (list (Imm (? big-int? i)) (Deref reg offset)))
     (list (Instr 'movq (list (Imm i) (Reg 'rax))) (Instr name (list (Reg 'rax) (Deref reg offset))))]
    [(Instr name (list (Deref reg offset) (Imm (? big-int? i))))
     (list (Instr 'movq (list (Imm i) (Reg 'rax))) (Instr name (list (Deref reg offset) (Reg 'rax))))]
    [(Instr name (list (Deref reg offset1) (Deref reg offset2)))
     (list (Instr 'movq (list (Deref reg offset1) (Reg 'rax)))
           ;;;    (Instr name (list (Deref reg offset1) (Reg 'rax)))
           (Instr name (list (Reg 'rax) (Deref reg offset2))))]
    [_ (list instr)]))

;; patch-instructions : x86var -> x86int
(define (patch-instructions p)
  (match p
    [(X86Program info (list (cons label (Block block-info instrs))))
     (X86Program info
                 (list (cons label
                             (Block block-info
                                    (foldr (lambda (instr acc) (append (patch-instruction instr) acc))
                                           '()
                                           instrs)))))]))

;(error "TODO: code goes here (patch-instructions)"))

(define (compute-delta a b)
  (define c (+ a b))
  (Imm (match (modulo c 16)
    [0 (- c b)]
    [_ (- (* 16 (+ (quotient c 16) 1)) b)])) )
;; prelude-and-conclusion : x86int -> x86int
(define (prelude-and-conclusion p)
  (match p
    [(X86Program info (list (cons label (Block block-info instrs))))
     (X86Program
      info
      (list (cons label (Block block-info (append instrs (list (Jmp 'conclusion)))))
            (cons 'main
                  (Block '()
                         (append (list (Instr 'pushq (list (Reg 'rbp)))
                               (Instr 'movq (list (Reg 'rsp) (Reg 'rbp))))
                               (for/list ([reg (dict-ref info 'callee-used)])
                                 (Instr 'pushq (list (Reg (color->register reg)))))

                               (list
                               (Instr 'subq (let ([C (length (dict-ref info 'callee-used))] [S (dict-ref info 'stack-space)])
                                              (list (compute-delta C S) (Reg 'rsp))
                                              ))
                               (Jmp label)))))
            (cons 'conclusion
                  (Block '()
                         (cons
                               (Instr 'addq (let ([C (length (dict-ref info 'callee-used))] [S (dict-ref info 'stack-space)])
                                              (list (compute-delta C S) (Reg 'rsp))
                                              ))
                               (append
                               (for/list ([reg (reverse (dict-ref info 'callee-used))])
                                 (Instr 'popq (list (Reg (color->register reg)))))
                               (list (Instr 'popq (list (Reg 'rbp)))
                               (Retq))))))))]))
; (define (locations-appear args)
;   (apply set
;          (filter (lambda (arg)
;                    (match arg
;                      [(Imm i) #f]
;                      [_ #t]))
;                  args)))

;(define (locations-appear args)
;  (apply set
;         (map (lambda (arg)
;                   (match arg
;                     [(Reg a) a]
;                     [(Var a) a]))
;                   (filter (lambda (arg)
;                   (match arg
;                     [(Imm i) #f]
;                     [_ #t]))
;                 args))))
(define (locations-appear args)
        (if (empty? args)
          (set) 
          (match (first args)
            [(Reg a) (set-add (locations-appear (rest args)) a)]
            [(Var a) (set-add (locations-appear (rest args)) a)]
            [(Imm a) (locations-appear (rest args))]
            )
        ))


(define (locations-read-by-instr instr)
  (match instr
    [(Instr 'addq (list arg1 arg2)) (locations-appear (list arg1 arg2))]
    [(Instr 'subq (list arg1 arg2)) (locations-appear (list arg1 arg2))]
    [(Instr 'negq (list arg)) (locations-appear (list arg))]
    [(Instr 'movq (list arg1 arg2)) (locations-appear (list arg1))]
    [(Instr 'pushq (list arg)) (locations-appear (list arg (Reg 'rsp)))]
    [(Instr 'popq (list arg)) (locations-appear (list (Reg 'rsp)))]
    [_ (set)]))

;;; still dont know what to do with jmp, callq, retq

(define (locations-write-by-instr instr)
  (match instr
    [(Instr 'addq (list arg1 arg2)) (locations-appear (list arg2))]
    [(Instr 'subq (list arg1 arg2)) (locations-appear (list arg2))]
    [(Instr 'negq (list arg)) (locations-appear (list arg))]
    [(Instr 'movq (list arg1 arg2)) (locations-appear (list arg2))]
    [(Instr 'pushq (list arg)) (locations-appear (list (Reg 'rsp)))]
    [(Instr 'popq (list arg)) (locations-appear (list arg (Reg 'rsp)))]
    [(Callq name num) (locations-appear (list (Reg 'rax)))]
    [_ (set)]))

(define (uncover-live-instrs instrs init-live-after)
  (foldr (lambda (instr acc)
           (cons (set-union (set-subtract (first acc) (locations-write-by-instr instr))
                            (locations-read-by-instr instr))
                 acc))
         (list init-live-after)
         instrs))

(define (uncover-live p)
  (match p
    [(X86Program info (list (cons label-list (Block info-list instrs-list)) ...))
     (X86Program
      info
      (for/list ([label label-list] [block-info info-list] [instrs instrs-list])
        (cons label
              (Block (dict-set block-info 'live-after (rest (uncover-live-instrs instrs (set))))
                     instrs))))]))

(define (temp lst1 lst2)
  (cond [(or (empty? lst1) (empty? lst2)) '()]
        [else (filter (lambda (x) (not (equal? (first x) (last x)))) (for*/list ([x (set->list lst1)] [y (set->list lst2)])
               (list x y)))]))

(define (decompose a)
  (match a
    [(Reg b) b]
    [(Var b) b]
    [_ a]
    )
  )
(define (build-interference-block instrs live-after-list)
   (foldr (lambda (instr live-after prev)
            (match instr
              [(Instr 'movq (list arg1 arg2)) (append (temp (set (decompose arg2)) (set-subtract live-after (set (decompose arg1)))) prev)]
              [_ (append (temp (locations-write-by-instr instr) live-after) prev)])
          )
          '()
          instrs live-after-list))

(define (build-graph block-info-list instrs-list)
  (define graph (undirected-graph '()))
  (for/list ([block-info block-info-list] [instrs instrs-list])
    (for ([edge (build-interference-block instrs (dict-ref block-info 'live-after))]) 
      (add-edge! graph (first edge) (last edge))))
  graph )

(define (build-interference p)
  (match p
    [(X86Program info (list (cons label-list (Block block-info-list instrs-list)) ...))
     (X86Program
      (dict-set info 'conflicts (build-graph block-info-list instrs-list)) 
      (for/list ([label label-list] [block-info block-info-list] [instrs instrs-list])
        (cons label (Block block-info instrs))))]))
(define (calc-offset num)
  (- (* (- num 6) 8))
  )
(define (allocate-reg reg color)
  (match reg 
    [(Imm a) reg]
    [(Reg a) reg]
    [(Var a) (let ([num (dict-ref color a)])
               (if (>= num 11)
                 (Deref 'rbp (calc-offset num))
                 (Reg (color->register (dict-ref color a)))))]
    )
  )
(define (allocate-instr instr color)
  (match instr
    [(Instr name arg*) (Instr name (for/list ([a arg*]) (allocate-reg a color)))]
    [_ instr]
    ))
(define (allocate-block instrs color)
  (for/list ([instr instrs])
    (allocate-instr instr color)
    ))
(define (allocate-registers p)
  (match p
    [(X86Program info (list (cons label-list (Block block-info-list instrs-list)) ...))
     (define-values (color callee-used)
       (graph-coloring (dict-ref info 'conflicts)(dict-ref info 'locals-types)))
     (X86Program
      (dict-set (dict-set info 'callee-used (set->list callee-used)) 'stack-space (* (max 0 (- (max-color color) 10)) 8))
      (for/list ([label label-list] [block-info block-info-list] [instrs instrs-list])
        (cons label (Block block-info (allocate-block instrs color)))))]))

(define (max-color ls) 
  (foldl (lambda (a b)
           (max (cdr a) b)) 0 ls))

(define (graph-coloring graph var-list)
  (define color (make-hash))  
  (define pq-handle (make-hash))
  (define used (make-hash))
  (define callee-used (mutable-set))
  (define pq (make-pqueue (lambda (a b) (>= (set-count (hash-ref used a)) (set-count (hash-ref used b))))))
  (define (find-color st c)
    (if (set-member? st c)
    (find-color st (+ c 1))
    c))
  (for ([v var-list])
    (let ([var (car v)])
      (add-vertex! graph var)
      (hash-set! used var (set))
      (for ([n (get-neighbors graph var)])
        (cond [(set-member? registers n) (hash-set! used var (set-add (hash-ref used var) (register->color n)))]))
      (hash-set! pq-handle var (pqueue-push! pq var))))

  (while (> (pqueue-count pq) 0)
    (let ([c (pqueue-pop! pq)])
      (hash-set! color c (find-color (hash-ref used c) 0))

      (let ([num (hash-ref color c)])
        (cond [(and (<= num 10) (>= num 7)) (set-add! callee-used num)]))

      (for ([u (get-neighbors graph c)])
        (cond [(not (set-member? registers u))
               (hash-set! used u (set-add (hash-ref used u) (hash-ref color c)))
               (pqueue-decrease-key! pq (hash-ref pq-handle u))
               ]))))
  (values (hash->list color) callee-used)
  )
;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  ;; Uncomment the following passes as you finish them.
  `(("uniquify" ,uniquify ,interp-Lvar ,type-check-Lvar)
    ("remove complex opera*" ,remove-complex-opera* ,interp-Lvar ,type-check-Lvar)
    ("explicate control" ,explicate-control ,interp-Cvar ,type-check-Cvar)
    ("instruction selection" ,select-instructions ,interp-x86-0)
    ("uncover live" ,uncover-live ,interp-x86-0)
    ("build interference" ,build-interference ,interp-x86-0)
    ("allocate registers", allocate-registers ,interp-x86-0)
    ; ("assign homes" ,assign-homes ,interp-x86-0)
    ("patch instructions" ,patch-instructions ,interp-x86-0)
    ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)))
    
