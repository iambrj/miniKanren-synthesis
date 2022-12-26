#|
Syntax

<mk-program> ::= (run* <logic variable> <goal expr>)
               | (run <peano> <logic variable> <goal expr>)

<goal expr> ::= (conde <goal expr>+)
              | (fresh (<logic-var>*) <goal expr>+)
              | (== <term expr> <term expr>)
              | (letrec-rel ((<lexical var> (<lexical var>*) <goal expr>))
                            <goal expr>)
              | (apply-rel <lexical var> <term expr>*)
              | (delay <goal expr>)

<term expr> ::= (quote <datum>) |
                <lexical variable> |
                <logic variable> |
                (cons <term expr> <term expr>)

<datum> ::= <number> |
            <boolean> |
            <symbol> (not the var tag) |
            ()

<peano> ::= () |
            (<peano>)

<lexical variable> ::= <symbol>

<logic variable> ::= (var . <peano>)

<number> ::= [0-9]+

<boolean> ::= #f |
              #t
|#

(load "../../faster-minikanren/mk-vicare.scm")
(load "../../faster-minikanren/mk.scm")

(define empty-s '())
(define peano-zero '())
(define init-env '())

(define (peano n)
  (if (zero? n) '() `(,(peano (- n 1)))))

(define (peanoo p)
  (conde
    [(== '() p)]
    [(fresh (p1)
       (== `(,p1) p)
       (peanoo p1))]))

(define (var?o x)
  (fresh (val)
    (== `(var . ,val) x)
    (peanoo val)))

(define (var=?o x y)
  (fresh (val)
    (== `(var . ,val) x)
    (== `(var . ,val) y)
    (peanoo val)))

(define (var=/=o x y)
  (fresh (val1 val2)
    (== `(var . ,val1) x)
    (== `(var . ,val2) y)
    (=/= val1 val2)
    (peanoo val1)
    (peanoo val2)))

(define (booleano b)
  (conde
    [(== #t b)]
    [(== #f b)]))

(define (walko u s v)
  (conde
    [(== u v)
     (conde
       [(== '() u)]
       [(symbolo u)]
       [(numbero u)]
       [(booleano u)]
       [(fresh (a d)
          (== `(,a . ,d) u)
          (=/= a 'var))])]
    [(var?o u)
     (conde
       [(== u v) (not-assp-subo u s)]
       [(fresh (pr-d)
          (assp-subo u s `(,u . ,pr-d))
          (walko pr-d s v))])]))

(define (occurso x v-unwalked s occurs?)
  (fresh (v)
    (walko v-unwalked s v)
    (conde
      [(== '() v) (== #f occurs?)]
      [(symbolo v) (== #f occurs?)]
      [(numbero v) (== #f occurs?)]
      [(booleano v) (== #f occurs?)]
      [(var?o v) (var=?o x v) (== #t occurs?)]
      [(fresh (av dv occurs-av? occurs-dv?)
         (== `(,av . ,dv) v)
         (=/= 'var av)
         (occurso x av s occurs-av?)
         (occurso x dv s occurs-dv?)
         (conde
           [(== #f occurs-av?) (== #f occurs-dv?) (== #f occurs?)]
           [(== #f occurs-av?) (== #t occurs-dv?) (== #t occurs?)]
           [(== #t occurs-av?) (== #f occurs-dv?) (== #t occurs?)]
           [(== #t occurs-av?) (== #t occurs-dv?) (== #t occurs?)]))])))

(define (assp-subo v s out)
  (fresh (h t h-a h-d)
    (== `(,h . ,t) s)
    (== `(,h-a . ,h-d) h)
    (var?o v)
    (var?o h-a)
    (conde
      [(== h-a v) (== h out)]
      [(=/= h-a v) (assp-subo v t out)])))

(define (not-assp-subo v s)
  (fresh ()
    (var?o v)
    (conde
      [(== '() s)]
      [(fresh (t h-a h-d)
         (== `((,h-a . ,h-d) . ,t) s)
         (=/= h-a v)
         (var?o h-a)
         (not-assp-subo v t))])))

(define (ext-so u v s s1)
  (== `((,u . ,v) . ,s) s1))

#;(define (ext-so u v s s1)
  (fresh (occurs?)
    (occurso u v s occurs?)
    (conde
      [(== #t occurs?) (== #f s1)]
      [(== #f occurs?) (== `((,u . ,v) . ,s) s1)])))

; u, v <- {logic var, number, symbol, boolean, empty list, non-empty list}
; Total 36 + 5 (term types match, but term values do not) = 41 cases
(define (unifyo u-unwalked v-unwalked s s1)
  (fresh (u v)
    (walko u-unwalked s u)
    (walko v-unwalked s v)
    (conde
      [(== s s1) (var=?o u v)]
      [(var?o u) (var?o v) (ext-so u v s s1) (var=/=o u v)]
      [(== '() v) (ext-so u v s s1) (var?o u)]
      [(booleano v) (var?o u) (ext-so u v s s1)]
      [(numbero v) (var?o u) (ext-so u v s s1)]
      [(symbolo v) (var?o u) (ext-so u v s s1)]
      [(var?o u)
       (fresh (a d)
         (== `(,a . ,d) v)
         (=/= 'var a))
       (ext-so u v s s1)]
      [(numbero u) (var?o v) (ext-so v u s s1)]
      [(== s s1) (== u v) (numbero u) (numbero v)]
      [(== #f s1) (=/= u v) (numbero u) (numbero v)]
      [(== #f s1) (== '() v) (numbero u)]
      [(== #f s1) (numbero u) (symbolo v)]
      [(== #f s1) (numbero u) (booleano v)]
      [(== #f s1)
       (numbero u)
       (fresh (a d)
         (== `(,a . ,d) v)
         (=/= 'var a))]
      [(symbolo u) (var?o v) (ext-so v u s s1)]
      [(== #f s1) (symbolo u) (numbero v)]
      [(== s s1) (== u v) (symbolo u) (symbolo v)]
      [(== #f s1) (=/= u v) (symbolo u) (symbolo v)]
      [(== #f s1) (== '() v) (symbolo u)]
      [(== #f s1) (symbolo u) (booleano v)]
      [(== #f s1)
       (symbolo u)
       (fresh (a d)
         (== `(,a . ,d) v)
         (=/= 'var a))]
      [(booleano u) (var?o v) (ext-so v u s s1)]
      [(== #f s1) (== '() v) (booleano u)]
      [(== #f s1) (booleano u) (numbero v)]
      [(== #f s1) (booleano u) (symbolo v)]
      [(== s s1) (== u v) (booleano u) (booleano v)]
      [(== #f s1) (=/= u v) (booleano u) (booleano v)]
      [(== #f s1)
       (booleano u)
       (fresh (a d)
         (== `(,a . ,d) v)
         (=/= 'var a))]
      [(== '() u) (var?o v) (ext-so v u s s1)]
      [(== '() u) (numbero v) (== #f s1)]
      [(== '() u) (symbolo v) (== #f s1)]
      [(== '() u) (booleano v) (== #f s1)]
      [(== '() u) (== '() v) (== s s1)]
      [(== #f s1)
       (== '() u)
       (fresh (a d)
         (== `(,a . ,d) v)
         (=/= 'var a))]
      [(var?o v)
       (fresh (a d)
         (== `(,a . ,d) u)
         (=/= 'var a))
       (ext-so v u s s1)]
      [(== #f s1)
       (numbero v)
       (fresh (a d)
         (== `(,a . ,d) u)
         (=/= 'var a))]
      [(== #f s1)
       (symbolo v)
       (fresh (a d)
         (== `(,a . ,d) u)
         (=/= 'var a))]
      [(== #f s1)
       (booleano v)
       (fresh (a d)
         (== `(,a . ,d) u)
         (=/= 'var a))]
      [(== #f s1)
       (== '() v)
       (fresh (a d)
         (== `(,a . ,d) u)
         (=/= 'var a))]
      [(fresh (u-a u-d v-a v-d s-a)
         (== `(,u-a . ,u-d) u)
         (== `(,v-a . ,v-d) v)
         (=/= 'var u-a)
         (=/= 'var v-a)
         (conde
           [(== s-a #f) (== #f s1) (unifyo u-a v-a s s-a)]
           [(=/= s-a #f)
            (unifyo u-a v-a s s-a)
            (unifyo u-d v-d s-a s1)]))])))

(define (evalo-gexpr expr s/c env $)
  (conde
    [(fresh (ge)
       (== `(delay ,ge) expr)
       ; Maturation happens when pulling
       (== `(delayed eval ,ge ,s/c ,env) $))]
    [(fresh (te1 te2 v1 v2 s c s1)
       (== `(== ,te1 ,te2) expr)
       (== `(,s . ,c) s/c)
       (evalo-texpr te1 env v1)
       (evalo-texpr te2 env v2)
       (conde
         [(== '() $) (== #f s1)]
         [(== `((,s1 . ,c)) $) (=/= #f s1)])
       (unifyo v1 v2 s s1))]
    [(fresh (x* ge+)
       (== `(fresh ,x* . ,ge+) expr)
       (=/= '() ge+)
       (evalo-fresh x* ge+ s/c env $))]
    [(fresh (ge+)
       (== `(conde . ,ge+) expr)
       (=/= '() ge+)
       (evalo-conde ge+ s/c env $))]
    [(fresh (b* c* ge+ renv)
       (== `(letrec-rel ,b* . ,ge+) expr)
       (ext-reco b* '() env renv)
       (evalo-conjn ge+ s/c renv $))]
    [(fresh (id args params ge+ env1 ext-env vargs)
       (== `(apply-rel ,id . ,args) expr)
       (lookupo id env `(closr ,params ,env1 . ,ge+))
       (evalo-args args env vargs)
       (exto params vargs env1 ext-env)
       (evalo-conjn ge+ s/c ext-env $))]))

(define (evalo-texpr expr env val)
  (conde
    [(== expr val)
     (conde
       [(== '() expr)]
       [(booleano expr)]
       [(numbero expr)])]
    [(== `(quote ,val) expr)
     (conde
       [(== '() val)]
       [(fresh (a d)
          (== `(,a . ,d) val))]
       [(booleano val)]
       [(numbero val)]
       [(symbolo val)])
     (not-in-envo 'quote env)
     (absento 'var val)
     (absento 'closr val)]
    [(symbolo expr)
     (lookupo expr env val)]
    [(fresh (e1 e2 v1 v2)
       (== `(cons ,e1 ,e2) expr)
       (== `(,v1 . ,v2) val)
       (not-in-envo 'cons env)
       (evalo-texpr e1 env v1)
       (evalo-texpr e2 env v2))]))

; [[GoalExpr]] -> State -> Env -> Stream State
(define (evalo-conde conjn-ge* st env $)
  (conde
    [(== '() conjn-ge*) (== '() $)]
    [(fresh (conjn-ge-a conjn-ge-d $-a $-d)
       (== `(,conjn-ge-a . ,conjn-ge-d) conjn-ge*)
       (evalo-conjn conjn-ge-a st env $-a)
       (evalo-conde conjn-ge-d st env $-d)
       (mpluso $-a $-d $))]))

; [GoalExpr] -> State -> Env -> Stream State
; Fails silently if ge+ is empty
(define (evalo-conjn ge+ st env $)
  (fresh (ge-a ge-d ge-a-$)
    (== `(,ge-a . ,ge-d) ge+)
    ; Loops on forward run if order changed
    (evalo-gexpr ge-a st env ge-a-$)
    (conde
      [(== '() ge-d)
       (== ge-a-$ $)]
      [(=/= '() ge-d)
       (fresh (ge-d-gexpr)
         (== `(fresh () . ,ge-d) ge-d-gexpr)
         (bindo ge-a-$ ge-d-gexpr env $))])))

; [Var] -> [GoalExpr] -> State -> Env -> Stream State
(define (evalo-fresh x* ge+ st env $)
  (conde
    [(== '() x*)
     (evalo-conjn ge+ st env $)]
    [(fresh (x-a x-d s c env1)
       (== `(,x-a . ,x-d) x*)
       (== `(,s . ,c) st)
       (exto `(,x-a) `((var . ,c)) env env1)
       (evalo-fresh x-d ge+ `(,s . (,c)) env1 $))]))

; Stream ($) := () ; empty stream
;             | (state . $) ; mature stream
;             | (delayed action ...) ; immature stream
;
; Maturation of immature streams happens in pullo
;
; action := eval
;         | mplus
;         | bind
(define (mpluso $1 $2 $)
  (conde
    [(== '() $1) (== $2 $)]
    [(fresh ($1-a $1-d $1-d-$2)
       (== `(,$1-a . ,$1-d) $1)
       (== `(,$1-a . ,$1-d-$2) $)
       (=/= 'delayed $1-a)
       (mpluso $1-d $2 $1-d-$2))]
    [(fresh (d)
       (== `(delayed . ,d) $1)
       (== `(delayed mplus ,$1 ,$2) $))]))

(define (bindo $ ge env $1)
  (conde
    [(== '() $) (== mzero $1)]
    [(fresh ($1-a $1-d v-a v-d)
       (== `(,$1-a . ,$1-d) $)
       (=/= 'delayed $1-a)
       (evalo-gexpr ge $1-a env v-a)
       (bindo $1-d ge env v-d)
       (mpluso v-a v-d $1))]
    [(fresh (d)
       (== `(delayed . ,d) $)
       (== `(delayed bind ,$ ,ge ,env) $1))]))

(define mzero '())

(define (exto params args env env1)
  (conde
    [(== params '())
     (== args '())
     (== env env1)]
    [(fresh (x-a x-d v-a v-d)
       (== `(,x-a . ,x-d) params)
       (== `(,v-a . ,v-d) args)
       (exto x-d v-d `((,x-a . ,v-a) . ,env) env1))]))

(define (ext-reco b* c* env renv)
  (conde
    [(== '() b*) (== `((rec ,c*) . ,env) renv)]
    [(fresh (id params ge+ c*-d b*-a-c*)
       (=/= '() ge+)
       (== `((,id ,params . ,ge+) . ,c*-d) b*)
       (== `((closr ,id ,params .,ge+) . ,c*) b*-a-c*)
       (ext-reco c*-d b*-a-c* env renv))]))

(define (lookupo x env v)
  (conde
    [(fresh (y u env-d)
       (== `((,y . ,u) . ,env-d) env)
       (=/= y 'rec)
       (conde
         [(== x y) (== v u)]
         [(=/= x y) (lookupo x env-d v)]))]
    [(fresh (c* env-d)
       (== `((rec ,c*) . ,env-d) env)
       (lookup-reco x c* env env-d v))]))

(define (lookup-reco x c* renv env v)
  (conde
    [(== '() c*) (lookupo x env v)]
    [(fresh (id params ge+ c*-d)
       (=/= '() ge+)
       (== `((closr ,id ,params . ,ge+) . ,c*-d) c*)
       (conde
         [(== id x)
          ; NOTE : be careful with punning closr tag
          (== `(closr ,params ,renv . ,ge+) v)]
         [(=/= id x)
          (lookup-reco x c*-d renv env v)]))]))

(define (not-in-envo x env)
  (conde
    [(== '() env)]
    [(fresh (y v env1)
       (== `((,y . ,v) . ,env1) env)
       (=/= x y)
       (not-in-envo x env1))]
    [(fresh (c* env1)
       (== `((rec . ,c*) . ,env1) env)
       (not-in-env-reco x c* env1))]))

(define (not-in-env-reco x c* env)
  (conde
    [(== '() c*) (not-in-envo x env)]
    [(fresh (id params ge+ c*-d)
       (== `((,id ,params . ,ge+) . ,c*-d) c*)
       (=/= id x)
       (=/= '() ge+)
       (not-in-env-reco x c*-d env))]))

(define (evalo-args args env vals)
  (conde
    [(== args '())
     (== vals '())]
    [(fresh (a d va vd)
       (== `(,a . ,d) args)
       (== `(,va . ,vd) vals)
       (evalo-texpr a env va)
       (evalo-args d env vd))]))

(define (evalo-program expr out)
  (conde
    [(fresh (lvar gexpr $ s/c*)
       (symbolo lvar)
       (== `(run* (,lvar) ,gexpr) expr)
       (evalo-gexpr `(fresh (,lvar) ,gexpr) `(,empty-s . ,peano-zero) init-env $)
       (take-allo $ s/c*)
       (reifyo s/c* out))]
    [(fresh (n lvar gexpr $ s/c*)
       (symbolo lvar)
       (== `(run ,n (,lvar) ,gexpr) expr)
       (evalo-gexpr `(fresh (,lvar) ,gexpr) `(,empty-s . ,peano-zero) init-env $)
       (take-no n $ s/c*)
       (reifyo s/c* out))]))

(define (take-allo $ s/c*)
  (fresh ($1)
    (pullo $ $1)
    (conde
      [(== '() $1) (== '() s/c*)]
      [(fresh (a d-s/c* $d)
         (== `(,a . ,$d) $1)
         (== `(,a . ,d-s/c*) s/c*)
         (take-allo $d d-s/c*))])))

(define (take-no n $ s/c*)
  (conde
    [(== '() n) (== '() s/c*)]
    [(=/= '() n)
     (fresh ($1)
       (pullo $ $1)
       (conde
         [(== '() $1) (== '() s/c*)]
         [(fresh (n-1 d-s/c* a d)
            (== `(,a . ,d) $1)
            (== `(,n-1) n)
            (== `(,a . ,d-s/c*) s/c*)
            (take-no n-1 d d-s/c*))]))]))

(define (pullo $ $1)
  (conde
    [(== '() $) (== '() $1)]
    [(fresh (a d)
       (== `(,a . ,d) $)
       (== $ $1)
       (=/= 'delayed a))]
    [(fresh (th $-th)
       (== `(delayed . ,th) $)
       (evalo-thunk $ $-th)
       (pullo $-th $1))]))

(define (evalo-thunk th $)
  (fresh ()
    (conde
    [(fresh (gexpr s/c env)
       (== `(delayed eval ,gexpr ,s/c ,env) th)
       (evalo-gexpr gexpr s/c env $))]
    [(fresh ($1 $2 $1e)
       (== `(delayed mplus ,$1 ,$2) th)
       (evalo-thunk $1 $1e)
       (mpluso $2 $1e $))]
    [(fresh ($1 gexpr env $1e)
       (== `(delayed bind ,$1 ,gexpr ,env) th)
       (evalo-thunk $1 $1e)
       (bindo $1e gexpr env $))])))

(define (reifyo s/c* out)
  (fresh()
    (conde
      [(== '() s/c*) (== '() out)]
      [(fresh (a d va vd)
         (== `(,a . ,d) s/c*)
         (== `(,va . ,vd) out)
         (reify-state/1st-varo a va)
         (reifyo d vd))])))

(define (reify-state/1st-varo s/c out)
  (fresh (s c v reified-S)
    (== `(,s . ,c) s/c)
    (walk*o `(var . ()) s v)
    (build-reify-S v '() reified-S)
    (walk*o v reified-S out)))

(define (build-reify-S v-unwalked s s1)
  (fresh (v)
    (walko v-unwalked s v)
    (conde
      [(var?o v)
       (fresh (len)
         (lengtho s len)
         (== `((,v . (_. . ,len)) . ,s) s1))]
      [(== s s1)
       (conde
         [(numbero v)]
         [(symbolo v)]
         [(booleano v)]
         [(== '() v)])]
      [(fresh (a d sa)
         (=/= 'var a)
         (== `(,a . ,d) v)
         (conde
           [(== '_. a)
            (== s s1)]
           [(=/= '_. a)
            (build-reify-S a s sa)
            (build-reify-S d sa s1)]))])))

(define (lengtho l len)
  (conde
    [(== '() l) (== '() len)]
    [(fresh (a d len-d)
       (== `(,a . ,d) l)
       (== `(,len-d) len)
       (lengtho d len-d))]))

(define (walk*o unwalked-v s u)
  (fresh (v)
    ; XXX : sensitive conjunction order
    (walko unwalked-v s v)
    (conde
      [(== v u)
       (conde
         [(== '() v)]
         [(booleano v)]
         [(numbero v)]
         [(symbolo v)]
         [(var?o v)])]
      [(fresh (a d walk*-a walk*-d)
         (== `(,a . ,d) v)
         (=/= a 'var)
         (conde
           [(== '_. a)
            (== u v)]
           [(=/= '_. a)
            (== `(,walk*-a . ,walk*-d) u)
            (walk*o a s walk*-a)
            (walk*o d s walk*-d)]))])))
