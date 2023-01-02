(load "./constraintless-mini-in-mini.scm")
(load "test-check.scm")

(define (makevar n) `(var . ,(peano n)))

(define env '((d var (())) (a var ()) (q var)))

(define initS/3 '(() . (((())))))

(printf "Running unit tests...\n")

(define conjn-1 '((== 5 d)))
(define conjn-2 '((== 5 d) (== (cons a d) q)))
(define conjn-3 '((== 3 a) (== 5 d) (== (cons a d) q)))

(test "eval-conjno 1"
      (run 1 ($) (eval-conjno conjn-1 initS/3 env $))
      `(((((,(makevar 2) . 5)) . (((())))))))

(test "eval-conjno 2"
      (run 1 ($) (eval-conjno conjn-2 initS/3 env $))
      `(((((,(makevar 0) . (,(makevar 1) . ,(makevar 2))) (,(makevar 2) . 5))
          . (((())))))))

(test "eval-conjno 3"
      (run 1 ($) (eval-conjno conjn-3 initS/3 env $))
      `(((((,(makevar 0) . (,(makevar 1) . ,(makevar 2)))
           (,(makevar 2) . 5)
           (,(makevar 1) . 3))
          . (((())))))))

(define disjn-1 '(((== 5 d))))
(define disjn-2 '(((== 5 d)) ((== 4 d))))
(define disjn-3 `(((== 5 d))
                  ((== 4 d))
                  ,conjn-3))
(define disjn-4 `(((== 5 d) (== 'cat a) (== (cons a d) q))
                  ((== 'apple d) (== 4 a) (== (cons a d) q))
                  ,conjn-3))

(test "eval-condeo 1"
      (run 1 ($) (eval-condeo disjn-1 initS/3 env $))
      `(((((,(makevar 2) . 5)) . (((())))))))

(test "eval-condeo 2"
      (run 1 ($) (eval-condeo disjn-2 initS/3 env $))
      `(((((,(makevar 2) . 5)) . (((()))))
         (((,(makevar 2) . 4)) . (((())))))))

(test "eval-condeo 3"
      (run 1 ($) (eval-condeo disjn-3 initS/3 env $))
      `(((((,(makevar 2) . 5)) . (((()))))
         (((,(makevar 2) . 4)) . (((()))))
         (((,(makevar 0) . (,(makevar 1) . ,(makevar 2)))
           (,(makevar 2) . 5)
           (,(makevar 1) . 3))
          . (((())))))))

(test "eval-condeo 4"
      (run 1 ($) (eval-condeo disjn-4 initS/3 env $))
      `(((((,(makevar 0) . (,(makevar 1) . ,(makevar 2)))
           (,(makevar 1) . cat)
           (,(makevar 2) . 5)) . (((()))))
         (((,(makevar 0) . (,(makevar 1) . ,(makevar 2)))
           (,(makevar 1) . 4)
           (,(makevar 2) . apple)) . (((()))))
         (((,(makevar 0) . (,(makevar 1) . ,(makevar 2)))
           (,(makevar 2) . 5)
           (,(makevar 1) . 3))
          . (((())))))))

; walko tests
(define S1 `((,(makevar 3) . ,(makevar 1))
             (,(makevar 2) . (,(makevar 1) . ,(makevar 0)))
             (,(makevar 1) . 3)
             (,(makevar 0) . apple)))
; Constants walk to themselves
(test "walko constant 1"
      (run* (v) (walko 'cat S1 v))
      `(cat))

(test "walko constant 2"
      (run* (v) (walko 5 S1 v))
      `(5))

(test "walko constant 3"
      (run* (v) (walko 5 S1 v))
      `(5))

; Fresh variable walks to itself
(test "walko fresh var"
      (run* (v) (walko (makevar 4) S1 v))
      `(,(makevar 4)))

; Nonrecursive variable walk
(test "walko nonrecursive var"
      (run* (v) (walko (makevar 0) S1 v))
      `(apple))

; Recursive variable walk
(test "walko recursive var"
      (run* (v) (walko (makevar 3) S1 v))
      `(3))

; Pairs aren't recursively walked
(test "walko pair"
      (run* (v) (walko (makevar 2) S1 v))
      `((,(makevar 1) . ,(makevar 0))))

; walk*o tests
(define S2 `((,(makevar 4) . ())
             (,(makevar 3) . ,(makevar 1))
             (,(makevar 2) . (,(makevar 1) . ,(makevar 5)))
             (,(makevar 1) . 3)
             (,(makevar 0) . apple)))

; Nonrecursive cases
(test "walk*o nonrecursive empty list"
      (run* (v) (walk*o (makevar 4) S2 v))
      `(()))

(test "walk*o nonrecursive number"
      (run* (v) (walk*o (makevar 1) S2 v))
      `(3))

(test "walk*o nonrecursive symbol"
      (run* (v) (walk*o (makevar 0) S2 v))
      `(apple))

(test "walk*o nonrecursive boolean"
      (run* (v) (walk*o #t S2 v))
      `(#t))

(test "walk*o nonrecursive fresh variable"
      (run* (v) (walk*o (makevar 5) S2 v))
      `(,(makevar 5)))

(test "walk*o recursive pair"
      (run* (v) (walk*o (makevar 2) S2 v))
      `((3 . ,(makevar 5))))

(test "unifyo equal constants 1"
      (run* (S) (unifyo 5 5 S1 S))
      `(,S1))

(test "unifyo equal constants 2"
      (run* (S) (unifyo 'cat 'cat S1 S))
      `(,S1))

(test "unifyo equal constants 3"
      (run* (S) (unifyo #t #t S1 S))
      `(,S1))

(test "unifyo equal constants 4"
      (run* (S) (unifyo '() '() S1 S))
      `(,S1))

(test "unifyo equal constants 5"
      (run* (S) (unifyo '(cat bat) '(cat bat) S1 S))
      `(,S1))

(test "unifyo same type unequal constants 1"
      (run* (S) (unifyo '(cat bat) '(cat cat) S1 S))
      `(#f))

(test "unifyo same type unequal constants 2"
      (run* (S) (unifyo 1 2 S1 S))
      `(#f))

(test "unifyo same type unequal constants 3"
      (run* (S) (unifyo #t #f S1 S))
      `(#f))

(test "unifyo same type unequal constants 4"
      (run* (S) (unifyo 'cat 'bat S1 S))
      `(#f))

(test "unifyo different type unequal constants 1"
      (run* (S) (unifyo 3 #t S1 S))
      `(#f))

(test "unifyo different type unequal constants 2"
      (run* (S) (unifyo 3 'cat S1 S))
      `(#f))

(test "unifyo different type unequal constants 3"
      (run* (S) (unifyo 3 '() S1 S))
      `(#f))

(test "unifyo different type unequal constants 4"
      (run* (S) (unifyo 3 '(cat bat) S1 S))
      `(#f))

(test "unifyo different type unequal constants 5"
      (run* (S) (unifyo #t 'cat S1 S))
      `(#f))

(test "unifyo different type unequal constants 6"
      (run* (S) (unifyo #t '() S1 S))
      `(#f))

(test "unifyo different type unequal constants 7"
      (run* (S) (unifyo #t '(cat bat) S1 S))
      `(#f))

(test "unifyo different type unequal constants 8"
      (run* (S) (unifyo '() '(cat bat) S1 S))
      `(#f))

(test "unifyo fresh variable success"
      (run* (S) (unifyo (makevar 4) '(cat bat) S1 S))
      `(((,(makevar 4) . (cat bat))
         (,(makevar 3) . ,(makevar 1))
         (,(makevar 2) . (,(makevar 1) . ,(makevar 0)))
         (,(makevar 1) . 3)
         (,(makevar 0) . apple))))

(test "unifyo bound variable success"
      (run* (S) (unifyo (makevar 3) 3 S1 S))
      `(,S1))

(test "unifyo bound variable failure"
      (run* (S) (unifyo (makevar 3) 'cat S1 S))
      `(#f))

(test "unifyo bound variable pair success"
      (run* (S) (unifyo (makevar 2) '(3 . apple) S1 S))
      `(,S1))

(test "unifyo bound variable pair failure"
      (run* (S) (unifyo (makevar 2) 5 S1 S))
      `(#f))

(test "unifyo pair success"
      (run* (S) (unifyo `(,(makevar 2) . 5) '((3 . apple) . 5) S1 S))
      `(,S1))

(test "unifyo pair failure"
      (run* (S) (unifyo `(,(makevar 2) . 5) '((3 . banana) . 5) S1 S))
      `(#f))

; mpluso tests
(test "mpluso first argument empty stream"
      (run* ($) (mpluso '() `(,S1) $))
      `((,S1)))

(test "mpluso second argument empty stream"
      (run* ($) (mpluso `(,S1) '() $))
      `((,S1)))

(define env-S1 `((a . ,(makevar 0))
                 (b . ,(makevar 1))
                 (c . ,(makevar 2))
                 (d . ,(makevar 3))
                 (e . ,(makevar 4))))

(define st1 `(,S1 . (((((())))))))

(test "mpluso first argument empty stream"
      (run* ($) (mpluso `() `(delayed eval (== 'apple a) ,st1 ,env-S1) $))
      `((delayed eval (== 'apple a) ,st1 ,env-S1)))

(test "mpluso first argument mature stream"
      (run* ($) (mpluso `(,st1) `(delayed eval (== 'apple a) ,st1 ,env-S1) $))
      `((,st1 . (delayed eval (== 'apple a) ,st1 ,env-S1))))

(test "mpluso first argument (mature delayed) stream"
      (run* ($) (mpluso `(,st1 . (delayed eval (== b d) ,st1 ,env-S1))
                        `(delayed eval (== 'apple a) ,st1 ,env-S1)
                        $))
      `((,st1 . (delayed mplus (delayed eval (== b d) ,st1 ,env-S1)
                        (delayed eval (== 'apple a) ,st1 ,env-S1)))))

(test "mpluso first argument delayed stream"
      (run* ($) (mpluso `(delayed eval (== 'apple a) ,st1 ,env-S1) `(,st1) $))
      `((delayed mplus (delayed eval (== 'apple a) ,st1 ,env-S1) (,st1))))

; bindo tests
(test "bindo first argument empty stream"
      (run* ($) (bindo '() '(== 'apple a) env-S1 $))
      '(()))

(test "bindo first argument mature stream"
      (run* ($) (bindo `(,st1) '(== 'cat e) env-S1 $))
      `(((((,(makevar 4) . cat) . ,S1) . (((((())))))))))

(test "bindo first argument (mature delayed) stream"
      (run* ($) (bindo `(,st1 . (delayed eval (== b d) ,st1 ,env-S1)) '(== 'cat e) env-S1 $))
      `(((((,(makevar 4) . cat) . ,S1) . (((((())))))) .
         (delayed bind (delayed eval (== b d) ,st1 ,env-S1) (== 'cat e) ,env-S1))))

(test "bindo first argument delayed stream"
      (run* ($) (bindo `(delayed eval (== b d) ,st1 ,env-S1) '(== 'cat e) env-S1 $))
      `((delayed bind (delayed eval (== b d) ,st1 ,env-S1) (== 'cat e) ,env-S1)))

; lookupo tests
(test "lookupo nonrecursive env base case"
      (run* (v) (lookupo 'a env-S1 v))
      `(,(makevar 0)))

(test "lookupo nonrecursive env recursive case"
      (run* (v) (lookupo 'c env-S1 v))
      `(,(makevar 2)))

(define eveno-oddo-c*
  `((closr eveno (x) . ((conde [(== '() x)]
                               [(fresh (a d)
                                  (== (cons a d) x)
                                  (apply-rel oddo d))])))
    (closr oddo (x) . ((fresh (a d)
                         (== (cons a d) x)
                         (apply-rel eveno d))))))

(define renv-S1 `((rec ,eveno-oddo-c*) . ,env-S1))

(test "lookupo recursive env closure lookup"
      (run* (v) (lookupo 'eveno renv-S1 v))
      `((closr (x) ,renv-S1 . ((conde [(== '() x)]
                                      [(fresh (a d)
                                         (== (cons a d) x)
                                         (apply-rel oddo d))])))))

; lookup-reco tests
(test "lookup-reco recursive env closure lookup 1"
      (run* (v) (lookup-reco 'eveno eveno-oddo-c* renv-S1 env-S1 v))
      `((closr (x) ,renv-S1 . ((conde [(== '() x)]
                                      [(fresh (a d)
                                         (== (cons a d) x)
                                         (apply-rel oddo d))])))))

(test "lookup-reco recursive env closure lookup 2"
      (run* (v) (lookup-reco 'oddo eveno-oddo-c* renv-S1 env-S1 v))
      `((closr (x) ,renv-S1 . ((fresh (a d)
                                 (== (cons a d) x)
                                 (apply-rel eveno d))))))

(test "lookup-reco recursive env variable lookup"
      (run* (v) (lookup-reco 'c eveno-oddo-c* renv-S1 env-S1 v))
      `(,(makevar 2)))

; eval-texpro tests
(test "eval-texpro number"
      (run* (v) (eval-texpro 5 env-S1 v))
      `(5))

(test "eval-texpro boolean"
      (run* (v) (eval-texpro '#f env-S1 v))
      `(#f))

(test "eval-texpro empty list"
      (run* (v) (eval-texpro '() env-S1 v))
      `(()))

(test "eval-texpro quote number"
      (run* (v) (eval-texpro '(quote 3) env-S1 v))
      `(3))

(test "eval-texpro quote symbol"
      (run* (v) (eval-texpro '(quote cat) env-S1 v))
      `(cat))

(test "eval-texpro quote empty list"
      (run* (v) (eval-texpro '(quote ()) env-S1 v))
      `(()))

(test "eval-texpro quote boolean"
      (run* (v) (eval-texpro '(quote #t) env-S1 v))
      `(#t))

(test "eval-texpro quote bounded to constant in env"
      (run* (v) (eval-texpro '(cons quote 5) `((quote . 5) . ,env-S1) v))
      `((5 . 5)))

(test "eval-texpro closr lookup"
      (run* (v) (eval-texpro 'oddo renv-S1 v))
      `((closr (x) ,renv-S1 . ((fresh (a d)
                                 (== (cons a d) x)
                                 (apply-rel eveno d))))))

(test "eval-texpro variable lookup"
      (run* (v) (eval-texpro 'c renv-S1 v))
      `(,(makevar 2)))

(test "eval-texpro cons pair"
      (run* (v) (eval-texpro '(cons 3 4) renv-S1 v))
      `((3 . 4)))

(test "eval-texpro cons pair"
      (run* (v) (eval-texpro '(cons 3 4) renv-S1 v))
      `((3 . 4)))

(test "eval-texpro cons bound to constant"
      (run* (v) (eval-texpro 'cons `((cons . 5) . ,renv-S1) v))
      `(5))

(test "eval-texpro cons inside cons"
      (run* (v) (eval-texpro '(cons 1 (cons 2 '())) renv-S1 v))
      `((1 2)))

; eval-argso tests
(test "eval-argso"
      (run* (v) (eval-argso '(a 5 (cons b '())) renv-S1 v))
      `((,(makevar 0) 5 (,(makevar 1)))))

; eval-fresho tests
(define S2 `((,(makevar 1) . 3)
             (,(makevar 0) . apple)))
(define st2 `(,S2 . ((()))))
(define renv-S2 `((a . ,(makevar 0))
                  (b . ,(makevar 1))))
(test "eval-fresho"
      (run* ($) (eval-fresho '(c d e) '((== c (cons d e))) st2 renv-S2 $))
      `(((((,(makevar 2) . (,(makevar 3) . ,(makevar 4))) . ,S2) . (((((())))))))))

(define S3 `((,(makevar 3) . ,(makevar 1))
             (,(makevar 2) . (,(makevar 6) . ,(makevar 0)))
             (,(makevar 4) . ())
             (,(makevar 5) . #f)
             (,(makevar 1) . 3)
             (,(makevar 0) . apple)))
; build-reify-S tests
(test "build-reify-S constant number"
      (run* (S) (build-reify-S (makevar 3) S3 S))
      `(,S3))

(test "build-reify-S constant symbol"
      (run* (S) (build-reify-S (makevar 0) S3 S))
      `(,S3))

(test "build-reify-S constant boolean"
      (run* (S) (build-reify-S (makevar 5) S3 S))
      `(,S3))

(test "build-reify-S constant empty list"
      (run* (S) (build-reify-S (makevar 4) S3 S))
      `(,S3))

(test "build-reify-S fresh variable"
      (run* (S) (build-reify-S (makevar 6) S3 S))
      `(((,(makevar 6) . (_. . ,(peano 6))) . ,S3)))

(test "build-reify-S pair"
      (run* (S) (build-reify-S (makevar 2) S3 S))
      `(((,(makevar 6) . (_. . ,(peano 6))) . ,S3)))

; reify-state/1st-varo tests
(define S4 `((,(makevar 3) . ,(makevar 1))
             (,(makevar 0) . (,(makevar 6) . ,(makevar 2)))
             (,(makevar 4) . ())
             (,(makevar 5) . #f)
             (,(makevar 1) . 3)
             (,(makevar 2) . apple)))

(test "reify-state/1st-varo"
      (run* (v) (reify-state/1st-varo `(,S4 . (((((((())))))))) v))
      `(((_. . ,(peano 0)) . apple)))

; reifyo tests
(test "reifyo"
      (run* (ans*) (reifyo `((,S4 . (((((((())))))))) (,S3 . (((((((()))))))))) ans*))
      `((((_. . ,(peano 0)) . apple) apple)))

; eval-gexpro tests
(test "eval-gexpro =="
      (run* ($) (eval-gexpro '(== d 3) st1 env-S1 $))
      `((,st1)))

(test "eval-gexpro fresh 1"
      (run* ($) (eval-gexpro '(fresh (x) (== x c)) st1 env-S1 $))
      `(((((,(makevar 5) . (,(makevar 1) . ,(makevar 0))) . ,S1) . ((((((()))))))))))

(test "eval-gexpro fresh 2"
      (run* ($) (eval-gexpro '(fresh (x y) (== x y)) st1 env-S1 $))
      `(((((,(makevar 5) . ,(makevar 6)) . ,S1) . (((((((())))))))))))

(test "eval-gexpro fresh 2"
      (run* ($) (eval-gexpro '(fresh (x y) (== x y)) st1 env-S1 $))
      `(((((,(makevar 5) . ,(makevar 6)) . ,S1) . (((((((())))))))))))

(test "eval-gexpro conde"
      (run* ($) (eval-gexpro '(conde [(== e 6) (== a 3)]
                                     [(== e 6) (fresh (x) (== x 7))])
                             st1
                             env-S1
                             $))
      `(((((,(makevar 5) . 7) . ((,(makevar 4) . 6) . ,S1)) . ((((((()))))))))))

(test "eval-gexpro apply-rel"
      (run* ($) (eval-gexpro '(apply-rel oddo '(())) st1 renv-S1 $))
      `(((((,(makevar 6) . ()) . ((,(makevar 5) . ()) . ,S1)) . (((((((())))))))))))

(test "eval-gexpro letrec-rel"
      (run* ($) (eval-gexpro '(letrec-rel ((eveno (x) (conde [(== '() x)]
                                                             [(fresh (a d)
                                                                (== (cons a d) x)
                                                                (apply-rel oddo d))]))
                                           (oddo (x) (fresh (a d)
                                                       (== (cons a d) x)
                                                       (apply-rel eveno d))))
                                          (apply-rel oddo '(()))) st1 S1 $))
      `(((((,(makevar 6) . ()) . ((,(makevar 5) . ()) . ,S1)) . (((((((())))))))))))

; TODO: Add occurso tests
; TODO: Add ext-so tests
