(load "./constraintless-mini-in-mini.scm")
(load "test-check.scm")

(define (makevar n) `(var . ,(peano n)))

(define env '((d var (())) (a var ()) (q var)))

(define initS/3 '(() . (((())))))

(printf "Running unit tests...\n")

(define conjn-1 '((== 5 d)))
(define conjn-2 '((== 5 d) (== (cons a d) q)))
(define conjn-3 '((== 3 a) (== 5 d) (== (cons a d) q)))

(test "evalo-conjn 1"
      (run 1 ($) (evalo-conjn conjn-1 initS/3 env $))
      `(((((,(makevar 2) . 5)) . (((())))))))

(test "evalo-conjn 2"
      (run 1 ($) (evalo-conjn conjn-2 initS/3 env $))
      `(((((,(makevar 0) . (,(makevar 1) . ,(makevar 2))) (,(makevar 2) . 5))
          . (((())))))))

(test "evalo-conjn 3"
      (run 1 ($) (evalo-conjn conjn-3 initS/3 env $))
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

(test "evalo-conde 1"
      (run 1 ($) (evalo-conde disjn-1 initS/3 env $))
      `(((((,(makevar 2) . 5)) . (((())))))))

(test "evalo-conde 2"
      (run 1 ($) (evalo-conde disjn-2 initS/3 env $))
      `(((((,(makevar 2) . 5)) . (((()))))
         (((,(makevar 2) . 4)) . (((())))))))

(test "evalo-conde 3"
      (run 1 ($) (evalo-conde disjn-3 initS/3 env $))
      `(((((,(makevar 2) . 5)) . (((()))))
         (((,(makevar 2) . 4)) . (((()))))
         (((,(makevar 0) . (,(makevar 1) . ,(makevar 2)))
           (,(makevar 2) . 5)
           (,(makevar 1) . 3))
          . (((())))))))

(test "evalo-conde 4"
      (run 1 ($) (evalo-conde disjn-4 initS/3 env $))
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

; TODO: Add walk*o tests
; TODO: Add unifyo tests
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

(test "unifyo unequal constants 1"
      (run* (S) (unifyo 3 '() S1 S))
      `(#f))

(test "unifyo unequal constants 2"
      (run* (S) (unifyo 1 2 S1 S))
      `(#f))

(test "unifyo unequal constants 3"
      (run* (S) (unifyo #t #f S1 S))
      `(#f))

(test "unifyo unequal constants 4"
      (run* (S) (unifyo 3 #t S1 S))
      `(#f))

(test "unifyo unequal constants 5"
      (run* (S) (unifyo 3 '() S1 S))
      `(#f))
; TODO: Add evalo-gexpr tests
; TODO: Add evalo-texpr tests
; TODO: Add mpluso tests
; TODO: Add bindo tests
; TODO: Add lookupo tests
; TODO: Add lookupo-reco tests
; TODO: Add evalo-args tests
