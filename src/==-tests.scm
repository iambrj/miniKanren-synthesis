(load "./constraintless-mini-in-mini.scm")
(load "./test-check.scm")

(test "1"
      (run* (q) (eval-programo '(run* (z) (== 5 z)) q))
      '((5)))

(test "2"
  (run* (out) (eval-programo '(run* (q)
                                    (conde
                                      [(== 5 q)]
                                      [(== 6 q)]))
                             out))
  '((5 6)))

(test "3"
  (run* (out) (eval-programo '(run* (q)
                                    (fresh (a d)
                                      (== 3 a)
                                      (== 5 d)
                                      (== (cons a d) q)))
                              out))
      '(((3 . 5))))

(define appendo
  (lambda (l s out)
    (conde
      [(== '() l) (== s out)]
      [(fresh (a d res)
         (== (cons a d) l)
         (== (cons a res) out)
         (appendo d s res))])))

(test "4"
  (run* (out) (eval-programo '(run* (q)
                                (letrec-rel ([appendo (l s out)
                                               (conde
                                                 [(== '() l) (== s out)]
                                                 [(fresh (a d res)
                                                    (== (cons a d) l)
                                                    (== (cons a res) out)
                                                    (appendo d s res))])])
                                  (appendo '(a b c) '(d e) q)))
                           out))
  '(((a b c d e))))

(test "5"
  (run* (out) (eval-programo '(run* (q)
                                (letrec-rel ([appendo (l s out)
                                               (conde
                                                 [(== '() l) (== s out)]
                                                 [(fresh (a d res)
                                                    (== (cons a d) l)
                                                    (== (cons a res) out)
                                                    (appendo d s res))])])
                                  (appendo q '(d e) '(a b c d e))))
                           out))
  '(((a b c))))

(test "6"
  (run* (out) (eval-programo '(run* (q)
                                (letrec-rel ([appendo (l s out)
                                               (conde
                                                 [(== '() l) (== s out)]
                                                 [(fresh (a d res)
                                                    (== (cons a d) l)
                                                    (== (cons a res) out)
                                                    (appendo d s res))])])
                                  (appendo '(a b c) q '(a b c d e))))
                           out))
  '(((d e))))

(test "7"
  (run* (out) (eval-programo '(run (((((()))))) (q)
                                (letrec-rel ([appendo (l s out)
                                               (conde
                                                 [(== '() l) (== s out)]
                                                 [(fresh (a d res)
                                                    (== (cons a d) l)
                                                    (== (cons a res) out)
                                                    (delay (appendo d s res)))])])
                                  (fresh (l s out)    
                                    (== (cons l (cons s (cons out '()))) q)
                                    (appendo l s out))))
                           out))
  '(((() (_.) (_.))
     (((_.)) (_. ()) ((_.) _. ()))
     (((_.) (_. ())) (_. (())) ((_.) (_. ()) _. (())))
     (((_.) (_. ()) (_. (()))) (_. ((()))) ((_.) (_. ()) (_. (())) _. ((()))))
     (((_.) (_. ()) (_. (())) (_. ((())))) (_. (((())))) ((_.) (_. ()) (_. (())) (_. ((()))) _. (((()))))))))
