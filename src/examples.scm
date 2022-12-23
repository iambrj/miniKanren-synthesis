(load "./constraintless-mini-in-mini.scm")

; Forwards outside, backwards inside!
(run 1 (out) (evalo-program '(run (()) (q)
                               (letrec-rel ((appendo (l1 l2 l)
                                              (conde
                                                [(== '() l1) (== l2 l)]
                                                [(fresh (a d d-l2)
                                                   (== (cons a d) l1)
                                                   (== (cons a d-l2) l)
                                                   (delay (apply-rel appendo d
                                                                     l2 d-l2)))])))
                                           (apply-rel appendo '(1 2 3) q '(1 2 3 4 5))))
                         out))

; Simple synthesis
(run 1 (synth) (evalo-program `(run (()) (q)
                               (letrec-rel ((appendo (l1 l2 l)
                                              (conde
                                                [(== '() l1) (== l2 l)]
                                                [(fresh (a d d-l2)
                                                   (== (cons a d) l1)
                                                   (== (cons a d-l2) l)
                                                   (delay (apply-rel appendo d
                                                                     l2 d-l2)))])))
                                           (apply-rel appendo '(1 2 3) '(4 5) ,synth)))
                         '((1 2 3 4 5))))

; Can synthesize recursive relation calls too!
(run 1 (synth) (evalo-program `(run (()) (q)
                                 (letrec-rel ((appendo (l1 l2 l)
                                                (conde
                                                  [(== '() l1) (== l2 l)]
                                                  [(fresh (a d d-l2)
                                                     (== (cons a d) l1)
                                                     (== (cons a d-l2) l)
                                                     (delay (apply-rel ,synth d
                                                                       l2 d-l2)))])))
                                             (apply-rel appendo '(1 2 3) '(4 5) q)))
                         '((1 2 3 4 5))))
