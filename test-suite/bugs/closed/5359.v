Require Import Coq.nsatz.Nsatz.
Goal False.

  (* the first (succeeding) goal was reached by clearing one hypothesis in the second goal which overflows 6GB of stack space *)
  let sugar := constr:( 0%Z ) in
  let nparams := constr:( (-1)%Z ) in
  let reified_goal := constr:(
  (Ring_polynom.PEsub (Ring_polynom.PEc 1%Z)
     (Ring_polynom.PEmul
        (Ring_polynom.PEmul
           (Ring_polynom.PEmul
              (Ring_polynom.PEmul (Ring_polynom.PEX Z 4) (Ring_polynom.PEX Z 2))
              (Ring_polynom.PEX Z 5)) (Ring_polynom.PEX Z 3)) 
        (Ring_polynom.PEX Z 6))) ) in
  let power := constr:( N.one ) in
  let reified_givens := constr:(
  (Ring_polynom.PEmul
     (Ring_polynom.PEadd (Ring_polynom.PEc 1%Z)
        (Ring_polynom.PEmul
           (Ring_polynom.PEmul
              (Ring_polynom.PEmul
                 (Ring_polynom.PEmul (Ring_polynom.PEX Z 4) (Ring_polynom.PEX Z 2))
                 (Ring_polynom.PEX Z 5)) (Ring_polynom.PEX Z 3))
           (Ring_polynom.PEX Z 6)))
     (Ring_polynom.PEsub (Ring_polynom.PEc 1%Z)
        (Ring_polynom.PEmul
           (Ring_polynom.PEmul
              (Ring_polynom.PEmul
                 (Ring_polynom.PEmul (Ring_polynom.PEX Z 4) (Ring_polynom.PEX Z 2))
                 (Ring_polynom.PEX Z 5)) (Ring_polynom.PEX Z 3))
           (Ring_polynom.PEX Z 6)))
   :: Ring_polynom.PEsub
        (Ring_polynom.PEmul
           (Ring_polynom.PEadd (Ring_polynom.PEc 1%Z)
              (Ring_polynom.PEmul
                 (Ring_polynom.PEmul
                    (Ring_polynom.PEmul
                       (Ring_polynom.PEmul (Ring_polynom.PEX Z 4)
                          (Ring_polynom.PEX Z 2)) (Ring_polynom.PEX Z 5))
                    (Ring_polynom.PEX Z 3)) (Ring_polynom.PEX Z 6)))
           (Ring_polynom.PEX Z 10)) (Ring_polynom.PEc 1%Z)
      :: Ring_polynom.PEsub
           (Ring_polynom.PEmul
              (Ring_polynom.PEsub (Ring_polynom.PEc 1%Z)
                 (Ring_polynom.PEmul
                    (Ring_polynom.PEmul
                       (Ring_polynom.PEmul
                          (Ring_polynom.PEmul (Ring_polynom.PEX Z 4)
                             (Ring_polynom.PEX Z 2)) (Ring_polynom.PEX Z 5))
                       (Ring_polynom.PEX Z 3)) (Ring_polynom.PEX Z 6)))
              (Ring_polynom.PEX Z 9)) (Ring_polynom.PEc 1%Z)
         :: Ring_polynom.PEsub
              (Ring_polynom.PEadd
                 (Ring_polynom.PEmul (Ring_polynom.PEX Z 1)
                    (Ring_polynom.PEmul (Ring_polynom.PEX Z 7)
                       (Ring_polynom.PEX Z 7)))
                 (Ring_polynom.PEmul (Ring_polynom.PEX Z 8) (Ring_polynom.PEX Z 8)))
              (Ring_polynom.PEadd (Ring_polynom.PEc 1%Z)
                 (Ring_polynom.PEmul
                    (Ring_polynom.PEmul (Ring_polynom.PEX Z 4)
                       (Ring_polynom.PEmul (Ring_polynom.PEX Z 7)
                          (Ring_polynom.PEX Z 7)))
                    (Ring_polynom.PEmul (Ring_polynom.PEX Z 8)
                       (Ring_polynom.PEX Z 8))))
            :: Ring_polynom.PEsub
                 (Ring_polynom.PEadd
                    (Ring_polynom.PEmul (Ring_polynom.PEX Z 1)
                       (Ring_polynom.PEmul (Ring_polynom.PEX Z 5)
                          (Ring_polynom.PEX Z 5)))
                    (Ring_polynom.PEmul (Ring_polynom.PEX Z 6)
                       (Ring_polynom.PEX Z 6)))
                 (Ring_polynom.PEadd (Ring_polynom.PEc 1%Z)
                    (Ring_polynom.PEmul
                       (Ring_polynom.PEmul (Ring_polynom.PEX Z 4)
                          (Ring_polynom.PEmul (Ring_polynom.PEX Z 5)
                             (Ring_polynom.PEX Z 5)))
                       (Ring_polynom.PEmul (Ring_polynom.PEX Z 6)
                          (Ring_polynom.PEX Z 6))))
               :: Ring_polynom.PEsub
                    (Ring_polynom.PEadd
                       (Ring_polynom.PEmul (Ring_polynom.PEX Z 1)
                          (Ring_polynom.PEmul (Ring_polynom.PEX Z 2)
                             (Ring_polynom.PEX Z 2)))
                       (Ring_polynom.PEmul (Ring_polynom.PEX Z 3)
                          (Ring_polynom.PEX Z 3)))
                    (Ring_polynom.PEadd (Ring_polynom.PEc 1%Z)
                       (Ring_polynom.PEmul
                          (Ring_polynom.PEmul (Ring_polynom.PEX Z 4)
                             (Ring_polynom.PEmul (Ring_polynom.PEX Z 2)
                                (Ring_polynom.PEX Z 2)))
                          (Ring_polynom.PEmul (Ring_polynom.PEX Z 3)
                             (Ring_polynom.PEX Z 3)))) :: nil)%list ) in
    Nsatz.nsatz_compute
          (@cons _ (@Ring_polynom.PEc _ sugar) (@cons _ (@Ring_polynom.PEc _ nparams) (@cons _ (@Ring_polynom.PEpow _ reified_goal power) reified_givens))).
  
  let sugar := constr:( 0%Z ) in
  let nparams := constr:( (-1)%Z ) in
  let reified_goal := constr:(
  (Ring_polynom.PEsub (Ring_polynom.PEc 1%Z)
     (Ring_polynom.PEmul
        (Ring_polynom.PEmul
           (Ring_polynom.PEmul
              (Ring_polynom.PEmul (Ring_polynom.PEX Z 4) (Ring_polynom.PEX Z 2))
              (Ring_polynom.PEX Z 5)) (Ring_polynom.PEX Z 3)) 
        (Ring_polynom.PEX Z 6))) ) in
  let power := constr:( N.one ) in
  let reified_givens := constr:(
  (Ring_polynom.PEmul
     (Ring_polynom.PEadd (Ring_polynom.PEc 1%Z)
        (Ring_polynom.PEmul
           (Ring_polynom.PEmul
              (Ring_polynom.PEmul
                 (Ring_polynom.PEmul (Ring_polynom.PEX Z 4) (Ring_polynom.PEX Z 2))
                 (Ring_polynom.PEX Z 5)) (Ring_polynom.PEX Z 3))
           (Ring_polynom.PEX Z 6)))
     (Ring_polynom.PEsub (Ring_polynom.PEc 1%Z)
        (Ring_polynom.PEmul
           (Ring_polynom.PEmul
              (Ring_polynom.PEmul
                 (Ring_polynom.PEmul (Ring_polynom.PEX Z 4) (Ring_polynom.PEX Z 2))
                 (Ring_polynom.PEX Z 5)) (Ring_polynom.PEX Z 3))
           (Ring_polynom.PEX Z 6)))
   :: Ring_polynom.PEadd
        (Ring_polynom.PEmul
           (Ring_polynom.PEadd (Ring_polynom.PEc 1%Z)
              (Ring_polynom.PEmul
                 (Ring_polynom.PEmul
                    (Ring_polynom.PEmul
                       (Ring_polynom.PEmul (Ring_polynom.PEX Z 4)
                          (Ring_polynom.PEX Z 2)) (Ring_polynom.PEX Z 5))
                    (Ring_polynom.PEX Z 3)) (Ring_polynom.PEX Z 6)))
           (Ring_polynom.PEsub (Ring_polynom.PEc 1%Z)
              (Ring_polynom.PEmul
                 (Ring_polynom.PEmul
                    (Ring_polynom.PEmul
                       (Ring_polynom.PEmul (Ring_polynom.PEX Z 4)
                          (Ring_polynom.PEX Z 2)) (Ring_polynom.PEX Z 5))
                    (Ring_polynom.PEX Z 3)) (Ring_polynom.PEX Z 6))))
        (Ring_polynom.PEmul
           (Ring_polynom.PEmul
              (Ring_polynom.PEmul
                 (Ring_polynom.PEmul (Ring_polynom.PEX Z 4)
                    (Ring_polynom.PEadd
                       (Ring_polynom.PEmul (Ring_polynom.PEX Z 2)
                          (Ring_polynom.PEX Z 6))
                       (Ring_polynom.PEmul (Ring_polynom.PEX Z 3)
                          (Ring_polynom.PEX Z 5)))) (Ring_polynom.PEX Z 7))
              (Ring_polynom.PEsub
                 (Ring_polynom.PEmul (Ring_polynom.PEX Z 3) (Ring_polynom.PEX Z 6))
                 (Ring_polynom.PEmul
                    (Ring_polynom.PEmul (Ring_polynom.PEX Z 1)
                       (Ring_polynom.PEX Z 2)) (Ring_polynom.PEX Z 5))))
           (Ring_polynom.PEX Z 8))
      :: Ring_polynom.PEsub
           (Ring_polynom.PEmul
              (Ring_polynom.PEadd (Ring_polynom.PEc 1%Z)
                 (Ring_polynom.PEmul
                    (Ring_polynom.PEmul
                       (Ring_polynom.PEmul
                          (Ring_polynom.PEmul (Ring_polynom.PEX Z 4)
                             (Ring_polynom.PEX Z 2)) (Ring_polynom.PEX Z 5))
                       (Ring_polynom.PEX Z 3)) (Ring_polynom.PEX Z 6)))
              (Ring_polynom.PEX Z 10)) (Ring_polynom.PEc 1%Z)
         :: Ring_polynom.PEsub
              (Ring_polynom.PEmul
                 (Ring_polynom.PEsub (Ring_polynom.PEc 1%Z)
                    (Ring_polynom.PEmul
                       (Ring_polynom.PEmul
                          (Ring_polynom.PEmul
                             (Ring_polynom.PEmul (Ring_polynom.PEX Z 4)
                                (Ring_polynom.PEX Z 2)) 
                             (Ring_polynom.PEX Z 5)) (Ring_polynom.PEX Z 3))
                       (Ring_polynom.PEX Z 6))) (Ring_polynom.PEX Z 9))
              (Ring_polynom.PEc 1%Z)
            :: Ring_polynom.PEsub
                 (Ring_polynom.PEadd
                    (Ring_polynom.PEmul (Ring_polynom.PEX Z 1)
                       (Ring_polynom.PEmul (Ring_polynom.PEX Z 7)
                          (Ring_polynom.PEX Z 7)))
                    (Ring_polynom.PEmul (Ring_polynom.PEX Z 8)
                       (Ring_polynom.PEX Z 8)))
                 (Ring_polynom.PEadd (Ring_polynom.PEc 1%Z)
                    (Ring_polynom.PEmul
                       (Ring_polynom.PEmul (Ring_polynom.PEX Z 4)
                          (Ring_polynom.PEmul (Ring_polynom.PEX Z 7)
                             (Ring_polynom.PEX Z 7)))
                       (Ring_polynom.PEmul (Ring_polynom.PEX Z 8)
                          (Ring_polynom.PEX Z 8))))
               :: Ring_polynom.PEsub
                    (Ring_polynom.PEadd
                       (Ring_polynom.PEmul (Ring_polynom.PEX Z 1)
                          (Ring_polynom.PEmul (Ring_polynom.PEX Z 5)
                             (Ring_polynom.PEX Z 5)))
                       (Ring_polynom.PEmul (Ring_polynom.PEX Z 6)
                          (Ring_polynom.PEX Z 6)))
                    (Ring_polynom.PEadd (Ring_polynom.PEc 1%Z)
                       (Ring_polynom.PEmul
                          (Ring_polynom.PEmul (Ring_polynom.PEX Z 4)
                             (Ring_polynom.PEmul (Ring_polynom.PEX Z 5)
                                (Ring_polynom.PEX Z 5)))
                          (Ring_polynom.PEmul (Ring_polynom.PEX Z 6)
                             (Ring_polynom.PEX Z 6))))
                  :: Ring_polynom.PEsub
                       (Ring_polynom.PEadd
                          (Ring_polynom.PEmul (Ring_polynom.PEX Z 1)
                             (Ring_polynom.PEmul (Ring_polynom.PEX Z 2)
                                (Ring_polynom.PEX Z 2)))
                          (Ring_polynom.PEmul (Ring_polynom.PEX Z 3)
                             (Ring_polynom.PEX Z 3)))
                       (Ring_polynom.PEadd (Ring_polynom.PEc 1%Z)
                          (Ring_polynom.PEmul
                             (Ring_polynom.PEmul (Ring_polynom.PEX Z 4)
                                (Ring_polynom.PEmul (Ring_polynom.PEX Z 2)
                                   (Ring_polynom.PEX Z 2)))
                             (Ring_polynom.PEmul (Ring_polynom.PEX Z 3)
                                (Ring_polynom.PEX Z 3)))) :: nil)%list ) in
    Nsatz.nsatz_compute
          (@cons _ (@Ring_polynom.PEc _ sugar) (@cons _ (@Ring_polynom.PEc _ nparams) (@cons _ (@Ring_polynom.PEpow _ reified_goal power) reified_givens))).
