(* Test about a slowness of f_equal in 8.5pl1 *)

(* Submitted by Jason Gross *)

(* -*- mode: coq; coq-prog-args: ("-R" "src" "Crypto" "-R" "Bedrock" "Bedrock" "-R" "coqprime-8.5/Coqprime" "Coqprime" "-top" "GF255192") -*- *)
(* File reduced by coq-bug-finder from original input, then from 162 lines to 23 lines, then from 245 lines to 95 lines, then from 198 lines to 101 lines, then from 654 lines to 452 lines, then from 591 lines to 505 lines, then from 1770 lines to 580 lines, then from 2238 lines to 1715 lines, then from 1776 lines to 1738 lines, then from 1750 lines to 1679 lines, then from 1693 lines to 1679 lines *)
(* coqc version 8.5pl1 (April 2016) compiled on Apr 18 2016 14:48:5 with OCaml 4.02.3
   coqtop version 8.5pl1 (April 2016) *)
Require Coq.ZArith.ZArith.

Import Coq.ZArith.ZArith.

Axiom F : Z -> Set.
Definition Let_In {A P} (x : A) (f : forall y : A, P y)
  := let y := x in f y.
Local Open Scope Z_scope.
Definition modulus : Z := 2^255 - 19.
Axiom decode : list Z -> F modulus.
Goal    forall x9 x8 x7 x6 x5 x4 x3 x2 x1 x0 y9 y8 y7 y6 y5 y4 y3 y2 y1 y0 : Z,
   let Zmul := Z.mul in
   let Zadd := Z.add in
   let Zsub := Z.sub in
   let Zpow_pos := Z.pow_pos in
   @eq (F (Zsub (Zpow_pos (Zpos (xO xH)) (xI (xI (xI (xI (xI (xI (xI xH)))))))) (Zpos (xI (xI (xO (xO xH)))))))
     (@decode
        (@Let_In Z (fun _ : Z => list Z)
           (Zadd (Zmul x0 y0)
              (Zmul (Zpos (xI (xI (xO (xO xH)))))
                 (Zadd
                    (Zadd
                       (Zadd
                          (Zadd
                             (Zadd
                                (Zadd
                                   (Zadd (Zadd (Zmul (Zmul x9 y1) (Zpos (xO xH))) (Zmul x8 y2)) (Zmul (Zmul x7 y3) (Zpos (xO xH))))
                                   (Zmul x6 y4)) (Zmul (Zmul x5 y5) (Zpos (xO xH)))) (Zmul x4 y6))
                          (Zmul (Zmul x3 y7) (Zpos (xO xH)))) (Zmul x2 y8)) (Zmul (Zmul x1 y9) (Zpos (xO xH))))))
           (fun z : Z =>
            @Let_In Z (fun _ : Z => list Z)
              (Zadd (Z.shiftr z (Zpos (xO (xI (xO (xI xH))))))
                 (Zadd (Zadd (Zmul x1 y0) (Zmul x0 y1))
                    (Zmul (Zpos (xI (xI (xO (xO xH)))))
                       (Zadd
                          (Zadd
                             (Zadd (Zadd (Zadd (Zadd (Zadd (Zmul x9 y2) (Zmul x8 y3)) (Zmul x7 y4)) (Zmul x6 y5)) (Zmul x5 y6))
                                (Zmul x4 y7)) (Zmul x3 y8)) (Zmul x2 y9)))))
              (fun z0 : Z =>
               @Let_In Z (fun _ : Z => list Z)
                 (Zadd (Z.shiftr z0 (Zpos (xI (xO (xO (xI xH))))))
                    (Zadd (Zadd (Zadd (Zmul x2 y0) (Zmul (Zmul x1 y1) (Zpos (xO xH)))) (Zmul x0 y2))
                       (Zmul (Zpos (xI (xI (xO (xO xH)))))
                          (Zadd
                             (Zadd
                                (Zadd
                                   (Zadd
                                      (Zadd (Zadd (Zmul (Zmul x9 y3) (Zpos (xO xH))) (Zmul x8 y4))
                                         (Zmul (Zmul x7 y5) (Zpos (xO xH)))) (Zmul x6 y6)) (Zmul (Zmul x5 y7) (Zpos (xO xH))))
                                (Zmul x4 y8)) (Zmul (Zmul x3 y9) (Zpos (xO xH)))))))
                 (fun z1 : Z =>
                  @Let_In Z (fun _ : Z => list Z)
                    (Zadd (Z.shiftr z1 (Zpos (xO (xI (xO (xI xH))))))
                       (Zadd (Zadd (Zadd (Zadd (Zmul x3 y0) (Zmul x2 y1)) (Zmul x1 y2)) (Zmul x0 y3))
                          (Zmul (Zpos (xI (xI (xO (xO xH)))))
                             (Zadd (Zadd (Zadd (Zadd (Zadd (Zmul x9 y4) (Zmul x8 y5)) (Zmul x7 y6)) (Zmul x6 y7)) (Zmul x5 y8))
                                (Zmul x4 y9)))))
                    (fun z2 : Z =>
                     @Let_In Z (fun _ : Z => list Z)
                       (Zadd (Z.shiftr z2 (Zpos (xI (xO (xO (xI xH))))))
                          (Zadd
                             (Zadd
                                (Zadd (Zadd (Zadd (Zmul x4 y0) (Zmul (Zmul x3 y1) (Zpos (xO xH)))) (Zmul x2 y2))
                                   (Zmul (Zmul x1 y3) (Zpos (xO xH)))) (Zmul x0 y4))
                             (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                (Zadd
                                   (Zadd
                                      (Zadd (Zadd (Zmul (Zmul x9 y5) (Zpos (xO xH))) (Zmul x8 y6))
                                         (Zmul (Zmul x7 y7) (Zpos (xO xH)))) (Zmul x6 y8)) (Zmul (Zmul x5 y9) (Zpos (xO xH)))))))
                       (fun z3 : Z =>
                        @Let_In Z (fun _ : Z => list Z)
                          (Zadd (Z.shiftr z3 (Zpos (xO (xI (xO (xI xH))))))
                             (Zadd
                                (Zadd (Zadd (Zadd (Zadd (Zadd (Zmul x5 y0) (Zmul x4 y1)) (Zmul x3 y2)) (Zmul x2 y3)) (Zmul x1 y4))
                                   (Zmul x0 y5))
                                (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                   (Zadd (Zadd (Zadd (Zmul x9 y6) (Zmul x8 y7)) (Zmul x7 y8)) (Zmul x6 y9)))))
                          (fun z4 : Z =>
                           @Let_In Z (fun _ : Z => list Z)
                             (Zadd (Z.shiftr z4 (Zpos (xI (xO (xO (xI xH))))))
                                (Zadd
                                   (Zadd
                                      (Zadd
                                         (Zadd
                                            (Zadd (Zadd (Zadd (Zmul x6 y0) (Zmul (Zmul x5 y1) (Zpos (xO xH)))) (Zmul x4 y2))
                                               (Zmul (Zmul x3 y3) (Zpos (xO xH)))) (Zmul x2 y4)) (Zmul (Zmul x1 y5) (Zpos (xO xH))))
                                      (Zmul x0 y6))
                                   (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                      (Zadd (Zadd (Zmul (Zmul x9 y7) (Zpos (xO xH))) (Zmul x8 y8))
                                         (Zmul (Zmul x7 y9) (Zpos (xO xH)))))))
                             (fun z5 : Z =>
                              @Let_In Z (fun _ : Z => list Z)
                                (Zadd (Z.shiftr z5 (Zpos (xO (xI (xO (xI xH))))))
                                   (Zadd
                                      (Zadd
                                         (Zadd
                                            (Zadd
                                               (Zadd (Zadd (Zadd (Zadd (Zmul x7 y0) (Zmul x6 y1)) (Zmul x5 y2)) (Zmul x4 y3))
                                                  (Zmul x3 y4)) (Zmul x2 y5)) (Zmul x1 y6)) (Zmul x0 y7))
                                      (Zmul (Zpos (xI (xI (xO (xO xH))))) (Zadd (Zmul x9 y8) (Zmul x8 y9)))))
                                (fun z6 : Z =>
                                 @Let_In Z (fun _ : Z => list Z)
                                   (Zadd (Z.shiftr z6 (Zpos (xI (xO (xO (xI xH))))))
                                      (Zadd
                                         (Zadd
                                            (Zadd
                                               (Zadd
                                                  (Zadd
                                                     (Zadd
                                                        (Zadd
                                                           (Zadd (Zadd (Zmul x8 y0) (Zmul (Zmul x7 y1) (Zpos (xO xH)))) (Zmul x6 y2))
                                                           (Zmul (Zmul x5 y3) (Zpos (xO xH)))) (Zmul x4 y4))
                                                     (Zmul (Zmul x3 y5) (Zpos (xO xH)))) (Zmul x2 y6))
                                               (Zmul (Zmul x1 y7) (Zpos (xO xH)))) (Zmul x0 y8))
                                         (Zmul (Zmul (Zmul (Zpos (xI (xI (xO (xO xH))))) x9) y9) (Zpos (xO xH)))))
                                   (fun z7 : Z =>
                                    @Let_In Z (fun _ : Z => list Z)
                                      (Zadd (Z.shiftr z7 (Zpos (xO (xI (xO (xI xH))))))
                                         (Zadd
                                            (Zadd
                                               (Zadd
                                                  (Zadd
                                                     (Zadd
                                                        (Zadd
                                                           (Zadd (Zadd (Zadd (Zmul x9 y0) (Zmul x8 y1)) (Zmul x7 y2)) (Zmul x6 y3))
                                                           (Zmul x5 y4)) (Zmul x4 y5)) (Zmul x3 y6)) (Zmul x2 y7))
                                               (Zmul x1 y8)) (Zmul x0 y9)))
                                      (fun z8 : Z =>
                                       @Let_In Z (fun _ : Z => list Z)
                                         (Zadd (Zmul (Zpos (xI (xI (xO (xO xH))))) (Z.shiftr z8 (Zpos (xI (xO (xO (xI xH)))))))
                                            (Z.land z
                                               (Zpos
                                                  (xI
                                                     (xI
                                                        (xI
                                                           (xI
                                                              (xI
                                                                 (xI
                                                                    (xI
                                                                       (xI
                                                                          (xI
                                                                             (xI
                                                                                (xI
                                                                                   (xI
                                                                                      (xI
                                                                                         (xI
                                                                                            (xI
                                                                                               (xI
                                                                                                  (xI
                                                                                                     (xI
                                                                                                       (xI
                                                                                                       (xI
                                                                                                       (xI (xI (xI (xI (xI xH))))))))))))))))))))))))))))
                                         (fun z9 : Z =>
                                          @cons Z
                                            (Z.land z9
                                               (Zpos
                                                  (xI
                                                     (xI
                                                        (xI
                                                           (xI
                                                              (xI
                                                                 (xI
                                                                    (xI
                                                                       (xI
                                                                          (xI
                                                                             (xI
                                                                                (xI
                                                                                   (xI
                                                                                      (xI
                                                                                         (xI
                                                                                            (xI
                                                                                               (xI
                                                                                                  (xI
                                                                                                     (xI
                                                                                                       (xI
                                                                                                       (xI
                                                                                                       (xI (xI (xI (xI (xI xH)))))))))))))))))))))))))))
                                            (@cons Z
                                               (Zadd (Z.shiftr z9 (Zpos (xO (xI (xO (xI xH))))))
                                                  (Z.land z0
                                                     (Zpos
                                                        (xI
                                                           (xI
                                                              (xI
                                                                 (xI
                                                                    (xI
                                                                       (xI
                                                                          (xI
                                                                             (xI
                                                                                (xI
                                                                                   (xI
                                                                                      (xI
                                                                                         (xI
                                                                                            (xI
                                                                                               (xI
                                                                                                  (xI
                                                                                                     (xI
                                                                                                       (xI
                                                                                                       (xI
                                                                                                       (xI
                                                                                                       (xI (xI (xI (xI (xI xH)))))))))))))))))))))))))))
                                               (@cons Z
                                                  (Z.land z1
                                                     (Zpos
                                                        (xI
                                                           (xI
                                                              (xI
                                                                 (xI
                                                                    (xI
                                                                       (xI
                                                                          (xI
                                                                             (xI
                                                                                (xI
                                                                                   (xI
                                                                                      (xI
                                                                                         (xI
                                                                                            (xI
                                                                                               (xI
                                                                                                  (xI
                                                                                                     (xI
                                                                                                       (xI
                                                                                                       (xI
                                                                                                       (xI
                                                                                                       (xI
                                                                                                       (xI (xI (xI (xI (xI xH)))))))))))))))))))))))))))
                                                  (@cons Z
                                                     (Z.land z2
                                                        (Zpos
                                                           (xI
                                                              (xI
                                                                 (xI
                                                                    (xI
                                                                       (xI
                                                                          (xI
                                                                             (xI
                                                                                (xI
                                                                                   (xI
                                                                                      (xI
                                                                                         (xI
                                                                                            (xI
                                                                                               (xI
                                                                                                  (xI
                                                                                                     (xI
                                                                                                       (xI
                                                                                                       (xI
                                                                                                       (xI
                                                                                                       (xI
                                                                                                       (xI (xI (xI (xI (xI xH))))))))))))))))))))))))))
                                                     (@cons Z
                                                        (Z.land z3
                                                           (Zpos
                                                              (xI
                                                                 (xI
                                                                    (xI
                                                                       (xI
                                                                          (xI
                                                                             (xI
                                                                                (xI
                                                                                   (xI
                                                                                      (xI
                                                                                         (xI
                                                                                            (xI
                                                                                               (xI
                                                                                                  (xI
                                                                                                     (xI
                                                                                                       (xI
                                                                                                       (xI
                                                                                                       (xI
                                                                                                       (xI
                                                                                                       (xI
                                                                                                       (xI
                                                                                                       (xI (xI (xI (xI (xI xH)))))))))))))))))))))))))))
                                                        (@cons Z
                                                           (Z.land z4
                                                              (Zpos
                                                                 (xI
                                                                    (xI
                                                                       (xI
                                                                          (xI
                                                                             (xI
                                                                                (xI
                                                                                   (xI
                                                                                      (xI
                                                                                         (xI
                                                                                            (xI
                                                                                               (xI
                                                                                                  (xI
                                                                                                     (xI
                                                                                                       (xI
                                                                                                       (xI
                                                                                                       (xI
                                                                                                       (xI
                                                                                                       (xI
                                                                                                       (xI
                                                                                                       (xI (xI (xI (xI (xI xH))))))))))))))))))))))))))
                                                           (@cons Z
                                                              (Z.land z5
                                                                 (Zpos
                                                                    (xI
                                                                       (xI
                                                                          (xI
                                                                             (xI
                                                                                (xI
                                                                                   (xI
                                                                                      (xI
                                                                                         (xI
                                                                                            (xI
                                                                                               (xI
                                                                                                  (xI
                                                                                                     (xI
                                                                                                       (xI
                                                                                                       (xI
                                                                                                       (xI
                                                                                                       (xI
                                                                                                       (xI
                                                                                                       (xI
                                                                                                       (xI
                                                                                                       (xI
                                                                                                       (xI (xI (xI (xI (xI xH)))))))))))))))))))))))))))
                                                              (@cons Z
                                                                 (Z.land z6
                                                                    (Zpos
                                                                       (xI
                                                                          (xI
                                                                             (xI
                                                                                (xI
                                                                                   (xI
                                                                                      (xI
                                                                                         (xI
                                                                                            (xI
                                                                                               (xI
                                                                                                  (xI
                                                                                                     (xI
                                                                                                       (xI
                                                                                                       (xI
                                                                                                       (xI
                                                                                                       (xI
                                                                                                       (xI
                                                                                                       (xI
                                                                                                       (xI
                                                                                                       (xI
                                                                                                       (xI (xI (xI (xI (xI xH))))))))))))))))))))))))))
                                                                 (@cons Z
                                                                    (Z.land z7
                                                                       (Zpos
                                                                          (xI
                                                                             (xI
                                                                                (xI
                                                                                   (xI
                                                                                      (xI
                                                                                         (xI
                                                                                            (xI
                                                                                               (xI
                                                                                                  (xI
                                                                                                     (xI
                                                                                                       (xI
                                                                                                       (xI
                                                                                                       (xI
                                                                                                       (xI
                                                                                                       (xI
                                                                                                       (xI
                                                                                                       (xI
                                                                                                       (xI
                                                                                                       (xI
                                                                                                       (xI
                                                                                                       (xI (xI (xI (xI (xI xH)))))))))))))))))))))))))))
                                                                    (@cons Z
                                                                       (Z.land z8
                                                                          (Zpos
                                                                             (xI
                                                                                (xI
                                                                                   (xI
                                                                                      (xI
                                                                                         (xI
                                                                                            (xI
                                                                                               (xI
                                                                                                  (xI
                                                                                                     (xI
                                                                                                       (xI
                                                                                                       (xI
                                                                                                       (xI
                                                                                                       (xI
                                                                                                       (xI
                                                                                                       (xI
                                                                                                       (xI
                                                                                                       (xI
                                                                                                       (xI
                                                                                                       (xI
                                                                                                       (xI (xI (xI (xI (xI xH))))))))))))))))))))))))))
                                                                       (@nil Z)))))))))))))))))))))))
     (@decode
        (@cons Z
           (Z.land
              (Zadd
                 (Zmul (Zpos (xI (xI (xO (xO xH)))))
                    (Z.shiftr
                       (Zadd
                          (Z.shiftr
                             (Zadd
                                (Z.shiftr
                                   (Zadd
                                      (Z.shiftr
                                         (Zadd
                                            (Z.shiftr
                                               (Zadd
                                                  (Z.shiftr
                                                     (Zadd
                                                        (Z.shiftr
                                                           (Zadd
                                                              (Z.shiftr
                                                                 (Zadd
                                                                    (Z.shiftr
                                                                       (Zadd
                                                                          (Z.shiftr
                                                                             (Zadd (Zmul x0 y0)
                                                                                (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                                                                   (Zadd
                                                                                      (Zadd
                                                                                         (Zadd
                                                                                            (Zadd
                                                                                               (Zadd
                                                                                                  (Zadd
                                                                                                     (Zadd
                                                                                                       (Zadd
                                                                                                       (Zmul
                                                                                                       (Zmul x9 y1)
                                                                                                       (Zpos (xO xH)))
                                                                                                       (Zmul x8 y2))
                                                                                                       (Zmul
                                                                                                       (Zmul x7 y3)
                                                                                                       (Zpos (xO xH))))
                                                                                                     (Zmul x6 y4))
                                                                                                  (Zmul (Zmul x5 y5) (Zpos (xO xH))))
                                                                                               (Zmul x4 y6))
                                                                                            (Zmul (Zmul x3 y7) (Zpos (xO xH))))
                                                                                         (Zmul x2 y8))
                                                                                      (Zmul (Zmul x1 y9) (Zpos (xO xH))))))
                                                                             (Zpos (xO (xI (xO (xI xH))))))
                                                                          (Zadd (Zadd (Zmul x1 y0) (Zmul x0 y1))
                                                                             (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                                                                (Zadd
                                                                                   (Zadd
                                                                                      (Zadd
                                                                                         (Zadd
                                                                                            (Zadd
                                                                                               (Zadd
                                                                                                  (Zadd (Zmul x9 y2) (Zmul x8 y3))
                                                                                                  (Zmul x7 y4))
                                                                                               (Zmul x6 y5))
                                                                                            (Zmul x5 y6))
                                                                                         (Zmul x4 y7)) (Zmul x3 y8))
                                                                                   (Zmul x2 y9))))) (Zpos (xI (xO (xO (xI xH))))))
                                                                    (Zadd
                                                                       (Zadd (Zadd (Zmul x2 y0) (Zmul (Zmul x1 y1) (Zpos (xO xH))))
                                                                          (Zmul x0 y2))
                                                                       (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                                                          (Zadd
                                                                             (Zadd
                                                                                (Zadd
                                                                                   (Zadd
                                                                                      (Zadd
                                                                                         (Zadd (Zmul (Zmul x9 y3) (Zpos (xO xH)))
                                                                                            (Zmul x8 y4))
                                                                                         (Zmul (Zmul x7 y5) (Zpos (xO xH))))
                                                                                      (Zmul x6 y6))
                                                                                   (Zmul (Zmul x5 y7) (Zpos (xO xH))))
                                                                                (Zmul x4 y8)) (Zmul (Zmul x3 y9) (Zpos (xO xH)))))))
                                                                 (Zpos (xO (xI (xO (xI xH))))))
                                                              (Zadd
                                                                 (Zadd (Zadd (Zadd (Zmul x3 y0) (Zmul x2 y1)) (Zmul x1 y2))
                                                                    (Zmul x0 y3))
                                                                 (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                                                    (Zadd
                                                                       (Zadd
                                                                          (Zadd (Zadd (Zadd (Zmul x9 y4) (Zmul x8 y5)) (Zmul x7 y6))
                                                                             (Zmul x6 y7)) (Zmul x5 y8))
                                                                       (Zmul x4 y9))))) (Zpos (xI (xO (xO (xI xH))))))
                                                        (Zadd
                                                           (Zadd
                                                              (Zadd
                                                                 (Zadd (Zadd (Zmul x4 y0) (Zmul (Zmul x3 y1) (Zpos (xO xH))))
                                                                    (Zmul x2 y2)) (Zmul (Zmul x1 y3) (Zpos (xO xH))))
                                                              (Zmul x0 y4))
                                                           (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                                              (Zadd
                                                                 (Zadd
                                                                    (Zadd (Zadd (Zmul (Zmul x9 y5) (Zpos (xO xH))) (Zmul x8 y6))
                                                                       (Zmul (Zmul x7 y7) (Zpos (xO xH))))
                                                                    (Zmul x6 y8)) (Zmul (Zmul x5 y9) (Zpos (xO xH)))))))
                                                     (Zpos (xO (xI (xO (xI xH))))))
                                                  (Zadd
                                                     (Zadd
                                                        (Zadd
                                                           (Zadd (Zadd (Zadd (Zmul x5 y0) (Zmul x4 y1)) (Zmul x3 y2)) (Zmul x2 y3))
                                                           (Zmul x1 y4)) (Zmul x0 y5))
                                                     (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                                        (Zadd (Zadd (Zadd (Zmul x9 y6) (Zmul x8 y7)) (Zmul x7 y8)) (Zmul x6 y9)))))
                                               (Zpos (xI (xO (xO (xI xH))))))
                                            (Zadd
                                               (Zadd
                                                  (Zadd
                                                     (Zadd
                                                        (Zadd
                                                           (Zadd (Zadd (Zmul x6 y0) (Zmul (Zmul x5 y1) (Zpos (xO xH)))) (Zmul x4 y2))
                                                           (Zmul (Zmul x3 y3) (Zpos (xO xH)))) (Zmul x2 y4))
                                                     (Zmul (Zmul x1 y5) (Zpos (xO xH)))) (Zmul x0 y6))
                                               (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                                  (Zadd (Zadd (Zmul (Zmul x9 y7) (Zpos (xO xH))) (Zmul x8 y8))
                                                     (Zmul (Zmul x7 y9) (Zpos (xO xH))))))) (Zpos (xO (xI (xO (xI xH))))))
                                      (Zadd
                                         (Zadd
                                            (Zadd
                                               (Zadd
                                                  (Zadd (Zadd (Zadd (Zadd (Zmul x7 y0) (Zmul x6 y1)) (Zmul x5 y2)) (Zmul x4 y3))
                                                     (Zmul x3 y4)) (Zmul x2 y5)) (Zmul x1 y6)) (Zmul x0 y7))
                                         (Zmul (Zpos (xI (xI (xO (xO xH))))) (Zadd (Zmul x9 y8) (Zmul x8 y9)))))
                                   (Zpos (xI (xO (xO (xI xH))))))
                                (Zadd
                                   (Zadd
                                      (Zadd
                                         (Zadd
                                            (Zadd
                                               (Zadd
                                                  (Zadd (Zadd (Zadd (Zmul x8 y0) (Zmul (Zmul x7 y1) (Zpos (xO xH)))) (Zmul x6 y2))
                                                     (Zmul (Zmul x5 y3) (Zpos (xO xH)))) (Zmul x4 y4))
                                               (Zmul (Zmul x3 y5) (Zpos (xO xH)))) (Zmul x2 y6)) (Zmul (Zmul x1 y7) (Zpos (xO xH))))
                                      (Zmul x0 y8)) (Zmul (Zmul (Zmul (Zpos (xI (xI (xO (xO xH))))) x9) y9) (Zpos (xO xH)))))
                             (Zpos (xO (xI (xO (xI xH))))))
                          (Zadd
                             (Zadd
                                (Zadd
                                   (Zadd
                                      (Zadd
                                         (Zadd (Zadd (Zadd (Zadd (Zmul x9 y0) (Zmul x8 y1)) (Zmul x7 y2)) (Zmul x6 y3)) (Zmul x5 y4))
                                         (Zmul x4 y5)) (Zmul x3 y6)) (Zmul x2 y7)) (Zmul x1 y8)) (Zmul x0 y9)))
                       (Zpos (xI (xO (xO (xI xH)))))))
                 (Z.land
                    (Zadd (Zmul x0 y0)
                       (Zmul (Zpos (xI (xI (xO (xO xH)))))
                          (Zadd
                             (Zadd
                                (Zadd
                                   (Zadd
                                      (Zadd
                                         (Zadd
                                            (Zadd (Zadd (Zmul (Zmul x9 y1) (Zpos (xO xH))) (Zmul x8 y2))
                                               (Zmul (Zmul x7 y3) (Zpos (xO xH)))) (Zmul x6 y4)) (Zmul (Zmul x5 y5) (Zpos (xO xH))))
                                      (Zmul x4 y6)) (Zmul (Zmul x3 y7) (Zpos (xO xH)))) (Zmul x2 y8))
                             (Zmul (Zmul x1 y9) (Zpos (xO xH))))))
                    (Zpos
                       (xI
                          (xI
                             (xI
                                (xI
                                   (xI
                                      (xI
                                         (xI
                                            (xI
                                               (xI
                                                  (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI xH))))))))))))))))))))))))))))
              (Zpos
                 (xI
                    (xI
                       (xI
                          (xI
                             (xI
                                (xI
                                   (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI xH)))))))))))))))))))))))))))
           (@cons Z
              (Zadd
                 (Z.shiftr
                    (Zadd
                       (Zmul (Zpos (xI (xI (xO (xO xH)))))
                          (Z.shiftr
                             (Zadd
                                (Z.shiftr
                                   (Zadd
                                      (Z.shiftr
                                         (Zadd
                                            (Z.shiftr
                                               (Zadd
                                                  (Z.shiftr
                                                     (Zadd
                                                        (Z.shiftr
                                                           (Zadd
                                                              (Z.shiftr
                                                                 (Zadd
                                                                    (Z.shiftr
                                                                       (Zadd
                                                                          (Z.shiftr
                                                                             (Zadd
                                                                                (Z.shiftr
                                                                                   (Zadd (Zmul x0 y0)
                                                                                      (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                                                                         (Zadd
                                                                                            (Zadd
                                                                                               (Zadd
                                                                                                  (Zadd
                                                                                                     (Zadd
                                                                                                       (Zadd
                                                                                                       (Zadd
                                                                                                       (Zadd
                                                                                                       (Zmul
                                                                                                       (Zmul x9 y1)
                                                                                                       (Zpos (xO xH)))
                                                                                                       (Zmul x8 y2))
                                                                                                       (Zmul
                                                                                                       (Zmul x7 y3)
                                                                                                       (Zpos (xO xH))))
                                                                                                       (Zmul x6 y4))
                                                                                                       (Zmul
                                                                                                       (Zmul x5 y5)
                                                                                                       (Zpos (xO xH))))
                                                                                                     (Zmul x4 y6))
                                                                                                  (Zmul (Zmul x3 y7) (Zpos (xO xH))))
                                                                                               (Zmul x2 y8))
                                                                                            (Zmul (Zmul x1 y9) (Zpos (xO xH))))))
                                                                                   (Zpos (xO (xI (xO (xI xH))))))
                                                                                (Zadd (Zadd (Zmul x1 y0) (Zmul x0 y1))
                                                                                   (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                                                                      (Zadd
                                                                                         (Zadd
                                                                                            (Zadd
                                                                                               (Zadd
                                                                                                  (Zadd
                                                                                                     (Zadd
                                                                                                       (Zadd
                                                                                                       (Zmul x9 y2)
                                                                                                       (Zmul x8 y3))
                                                                                                       (Zmul x7 y4))
                                                                                                     (Zmul x6 y5))
                                                                                                  (Zmul x5 y6))
                                                                                               (Zmul x4 y7))
                                                                                            (Zmul x3 y8))
                                                                                         (Zmul x2 y9)))))
                                                                             (Zpos (xI (xO (xO (xI xH))))))
                                                                          (Zadd
                                                                             (Zadd
                                                                                (Zadd (Zmul x2 y0)
                                                                                   (Zmul (Zmul x1 y1) (Zpos (xO xH))))
                                                                                (Zmul x0 y2))
                                                                             (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                                                                (Zadd
                                                                                   (Zadd
                                                                                      (Zadd
                                                                                         (Zadd
                                                                                            (Zadd
                                                                                               (Zadd
                                                                                                  (Zmul (Zmul x9 y3) (Zpos (xO xH)))
                                                                                                  (Zmul x8 y4))
                                                                                               (Zmul (Zmul x7 y5) (Zpos (xO xH))))
                                                                                            (Zmul x6 y6))
                                                                                         (Zmul (Zmul x5 y7) (Zpos (xO xH))))
                                                                                      (Zmul x4 y8))
                                                                                   (Zmul (Zmul x3 y9) (Zpos (xO xH)))))))
                                                                       (Zpos (xO (xI (xO (xI xH))))))
                                                                    (Zadd
                                                                       (Zadd (Zadd (Zadd (Zmul x3 y0) (Zmul x2 y1)) (Zmul x1 y2))
                                                                          (Zmul x0 y3))
                                                                       (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                                                          (Zadd
                                                                             (Zadd
                                                                                (Zadd
                                                                                   (Zadd (Zadd (Zmul x9 y4) (Zmul x8 y5))
                                                                                      (Zmul x7 y6)) (Zmul x6 y7))
                                                                                (Zmul x5 y8)) (Zmul x4 y9)))))
                                                                 (Zpos (xI (xO (xO (xI xH))))))
                                                              (Zadd
                                                                 (Zadd
                                                                    (Zadd
                                                                       (Zadd (Zadd (Zmul x4 y0) (Zmul (Zmul x3 y1) (Zpos (xO xH))))
                                                                          (Zmul x2 y2)) (Zmul (Zmul x1 y3) (Zpos (xO xH))))
                                                                    (Zmul x0 y4))
                                                                 (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                                                    (Zadd
                                                                       (Zadd
                                                                          (Zadd
                                                                             (Zadd (Zmul (Zmul x9 y5) (Zpos (xO xH))) (Zmul x8 y6))
                                                                             (Zmul (Zmul x7 y7) (Zpos (xO xH))))
                                                                          (Zmul x6 y8)) (Zmul (Zmul x5 y9) (Zpos (xO xH)))))))
                                                           (Zpos (xO (xI (xO (xI xH))))))
                                                        (Zadd
                                                           (Zadd
                                                              (Zadd
                                                                 (Zadd (Zadd (Zadd (Zmul x5 y0) (Zmul x4 y1)) (Zmul x3 y2))
                                                                    (Zmul x2 y3)) (Zmul x1 y4)) (Zmul x0 y5))
                                                           (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                                              (Zadd (Zadd (Zadd (Zmul x9 y6) (Zmul x8 y7)) (Zmul x7 y8))
                                                                 (Zmul x6 y9))))) (Zpos (xI (xO (xO (xI xH))))))
                                                  (Zadd
                                                     (Zadd
                                                        (Zadd
                                                           (Zadd
                                                              (Zadd
                                                                 (Zadd (Zadd (Zmul x6 y0) (Zmul (Zmul x5 y1) (Zpos (xO xH))))
                                                                    (Zmul x4 y2)) (Zmul (Zmul x3 y3) (Zpos (xO xH))))
                                                              (Zmul x2 y4)) (Zmul (Zmul x1 y5) (Zpos (xO xH))))
                                                        (Zmul x0 y6))
                                                     (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                                        (Zadd (Zadd (Zmul (Zmul x9 y7) (Zpos (xO xH))) (Zmul x8 y8))
                                                           (Zmul (Zmul x7 y9) (Zpos (xO xH))))))) (Zpos (xO (xI (xO (xI xH))))))
                                            (Zadd
                                               (Zadd
                                                  (Zadd
                                                     (Zadd
                                                        (Zadd
                                                           (Zadd (Zadd (Zadd (Zmul x7 y0) (Zmul x6 y1)) (Zmul x5 y2)) (Zmul x4 y3))
                                                           (Zmul x3 y4)) (Zmul x2 y5)) (Zmul x1 y6)) (Zmul x0 y7))
                                               (Zmul (Zpos (xI (xI (xO (xO xH))))) (Zadd (Zmul x9 y8) (Zmul x8 y9)))))
                                         (Zpos (xI (xO (xO (xI xH))))))
                                      (Zadd
                                         (Zadd
                                            (Zadd
                                               (Zadd
                                                  (Zadd
                                                     (Zadd
                                                        (Zadd
                                                           (Zadd (Zadd (Zmul x8 y0) (Zmul (Zmul x7 y1) (Zpos (xO xH)))) (Zmul x6 y2))
                                                           (Zmul (Zmul x5 y3) (Zpos (xO xH)))) (Zmul x4 y4))
                                                     (Zmul (Zmul x3 y5) (Zpos (xO xH)))) (Zmul x2 y6))
                                               (Zmul (Zmul x1 y7) (Zpos (xO xH)))) (Zmul x0 y8))
                                         (Zmul (Zmul (Zmul (Zpos (xI (xI (xO (xO xH))))) x9) y9) (Zpos (xO xH)))))
                                   (Zpos (xO (xI (xO (xI xH))))))
                                (Zadd
                                   (Zadd
                                      (Zadd
                                         (Zadd
                                            (Zadd
                                               (Zadd (Zadd (Zadd (Zadd (Zmul x9 y0) (Zmul x8 y1)) (Zmul x7 y2)) (Zmul x6 y3))
                                                  (Zmul x5 y4)) (Zmul x4 y5)) (Zmul x3 y6)) (Zmul x2 y7))
                                      (Zmul x1 y8)) (Zmul x0 y9))) (Zpos (xI (xO (xO (xI xH)))))))
                       (Z.land
                          (Zadd (Zmul x0 y0)
                             (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                (Zadd
                                   (Zadd
                                      (Zadd
                                         (Zadd
                                            (Zadd
                                               (Zadd
                                                  (Zadd (Zadd (Zmul (Zmul x9 y1) (Zpos (xO xH))) (Zmul x8 y2))
                                                     (Zmul (Zmul x7 y3) (Zpos (xO xH)))) (Zmul x6 y4))
                                               (Zmul (Zmul x5 y5) (Zpos (xO xH)))) (Zmul x4 y6)) (Zmul (Zmul x3 y7) (Zpos (xO xH))))
                                      (Zmul x2 y8)) (Zmul (Zmul x1 y9) (Zpos (xO xH))))))
                          (Zpos
                             (xI
                                (xI
                                   (xI
                                      (xI
                                         (xI
                                            (xI
                                               (xI
                                                  (xI
                                                     (xI
                                                        (xI
                                                           (xI
                                                              (xI
                                                                 (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI xH))))))))))))))))))))))))))))
                    (Zpos (xO (xI (xO (xI xH))))))
                 (Z.land
                    (Zadd
                       (Z.shiftr
                          (Zadd (Zmul x0 y0)
                             (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                (Zadd
                                   (Zadd
                                      (Zadd
                                         (Zadd
                                            (Zadd
                                               (Zadd
                                                  (Zadd (Zadd (Zmul (Zmul x9 y1) (Zpos (xO xH))) (Zmul x8 y2))
                                                     (Zmul (Zmul x7 y3) (Zpos (xO xH)))) (Zmul x6 y4))
                                               (Zmul (Zmul x5 y5) (Zpos (xO xH)))) (Zmul x4 y6)) (Zmul (Zmul x3 y7) (Zpos (xO xH))))
                                      (Zmul x2 y8)) (Zmul (Zmul x1 y9) (Zpos (xO xH)))))) (Zpos (xO (xI (xO (xI xH))))))
                       (Zadd (Zadd (Zmul x1 y0) (Zmul x0 y1))
                          (Zmul (Zpos (xI (xI (xO (xO xH)))))
                             (Zadd
                                (Zadd
                                   (Zadd
                                      (Zadd (Zadd (Zadd (Zadd (Zmul x9 y2) (Zmul x8 y3)) (Zmul x7 y4)) (Zmul x6 y5)) (Zmul x5 y6))
                                      (Zmul x4 y7)) (Zmul x3 y8)) (Zmul x2 y9)))))
                    (Zpos
                       (xI
                          (xI
                             (xI
                                (xI
                                   (xI
                                      (xI
                                         (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI xH)))))))))))))))))))))))))))
              (@cons Z
                 (Z.land
                    (Zadd
                       (Z.shiftr
                          (Zadd
                             (Z.shiftr
                                (Zadd (Zmul x0 y0)
                                   (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                      (Zadd
                                         (Zadd
                                            (Zadd
                                               (Zadd
                                                  (Zadd
                                                     (Zadd
                                                        (Zadd (Zadd (Zmul (Zmul x9 y1) (Zpos (xO xH))) (Zmul x8 y2))
                                                           (Zmul (Zmul x7 y3) (Zpos (xO xH)))) (Zmul x6 y4))
                                                     (Zmul (Zmul x5 y5) (Zpos (xO xH)))) (Zmul x4 y6))
                                               (Zmul (Zmul x3 y7) (Zpos (xO xH)))) (Zmul x2 y8)) (Zmul (Zmul x1 y9) (Zpos (xO xH))))))
                                (Zpos (xO (xI (xO (xI xH))))))
                             (Zadd (Zadd (Zmul x1 y0) (Zmul x0 y1))
                                (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                   (Zadd
                                      (Zadd
                                         (Zadd
                                            (Zadd (Zadd (Zadd (Zadd (Zmul x9 y2) (Zmul x8 y3)) (Zmul x7 y4)) (Zmul x6 y5))
                                               (Zmul x5 y6)) (Zmul x4 y7)) (Zmul x3 y8)) (Zmul x2 y9)))))
                          (Zpos (xI (xO (xO (xI xH))))))
                       (Zadd (Zadd (Zadd (Zmul x2 y0) (Zmul (Zmul x1 y1) (Zpos (xO xH)))) (Zmul x0 y2))
                          (Zmul (Zpos (xI (xI (xO (xO xH)))))
                             (Zadd
                                (Zadd
                                   (Zadd
                                      (Zadd
                                         (Zadd (Zadd (Zmul (Zmul x9 y3) (Zpos (xO xH))) (Zmul x8 y4))
                                            (Zmul (Zmul x7 y5) (Zpos (xO xH)))) (Zmul x6 y6)) (Zmul (Zmul x5 y7) (Zpos (xO xH))))
                                   (Zmul x4 y8)) (Zmul (Zmul x3 y9) (Zpos (xO xH)))))))
                    (Zpos
                       (xI
                          (xI
                             (xI
                                (xI
                                   (xI
                                      (xI
                                         (xI
                                            (xI
                                               (xI
                                                  (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI xH)))))))))))))))))))))))))))
                 (@cons Z
                    (Z.land
                       (Zadd
                          (Z.shiftr
                             (Zadd
                                (Z.shiftr
                                   (Zadd
                                      (Z.shiftr
                                         (Zadd (Zmul x0 y0)
                                            (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                               (Zadd
                                                  (Zadd
                                                     (Zadd
                                                        (Zadd
                                                           (Zadd
                                                              (Zadd
                                                                 (Zadd (Zadd (Zmul (Zmul x9 y1) (Zpos (xO xH))) (Zmul x8 y2))
                                                                    (Zmul (Zmul x7 y3) (Zpos (xO xH))))
                                                                 (Zmul x6 y4)) (Zmul (Zmul x5 y5) (Zpos (xO xH))))
                                                           (Zmul x4 y6)) (Zmul (Zmul x3 y7) (Zpos (xO xH))))
                                                     (Zmul x2 y8)) (Zmul (Zmul x1 y9) (Zpos (xO xH))))))
                                         (Zpos (xO (xI (xO (xI xH))))))
                                      (Zadd (Zadd (Zmul x1 y0) (Zmul x0 y1))
                                         (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                            (Zadd
                                               (Zadd
                                                  (Zadd
                                                     (Zadd (Zadd (Zadd (Zadd (Zmul x9 y2) (Zmul x8 y3)) (Zmul x7 y4)) (Zmul x6 y5))
                                                        (Zmul x5 y6)) (Zmul x4 y7)) (Zmul x3 y8)) (Zmul x2 y9)))))
                                   (Zpos (xI (xO (xO (xI xH))))))
                                (Zadd (Zadd (Zadd (Zmul x2 y0) (Zmul (Zmul x1 y1) (Zpos (xO xH)))) (Zmul x0 y2))
                                   (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                      (Zadd
                                         (Zadd
                                            (Zadd
                                               (Zadd
                                                  (Zadd (Zadd (Zmul (Zmul x9 y3) (Zpos (xO xH))) (Zmul x8 y4))
                                                     (Zmul (Zmul x7 y5) (Zpos (xO xH)))) (Zmul x6 y6))
                                               (Zmul (Zmul x5 y7) (Zpos (xO xH)))) (Zmul x4 y8)) (Zmul (Zmul x3 y9) (Zpos (xO xH)))))))
                             (Zpos (xO (xI (xO (xI xH))))))
                          (Zadd (Zadd (Zadd (Zadd (Zmul x3 y0) (Zmul x2 y1)) (Zmul x1 y2)) (Zmul x0 y3))
                             (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                (Zadd (Zadd (Zadd (Zadd (Zadd (Zmul x9 y4) (Zmul x8 y5)) (Zmul x7 y6)) (Zmul x6 y7)) (Zmul x5 y8))
                                   (Zmul x4 y9)))))
                       (Zpos
                          (xI
                             (xI
                                (xI
                                   (xI
                                      (xI
                                         (xI
                                            (xI
                                               (xI
                                                  (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI xH))))))))))))))))))))))))))
                    (@cons Z
                       (Z.land
                          (Zadd
                             (Z.shiftr
                                (Zadd
                                   (Z.shiftr
                                      (Zadd
                                         (Z.shiftr
                                            (Zadd
                                               (Z.shiftr
                                                  (Zadd (Zmul x0 y0)
                                                     (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                                        (Zadd
                                                           (Zadd
                                                              (Zadd
                                                                 (Zadd
                                                                    (Zadd
                                                                       (Zadd
                                                                          (Zadd
                                                                             (Zadd (Zmul (Zmul x9 y1) (Zpos (xO xH))) (Zmul x8 y2))
                                                                             (Zmul (Zmul x7 y3) (Zpos (xO xH))))
                                                                          (Zmul x6 y4)) (Zmul (Zmul x5 y5) (Zpos (xO xH))))
                                                                    (Zmul x4 y6)) (Zmul (Zmul x3 y7) (Zpos (xO xH))))
                                                              (Zmul x2 y8)) (Zmul (Zmul x1 y9) (Zpos (xO xH))))))
                                                  (Zpos (xO (xI (xO (xI xH))))))
                                               (Zadd (Zadd (Zmul x1 y0) (Zmul x0 y1))
                                                  (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                                     (Zadd
                                                        (Zadd
                                                           (Zadd
                                                              (Zadd
                                                                 (Zadd (Zadd (Zadd (Zmul x9 y2) (Zmul x8 y3)) (Zmul x7 y4))
                                                                    (Zmul x6 y5)) (Zmul x5 y6)) (Zmul x4 y7))
                                                           (Zmul x3 y8)) (Zmul x2 y9))))) (Zpos (xI (xO (xO (xI xH))))))
                                         (Zadd (Zadd (Zadd (Zmul x2 y0) (Zmul (Zmul x1 y1) (Zpos (xO xH)))) (Zmul x0 y2))
                                            (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                               (Zadd
                                                  (Zadd
                                                     (Zadd
                                                        (Zadd
                                                           (Zadd (Zadd (Zmul (Zmul x9 y3) (Zpos (xO xH))) (Zmul x8 y4))
                                                              (Zmul (Zmul x7 y5) (Zpos (xO xH)))) (Zmul x6 y6))
                                                        (Zmul (Zmul x5 y7) (Zpos (xO xH)))) (Zmul x4 y8))
                                                  (Zmul (Zmul x3 y9) (Zpos (xO xH))))))) (Zpos (xO (xI (xO (xI xH))))))
                                   (Zadd (Zadd (Zadd (Zadd (Zmul x3 y0) (Zmul x2 y1)) (Zmul x1 y2)) (Zmul x0 y3))
                                      (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                         (Zadd
                                            (Zadd (Zadd (Zadd (Zadd (Zmul x9 y4) (Zmul x8 y5)) (Zmul x7 y6)) (Zmul x6 y7))
                                               (Zmul x5 y8)) (Zmul x4 y9))))) (Zpos (xI (xO (xO (xI xH))))))
                             (Zadd
                                (Zadd
                                   (Zadd (Zadd (Zadd (Zmul x4 y0) (Zmul (Zmul x3 y1) (Zpos (xO xH)))) (Zmul x2 y2))
                                      (Zmul (Zmul x1 y3) (Zpos (xO xH)))) (Zmul x0 y4))
                                (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                   (Zadd
                                      (Zadd
                                         (Zadd (Zadd (Zmul (Zmul x9 y5) (Zpos (xO xH))) (Zmul x8 y6))
                                            (Zmul (Zmul x7 y7) (Zpos (xO xH)))) (Zmul x6 y8)) (Zmul (Zmul x5 y9) (Zpos (xO xH)))))))
                          (Zpos
                             (xI
                                (xI
                                   (xI
                                      (xI
                                         (xI
                                            (xI
                                               (xI
                                                  (xI
                                                     (xI
                                                        (xI
                                                           (xI
                                                              (xI
                                                                 (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI xH)))))))))))))))))))))))))))
                       (@cons Z
                          (Z.land
                             (Zadd
                                (Z.shiftr
                                   (Zadd
                                      (Z.shiftr
                                         (Zadd
                                            (Z.shiftr
                                               (Zadd
                                                  (Z.shiftr
                                                     (Zadd
                                                        (Z.shiftr
                                                           (Zadd (Zmul x0 y0)
                                                              (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                                                 (Zadd
                                                                    (Zadd
                                                                       (Zadd
                                                                          (Zadd
                                                                             (Zadd
                                                                                (Zadd
                                                                                   (Zadd
                                                                                      (Zadd (Zmul (Zmul x9 y1) (Zpos (xO xH)))
                                                                                         (Zmul x8 y2))
                                                                                      (Zmul (Zmul x7 y3) (Zpos (xO xH))))
                                                                                   (Zmul x6 y4)) (Zmul (Zmul x5 y5) (Zpos (xO xH))))
                                                                             (Zmul x4 y6)) (Zmul (Zmul x3 y7) (Zpos (xO xH))))
                                                                       (Zmul x2 y8)) (Zmul (Zmul x1 y9) (Zpos (xO xH))))))
                                                           (Zpos (xO (xI (xO (xI xH))))))
                                                        (Zadd (Zadd (Zmul x1 y0) (Zmul x0 y1))
                                                           (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                                              (Zadd
                                                                 (Zadd
                                                                    (Zadd
                                                                       (Zadd
                                                                          (Zadd (Zadd (Zadd (Zmul x9 y2) (Zmul x8 y3)) (Zmul x7 y4))
                                                                             (Zmul x6 y5)) (Zmul x5 y6))
                                                                       (Zmul x4 y7)) (Zmul x3 y8)) (Zmul x2 y9)))))
                                                     (Zpos (xI (xO (xO (xI xH))))))
                                                  (Zadd (Zadd (Zadd (Zmul x2 y0) (Zmul (Zmul x1 y1) (Zpos (xO xH)))) (Zmul x0 y2))
                                                     (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                                        (Zadd
                                                           (Zadd
                                                              (Zadd
                                                                 (Zadd
                                                                    (Zadd (Zadd (Zmul (Zmul x9 y3) (Zpos (xO xH))) (Zmul x8 y4))
                                                                       (Zmul (Zmul x7 y5) (Zpos (xO xH))))
                                                                    (Zmul x6 y6)) (Zmul (Zmul x5 y7) (Zpos (xO xH))))
                                                              (Zmul x4 y8)) (Zmul (Zmul x3 y9) (Zpos (xO xH)))))))
                                               (Zpos (xO (xI (xO (xI xH))))))
                                            (Zadd (Zadd (Zadd (Zadd (Zmul x3 y0) (Zmul x2 y1)) (Zmul x1 y2)) (Zmul x0 y3))
                                               (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                                  (Zadd
                                                     (Zadd (Zadd (Zadd (Zadd (Zmul x9 y4) (Zmul x8 y5)) (Zmul x7 y6)) (Zmul x6 y7))
                                                        (Zmul x5 y8)) (Zmul x4 y9))))) (Zpos (xI (xO (xO (xI xH))))))
                                      (Zadd
                                         (Zadd
                                            (Zadd (Zadd (Zadd (Zmul x4 y0) (Zmul (Zmul x3 y1) (Zpos (xO xH)))) (Zmul x2 y2))
                                               (Zmul (Zmul x1 y3) (Zpos (xO xH)))) (Zmul x0 y4))
                                         (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                            (Zadd
                                               (Zadd
                                                  (Zadd (Zadd (Zmul (Zmul x9 y5) (Zpos (xO xH))) (Zmul x8 y6))
                                                     (Zmul (Zmul x7 y7) (Zpos (xO xH)))) (Zmul x6 y8))
                                               (Zmul (Zmul x5 y9) (Zpos (xO xH))))))) (Zpos (xO (xI (xO (xI xH))))))
                                (Zadd
                                   (Zadd
                                      (Zadd (Zadd (Zadd (Zadd (Zmul x5 y0) (Zmul x4 y1)) (Zmul x3 y2)) (Zmul x2 y3)) (Zmul x1 y4))
                                      (Zmul x0 y5))
                                   (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                      (Zadd (Zadd (Zadd (Zmul x9 y6) (Zmul x8 y7)) (Zmul x7 y8)) (Zmul x6 y9)))))
                             (Zpos
                                (xI
                                   (xI
                                      (xI
                                         (xI
                                            (xI
                                               (xI
                                                  (xI
                                                     (xI
                                                        (xI
                                                           (xI
                                                              (xI
                                                                 (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI xH))))))))))))))))))))))))))
                          (@cons Z
                             (Z.land
                                (Zadd
                                   (Z.shiftr
                                      (Zadd
                                         (Z.shiftr
                                            (Zadd
                                               (Z.shiftr
                                                  (Zadd
                                                     (Z.shiftr
                                                        (Zadd
                                                           (Z.shiftr
                                                              (Zadd
                                                                 (Z.shiftr
                                                                    (Zadd (Zmul x0 y0)
                                                                       (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                                                          (Zadd
                                                                             (Zadd
                                                                                (Zadd
                                                                                   (Zadd
                                                                                      (Zadd
                                                                                         (Zadd
                                                                                            (Zadd
                                                                                               (Zadd
                                                                                                  (Zmul (Zmul x9 y1) (Zpos (xO xH)))
                                                                                                  (Zmul x8 y2))
                                                                                               (Zmul (Zmul x7 y3) (Zpos (xO xH))))
                                                                                            (Zmul x6 y4))
                                                                                         (Zmul (Zmul x5 y5) (Zpos (xO xH))))
                                                                                      (Zmul x4 y6))
                                                                                   (Zmul (Zmul x3 y7) (Zpos (xO xH))))
                                                                                (Zmul x2 y8)) (Zmul (Zmul x1 y9) (Zpos (xO xH))))))
                                                                    (Zpos (xO (xI (xO (xI xH))))))
                                                                 (Zadd (Zadd (Zmul x1 y0) (Zmul x0 y1))
                                                                    (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                                                       (Zadd
                                                                          (Zadd
                                                                             (Zadd
                                                                                (Zadd
                                                                                   (Zadd
                                                                                      (Zadd (Zadd (Zmul x9 y2) (Zmul x8 y3))
                                                                                         (Zmul x7 y4)) (Zmul x6 y5))
                                                                                   (Zmul x5 y6)) (Zmul x4 y7))
                                                                             (Zmul x3 y8)) (Zmul x2 y9)))))
                                                              (Zpos (xI (xO (xO (xI xH))))))
                                                           (Zadd
                                                              (Zadd (Zadd (Zmul x2 y0) (Zmul (Zmul x1 y1) (Zpos (xO xH))))
                                                                 (Zmul x0 y2))
                                                              (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                                                 (Zadd
                                                                    (Zadd
                                                                       (Zadd
                                                                          (Zadd
                                                                             (Zadd
                                                                                (Zadd (Zmul (Zmul x9 y3) (Zpos (xO xH)))
                                                                                   (Zmul x8 y4)) (Zmul (Zmul x7 y5) (Zpos (xO xH))))
                                                                             (Zmul x6 y6)) (Zmul (Zmul x5 y7) (Zpos (xO xH))))
                                                                       (Zmul x4 y8)) (Zmul (Zmul x3 y9) (Zpos (xO xH)))))))
                                                        (Zpos (xO (xI (xO (xI xH))))))
                                                     (Zadd (Zadd (Zadd (Zadd (Zmul x3 y0) (Zmul x2 y1)) (Zmul x1 y2)) (Zmul x0 y3))
                                                        (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                                           (Zadd
                                                              (Zadd
                                                                 (Zadd (Zadd (Zadd (Zmul x9 y4) (Zmul x8 y5)) (Zmul x7 y6))
                                                                    (Zmul x6 y7)) (Zmul x5 y8)) (Zmul x4 y9)))))
                                                  (Zpos (xI (xO (xO (xI xH))))))
                                               (Zadd
                                                  (Zadd
                                                     (Zadd
                                                        (Zadd (Zadd (Zmul x4 y0) (Zmul (Zmul x3 y1) (Zpos (xO xH)))) (Zmul x2 y2))
                                                        (Zmul (Zmul x1 y3) (Zpos (xO xH)))) (Zmul x0 y4))
                                                  (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                                     (Zadd
                                                        (Zadd
                                                           (Zadd (Zadd (Zmul (Zmul x9 y5) (Zpos (xO xH))) (Zmul x8 y6))
                                                              (Zmul (Zmul x7 y7) (Zpos (xO xH)))) (Zmul x6 y8))
                                                        (Zmul (Zmul x5 y9) (Zpos (xO xH))))))) (Zpos (xO (xI (xO (xI xH))))))
                                         (Zadd
                                            (Zadd
                                               (Zadd (Zadd (Zadd (Zadd (Zmul x5 y0) (Zmul x4 y1)) (Zmul x3 y2)) (Zmul x2 y3))
                                                  (Zmul x1 y4)) (Zmul x0 y5))
                                            (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                               (Zadd (Zadd (Zadd (Zmul x9 y6) (Zmul x8 y7)) (Zmul x7 y8)) (Zmul x6 y9)))))
                                      (Zpos (xI (xO (xO (xI xH))))))
                                   (Zadd
                                      (Zadd
                                         (Zadd
                                            (Zadd
                                               (Zadd (Zadd (Zadd (Zmul x6 y0) (Zmul (Zmul x5 y1) (Zpos (xO xH)))) (Zmul x4 y2))
                                                  (Zmul (Zmul x3 y3) (Zpos (xO xH)))) (Zmul x2 y4))
                                            (Zmul (Zmul x1 y5) (Zpos (xO xH)))) (Zmul x0 y6))
                                      (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                         (Zadd (Zadd (Zmul (Zmul x9 y7) (Zpos (xO xH))) (Zmul x8 y8))
                                            (Zmul (Zmul x7 y9) (Zpos (xO xH)))))))
                                (Zpos
                                   (xI
                                      (xI
                                         (xI
                                            (xI
                                               (xI
                                                  (xI
                                                     (xI
                                                        (xI
                                                           (xI
                                                              (xI
                                                                 (xI
                                                                    (xI
                                                                       (xI
                                                                          (xI
                                                                             (xI
                                                                                (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI xH)))))))))))))))))))))))))))
                             (@cons Z
                                (Z.land
                                   (Zadd
                                      (Z.shiftr
                                         (Zadd
                                            (Z.shiftr
                                               (Zadd
                                                  (Z.shiftr
                                                     (Zadd
                                                        (Z.shiftr
                                                           (Zadd
                                                              (Z.shiftr
                                                                 (Zadd
                                                                    (Z.shiftr
                                                                       (Zadd
                                                                          (Z.shiftr
                                                                             (Zadd (Zmul x0 y0)
                                                                                (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                                                                   (Zadd
                                                                                      (Zadd
                                                                                         (Zadd
                                                                                            (Zadd
                                                                                               (Zadd
                                                                                                  (Zadd
                                                                                                     (Zadd
                                                                                                       (Zadd
                                                                                                       (Zmul
                                                                                                       (Zmul x9 y1)
                                                                                                       (Zpos (xO xH)))
                                                                                                       (Zmul x8 y2))
                                                                                                       (Zmul
                                                                                                       (Zmul x7 y3)
                                                                                                       (Zpos (xO xH))))
                                                                                                     (Zmul x6 y4))
                                                                                                  (Zmul (Zmul x5 y5) (Zpos (xO xH))))
                                                                                               (Zmul x4 y6))
                                                                                            (Zmul (Zmul x3 y7) (Zpos (xO xH))))
                                                                                         (Zmul x2 y8))
                                                                                      (Zmul (Zmul x1 y9) (Zpos (xO xH))))))
                                                                             (Zpos (xO (xI (xO (xI xH))))))
                                                                          (Zadd (Zadd (Zmul x1 y0) (Zmul x0 y1))
                                                                             (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                                                                (Zadd
                                                                                   (Zadd
                                                                                      (Zadd
                                                                                         (Zadd
                                                                                            (Zadd
                                                                                               (Zadd
                                                                                                  (Zadd (Zmul x9 y2) (Zmul x8 y3))
                                                                                                  (Zmul x7 y4))
                                                                                               (Zmul x6 y5))
                                                                                            (Zmul x5 y6))
                                                                                         (Zmul x4 y7)) (Zmul x3 y8))
                                                                                   (Zmul x2 y9))))) (Zpos (xI (xO (xO (xI xH))))))
                                                                    (Zadd
                                                                       (Zadd (Zadd (Zmul x2 y0) (Zmul (Zmul x1 y1) (Zpos (xO xH))))
                                                                          (Zmul x0 y2))
                                                                       (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                                                          (Zadd
                                                                             (Zadd
                                                                                (Zadd
                                                                                   (Zadd
                                                                                      (Zadd
                                                                                         (Zadd (Zmul (Zmul x9 y3) (Zpos (xO xH)))
                                                                                            (Zmul x8 y4))
                                                                                         (Zmul (Zmul x7 y5) (Zpos (xO xH))))
                                                                                      (Zmul x6 y6))
                                                                                   (Zmul (Zmul x5 y7) (Zpos (xO xH))))
                                                                                (Zmul x4 y8)) (Zmul (Zmul x3 y9) (Zpos (xO xH)))))))
                                                                 (Zpos (xO (xI (xO (xI xH))))))
                                                              (Zadd
                                                                 (Zadd (Zadd (Zadd (Zmul x3 y0) (Zmul x2 y1)) (Zmul x1 y2))
                                                                    (Zmul x0 y3))
                                                                 (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                                                    (Zadd
                                                                       (Zadd
                                                                          (Zadd (Zadd (Zadd (Zmul x9 y4) (Zmul x8 y5)) (Zmul x7 y6))
                                                                             (Zmul x6 y7)) (Zmul x5 y8))
                                                                       (Zmul x4 y9))))) (Zpos (xI (xO (xO (xI xH))))))
                                                        (Zadd
                                                           (Zadd
                                                              (Zadd
                                                                 (Zadd (Zadd (Zmul x4 y0) (Zmul (Zmul x3 y1) (Zpos (xO xH))))
                                                                    (Zmul x2 y2)) (Zmul (Zmul x1 y3) (Zpos (xO xH))))
                                                              (Zmul x0 y4))
                                                           (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                                              (Zadd
                                                                 (Zadd
                                                                    (Zadd (Zadd (Zmul (Zmul x9 y5) (Zpos (xO xH))) (Zmul x8 y6))
                                                                       (Zmul (Zmul x7 y7) (Zpos (xO xH))))
                                                                    (Zmul x6 y8)) (Zmul (Zmul x5 y9) (Zpos (xO xH)))))))
                                                     (Zpos (xO (xI (xO (xI xH))))))
                                                  (Zadd
                                                     (Zadd
                                                        (Zadd
                                                           (Zadd (Zadd (Zadd (Zmul x5 y0) (Zmul x4 y1)) (Zmul x3 y2)) (Zmul x2 y3))
                                                           (Zmul x1 y4)) (Zmul x0 y5))
                                                     (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                                        (Zadd (Zadd (Zadd (Zmul x9 y6) (Zmul x8 y7)) (Zmul x7 y8)) (Zmul x6 y9)))))
                                               (Zpos (xI (xO (xO (xI xH))))))
                                            (Zadd
                                               (Zadd
                                                  (Zadd
                                                     (Zadd
                                                        (Zadd
                                                           (Zadd (Zadd (Zmul x6 y0) (Zmul (Zmul x5 y1) (Zpos (xO xH)))) (Zmul x4 y2))
                                                           (Zmul (Zmul x3 y3) (Zpos (xO xH)))) (Zmul x2 y4))
                                                     (Zmul (Zmul x1 y5) (Zpos (xO xH)))) (Zmul x0 y6))
                                               (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                                  (Zadd (Zadd (Zmul (Zmul x9 y7) (Zpos (xO xH))) (Zmul x8 y8))
                                                     (Zmul (Zmul x7 y9) (Zpos (xO xH))))))) (Zpos (xO (xI (xO (xI xH))))))
                                      (Zadd
                                         (Zadd
                                            (Zadd
                                               (Zadd
                                                  (Zadd (Zadd (Zadd (Zadd (Zmul x7 y0) (Zmul x6 y1)) (Zmul x5 y2)) (Zmul x4 y3))
                                                     (Zmul x3 y4)) (Zmul x2 y5)) (Zmul x1 y6)) (Zmul x0 y7))
                                         (Zmul (Zpos (xI (xI (xO (xO xH))))) (Zadd (Zmul x9 y8) (Zmul x8 y9)))))
                                   (Zpos
                                      (xI
                                         (xI
                                            (xI
                                               (xI
                                                  (xI
                                                     (xI
                                                        (xI
                                                           (xI
                                                              (xI
                                                                 (xI
                                                                    (xI
                                                                       (xI
                                                                          (xI
                                                                             (xI
                                                                                (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI xH))))))))))))))))))))))))))
                                (@cons Z
                                   (Z.land
                                      (Zadd
                                         (Z.shiftr
                                            (Zadd
                                               (Z.shiftr
                                                  (Zadd
                                                     (Z.shiftr
                                                        (Zadd
                                                           (Z.shiftr
                                                              (Zadd
                                                                 (Z.shiftr
                                                                    (Zadd
                                                                       (Z.shiftr
                                                                          (Zadd
                                                                             (Z.shiftr
                                                                                (Zadd
                                                                                   (Z.shiftr
                                                                                      (Zadd (Zmul x0 y0)
                                                                                         (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                                                                            (Zadd
                                                                                               (Zadd
                                                                                                  (Zadd
                                                                                                     (Zadd
                                                                                                       (Zadd
                                                                                                       (Zadd
                                                                                                       (Zadd
                                                                                                       (Zadd
                                                                                                       (Zmul
                                                                                                       (Zmul x9 y1)
                                                                                                       (Zpos (xO xH)))
                                                                                                       (Zmul x8 y2))
                                                                                                       (Zmul
                                                                                                       (Zmul x7 y3)
                                                                                                       (Zpos (xO xH))))
                                                                                                       (Zmul x6 y4))
                                                                                                       (Zmul
                                                                                                       (Zmul x5 y5)
                                                                                                       (Zpos (xO xH))))
                                                                                                       (Zmul x4 y6))
                                                                                                     (Zmul
                                                                                                       (Zmul x3 y7)
                                                                                                       (Zpos (xO xH))))
                                                                                                  (Zmul x2 y8))
                                                                                               (Zmul (Zmul x1 y9) (Zpos (xO xH))))))
                                                                                      (Zpos (xO (xI (xO (xI xH))))))
                                                                                   (Zadd (Zadd (Zmul x1 y0) (Zmul x0 y1))
                                                                                      (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                                                                         (Zadd
                                                                                            (Zadd
                                                                                               (Zadd
                                                                                                  (Zadd
                                                                                                     (Zadd
                                                                                                       (Zadd
                                                                                                       (Zadd
                                                                                                       (Zmul x9 y2)
                                                                                                       (Zmul x8 y3))
                                                                                                       (Zmul x7 y4))
                                                                                                       (Zmul x6 y5))
                                                                                                     (Zmul x5 y6))
                                                                                                  (Zmul x4 y7))
                                                                                               (Zmul x3 y8))
                                                                                            (Zmul x2 y9)))))
                                                                                (Zpos (xI (xO (xO (xI xH))))))
                                                                             (Zadd
                                                                                (Zadd
                                                                                   (Zadd (Zmul x2 y0)
                                                                                      (Zmul (Zmul x1 y1) (Zpos (xO xH))))
                                                                                   (Zmul x0 y2))
                                                                                (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                                                                   (Zadd
                                                                                      (Zadd
                                                                                         (Zadd
                                                                                            (Zadd
                                                                                               (Zadd
                                                                                                  (Zadd
                                                                                                     (Zmul
                                                                                                       (Zmul x9 y3)
                                                                                                       (Zpos (xO xH)))
                                                                                                     (Zmul x8 y4))
                                                                                                  (Zmul (Zmul x7 y5) (Zpos (xO xH))))
                                                                                               (Zmul x6 y6))
                                                                                            (Zmul (Zmul x5 y7) (Zpos (xO xH))))
                                                                                         (Zmul x4 y8))
                                                                                      (Zmul (Zmul x3 y9) (Zpos (xO xH)))))))
                                                                          (Zpos (xO (xI (xO (xI xH))))))
                                                                       (Zadd
                                                                          (Zadd (Zadd (Zadd (Zmul x3 y0) (Zmul x2 y1)) (Zmul x1 y2))
                                                                             (Zmul x0 y3))
                                                                          (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                                                             (Zadd
                                                                                (Zadd
                                                                                   (Zadd
                                                                                      (Zadd (Zadd (Zmul x9 y4) (Zmul x8 y5))
                                                                                         (Zmul x7 y6)) (Zmul x6 y7))
                                                                                   (Zmul x5 y8)) (Zmul x4 y9)))))
                                                                    (Zpos (xI (xO (xO (xI xH))))))
                                                                 (Zadd
                                                                    (Zadd
                                                                       (Zadd
                                                                          (Zadd
                                                                             (Zadd (Zmul x4 y0) (Zmul (Zmul x3 y1) (Zpos (xO xH))))
                                                                             (Zmul x2 y2)) (Zmul (Zmul x1 y3) (Zpos (xO xH))))
                                                                       (Zmul x0 y4))
                                                                    (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                                                       (Zadd
                                                                          (Zadd
                                                                             (Zadd
                                                                                (Zadd (Zmul (Zmul x9 y5) (Zpos (xO xH)))
                                                                                   (Zmul x8 y6)) (Zmul (Zmul x7 y7) (Zpos (xO xH))))
                                                                             (Zmul x6 y8)) (Zmul (Zmul x5 y9) (Zpos (xO xH)))))))
                                                              (Zpos (xO (xI (xO (xI xH))))))
                                                           (Zadd
                                                              (Zadd
                                                                 (Zadd
                                                                    (Zadd (Zadd (Zadd (Zmul x5 y0) (Zmul x4 y1)) (Zmul x3 y2))
                                                                       (Zmul x2 y3)) (Zmul x1 y4)) (Zmul x0 y5))
                                                              (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                                                 (Zadd (Zadd (Zadd (Zmul x9 y6) (Zmul x8 y7)) (Zmul x7 y8))
                                                                    (Zmul x6 y9))))) (Zpos (xI (xO (xO (xI xH))))))
                                                     (Zadd
                                                        (Zadd
                                                           (Zadd
                                                              (Zadd
                                                                 (Zadd
                                                                    (Zadd (Zadd (Zmul x6 y0) (Zmul (Zmul x5 y1) (Zpos (xO xH))))
                                                                       (Zmul x4 y2)) (Zmul (Zmul x3 y3) (Zpos (xO xH))))
                                                                 (Zmul x2 y4)) (Zmul (Zmul x1 y5) (Zpos (xO xH))))
                                                           (Zmul x0 y6))
                                                        (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                                           (Zadd (Zadd (Zmul (Zmul x9 y7) (Zpos (xO xH))) (Zmul x8 y8))
                                                              (Zmul (Zmul x7 y9) (Zpos (xO xH))))))) (Zpos (xO (xI (xO (xI xH))))))
                                               (Zadd
                                                  (Zadd
                                                     (Zadd
                                                        (Zadd
                                                           (Zadd
                                                              (Zadd (Zadd (Zadd (Zmul x7 y0) (Zmul x6 y1)) (Zmul x5 y2))
                                                                 (Zmul x4 y3)) (Zmul x3 y4)) (Zmul x2 y5))
                                                        (Zmul x1 y6)) (Zmul x0 y7))
                                                  (Zmul (Zpos (xI (xI (xO (xO xH))))) (Zadd (Zmul x9 y8) (Zmul x8 y9)))))
                                            (Zpos (xI (xO (xO (xI xH))))))
                                         (Zadd
                                            (Zadd
                                               (Zadd
                                                  (Zadd
                                                     (Zadd
                                                        (Zadd
                                                           (Zadd
                                                              (Zadd (Zadd (Zmul x8 y0) (Zmul (Zmul x7 y1) (Zpos (xO xH))))
                                                                 (Zmul x6 y2)) (Zmul (Zmul x5 y3) (Zpos (xO xH))))
                                                           (Zmul x4 y4)) (Zmul (Zmul x3 y5) (Zpos (xO xH))))
                                                     (Zmul x2 y6)) (Zmul (Zmul x1 y7) (Zpos (xO xH)))) (Zmul x0 y8))
                                            (Zmul (Zmul (Zmul (Zpos (xI (xI (xO (xO xH))))) x9) y9) (Zpos (xO xH)))))
                                      (Zpos
                                         (xI
                                            (xI
                                               (xI
                                                  (xI
                                                     (xI
                                                        (xI
                                                           (xI
                                                              (xI
                                                                 (xI
                                                                    (xI
                                                                       (xI
                                                                          (xI
                                                                             (xI
                                                                                (xI
                                                                                   (xI
                                                                                      (xI
                                                                                         (xI
                                                                                            (xI
                                                                                               (xI (xI (xI (xI (xI (xI (xI xH)))))))))))))))))))))))))))
                                   (@cons Z
                                      (Z.land
                                         (Zadd
                                            (Z.shiftr
                                               (Zadd
                                                  (Z.shiftr
                                                     (Zadd
                                                        (Z.shiftr
                                                           (Zadd
                                                              (Z.shiftr
                                                                 (Zadd
                                                                    (Z.shiftr
                                                                       (Zadd
                                                                          (Z.shiftr
                                                                             (Zadd
                                                                                (Z.shiftr
                                                                                   (Zadd
                                                                                      (Z.shiftr
                                                                                         (Zadd
                                                                                            (Z.shiftr
                                                                                               (Zadd (Zmul x0 y0)
                                                                                                  (Zmul
                                                                                                     (Zpos (xI (xI (xO (xO xH)))))
                                                                                                     (Zadd
                                                                                                       (Zadd
                                                                                                       (Zadd
                                                                                                       (Zadd
                                                                                                       (Zadd
                                                                                                       (Zadd
                                                                                                       (Zadd
                                                                                                       (Zadd
                                                                                                       (Zmul
                                                                                                       (Zmul x9 y1)
                                                                                                       (Zpos (xO xH)))
                                                                                                       (Zmul x8 y2))
                                                                                                       (Zmul
                                                                                                       (Zmul x7 y3)
                                                                                                       (Zpos (xO xH))))
                                                                                                       (Zmul x6 y4))
                                                                                                       (Zmul
                                                                                                       (Zmul x5 y5)
                                                                                                       (Zpos (xO xH))))
                                                                                                       (Zmul x4 y6))
                                                                                                       (Zmul
                                                                                                       (Zmul x3 y7)
                                                                                                       (Zpos (xO xH))))
                                                                                                       (Zmul x2 y8))
                                                                                                       (Zmul
                                                                                                       (Zmul x1 y9)
                                                                                                       (Zpos (xO xH))))))
                                                                                               (Zpos (xO (xI (xO (xI xH))))))
                                                                                            (Zadd (Zadd (Zmul x1 y0) (Zmul x0 y1))
                                                                                               (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                                                                                  (Zadd
                                                                                                     (Zadd
                                                                                                       (Zadd
                                                                                                       (Zadd
                                                                                                       (Zadd
                                                                                                       (Zadd
                                                                                                       (Zadd
                                                                                                       (Zmul x9 y2)
                                                                                                       (Zmul x8 y3))
                                                                                                       (Zmul x7 y4))
                                                                                                       (Zmul x6 y5))
                                                                                                       (Zmul x5 y6))
                                                                                                       (Zmul x4 y7))
                                                                                                       (Zmul x3 y8))
                                                                                                     (Zmul x2 y9)))))
                                                                                         (Zpos (xI (xO (xO (xI xH))))))
                                                                                      (Zadd
                                                                                         (Zadd
                                                                                            (Zadd (Zmul x2 y0)
                                                                                               (Zmul (Zmul x1 y1) (Zpos (xO xH))))
                                                                                            (Zmul x0 y2))
                                                                                         (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                                                                            (Zadd
                                                                                               (Zadd
                                                                                                  (Zadd
                                                                                                     (Zadd
                                                                                                       (Zadd
                                                                                                       (Zadd
                                                                                                       (Zmul
                                                                                                       (Zmul x9 y3)
                                                                                                       (Zpos (xO xH)))
                                                                                                       (Zmul x8 y4))
                                                                                                       (Zmul
                                                                                                       (Zmul x7 y5)
                                                                                                       (Zpos (xO xH))))
                                                                                                       (Zmul x6 y6))
                                                                                                     (Zmul
                                                                                                       (Zmul x5 y7)
                                                                                                       (Zpos (xO xH))))
                                                                                                  (Zmul x4 y8))
                                                                                               (Zmul (Zmul x3 y9) (Zpos (xO xH)))))))
                                                                                   (Zpos (xO (xI (xO (xI xH))))))
                                                                                (Zadd
                                                                                   (Zadd
                                                                                      (Zadd (Zadd (Zmul x3 y0) (Zmul x2 y1))
                                                                                         (Zmul x1 y2)) (Zmul x0 y3))
                                                                                   (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                                                                      (Zadd
                                                                                         (Zadd
                                                                                            (Zadd
                                                                                               (Zadd
                                                                                                  (Zadd (Zmul x9 y4) (Zmul x8 y5))
                                                                                                  (Zmul x7 y6))
                                                                                               (Zmul x6 y7))
                                                                                            (Zmul x5 y8))
                                                                                         (Zmul x4 y9)))))
                                                                             (Zpos (xI (xO (xO (xI xH))))))
                                                                          (Zadd
                                                                             (Zadd
                                                                                (Zadd
                                                                                   (Zadd
                                                                                      (Zadd (Zmul x4 y0)
                                                                                         (Zmul (Zmul x3 y1) (Zpos (xO xH))))
                                                                                      (Zmul x2 y2))
                                                                                   (Zmul (Zmul x1 y3) (Zpos (xO xH))))
                                                                                (Zmul x0 y4))
                                                                             (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                                                                (Zadd
                                                                                   (Zadd
                                                                                      (Zadd
                                                                                         (Zadd (Zmul (Zmul x9 y5) (Zpos (xO xH)))
                                                                                            (Zmul x8 y6))
                                                                                         (Zmul (Zmul x7 y7) (Zpos (xO xH))))
                                                                                      (Zmul x6 y8))
                                                                                   (Zmul (Zmul x5 y9) (Zpos (xO xH)))))))
                                                                       (Zpos (xO (xI (xO (xI xH))))))
                                                                    (Zadd
                                                                       (Zadd
                                                                          (Zadd
                                                                             (Zadd
                                                                                (Zadd (Zadd (Zmul x5 y0) (Zmul x4 y1)) (Zmul x3 y2))
                                                                                (Zmul x2 y3)) (Zmul x1 y4))
                                                                          (Zmul x0 y5))
                                                                       (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                                                          (Zadd (Zadd (Zadd (Zmul x9 y6) (Zmul x8 y7)) (Zmul x7 y8))
                                                                             (Zmul x6 y9))))) (Zpos (xI (xO (xO (xI xH))))))
                                                              (Zadd
                                                                 (Zadd
                                                                    (Zadd
                                                                       (Zadd
                                                                          (Zadd
                                                                             (Zadd
                                                                                (Zadd (Zmul x6 y0)
                                                                                   (Zmul (Zmul x5 y1) (Zpos (xO xH))))
                                                                                (Zmul x4 y2)) (Zmul (Zmul x3 y3) (Zpos (xO xH))))
                                                                          (Zmul x2 y4)) (Zmul (Zmul x1 y5) (Zpos (xO xH))))
                                                                    (Zmul x0 y6))
                                                                 (Zmul (Zpos (xI (xI (xO (xO xH)))))
                                                                    (Zadd (Zadd (Zmul (Zmul x9 y7) (Zpos (xO xH))) (Zmul x8 y8))
                                                                       (Zmul (Zmul x7 y9) (Zpos (xO xH)))))))
                                                           (Zpos (xO (xI (xO (xI xH))))))
                                                        (Zadd
                                                           (Zadd
                                                              (Zadd
                                                                 (Zadd
                                                                    (Zadd
                                                                       (Zadd (Zadd (Zadd (Zmul x7 y0) (Zmul x6 y1)) (Zmul x5 y2))
                                                                          (Zmul x4 y3)) (Zmul x3 y4)) (Zmul x2 y5))
                                                                 (Zmul x1 y6)) (Zmul x0 y7))
                                                           (Zmul (Zpos (xI (xI (xO (xO xH))))) (Zadd (Zmul x9 y8) (Zmul x8 y9)))))
                                                     (Zpos (xI (xO (xO (xI xH))))))
                                                  (Zadd
                                                     (Zadd
                                                        (Zadd
                                                           (Zadd
                                                              (Zadd
                                                                 (Zadd
                                                                    (Zadd
                                                                       (Zadd (Zadd (Zmul x8 y0) (Zmul (Zmul x7 y1) (Zpos (xO xH))))
                                                                          (Zmul x6 y2)) (Zmul (Zmul x5 y3) (Zpos (xO xH))))
                                                                    (Zmul x4 y4)) (Zmul (Zmul x3 y5) (Zpos (xO xH))))
                                                              (Zmul x2 y6)) (Zmul (Zmul x1 y7) (Zpos (xO xH))))
                                                        (Zmul x0 y8))
                                                     (Zmul (Zmul (Zmul (Zpos (xI (xI (xO (xO xH))))) x9) y9) (Zpos (xO xH)))))
                                               (Zpos (xO (xI (xO (xI xH))))))
                                            (Zadd
                                               (Zadd
                                                  (Zadd
                                                     (Zadd
                                                        (Zadd
                                                           (Zadd
                                                              (Zadd (Zadd (Zadd (Zmul x9 y0) (Zmul x8 y1)) (Zmul x7 y2))
                                                                 (Zmul x6 y3)) (Zmul x5 y4)) (Zmul x4 y5))
                                                        (Zmul x3 y6)) (Zmul x2 y7)) (Zmul x1 y8)) (Zmul x0 y9)))
                                         (Zpos
                                            (xI
                                               (xI
                                                  (xI
                                                     (xI
                                                        (xI
                                                           (xI
                                                              (xI
                                                                 (xI
                                                                    (xI
                                                                       (xI
                                                                          (xI
                                                                             (xI
                                                                                (xI
                                                                                   (xI
                                                                                      (xI
                                                                                         (xI
                                                                                            (xI
                                                                                               (xI (xI (xI (xI (xI (xI (xI xH))))))))))))))))))))))))))
                                      (@nil Z)))))))))))).
  cbv beta zeta.
  intros.
  (timeout 1 (apply f_equal; reflexivity)) || fail 0 "too early".
  Undo.
  Time Timeout 1 f_equal. (* Finished transaction in 0. secs (0.3u,0.s) in 8.4 *)
