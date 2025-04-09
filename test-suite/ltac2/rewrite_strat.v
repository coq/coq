Require Import Setoid.

From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Std.
From Ltac2 Require Import Rewrite.

Parameter X : Set.

Parameter f : X -> X.
Parameter g : X -> X -> X.
Parameter h : nat -> X -> X.

Parameter lem0 : forall x, f (f x) = f x.
Parameter lem1 : forall x, g x x = f x.
Parameter lem2 : forall n x, h (S n) x = g (h n x) (h n x).
Parameter lem3 : forall x, h 0 x = x.

#[export] Hint Rewrite lem0 lem1 lem2 lem3 : rew.

Goal forall x, h 6 x = f x.
  intros.
  time (rewrite_strat (Rewrite.topdown (Rewrite.term preterm:(lem2) true)) None).
  time (rewrite_strat (Rewrite.topdown (Rewrite.term preterm:(lem1) true)) None).
  time (rewrite_strat (Rewrite.topdown (Rewrite.term preterm:(lem0) true)) None).
  time (rewrite_strat (Rewrite.topdown (Rewrite.term preterm:(lem3) true)) None).
  reflexivity ().
Undo 5.
  time (rewrite_strat (Rewrite.topdown
          (Rewrite.choice
             (Rewrite.term preterm:(lem2) true)
             (Rewrite.term preterm:(lem1) true)
       )) None).
  time (rewrite_strat (Rewrite.topdown
          (Rewrite.choice
             (Rewrite.term preterm:(lem0) true)
             (Rewrite.term preterm:(lem3) true)
       )) None).
  reflexivity ().
Undo 3.
time (rewrite_strat (Rewrite.seq
                       (Rewrite.topdown
                          (Rewrite.choice
                             (Rewrite.term preterm:(lem2) true)
                             (Rewrite.term preterm:(lem1) true)
                       ))
                       (Rewrite.topdown
                          (Rewrite.choice
                             (Rewrite.term preterm:(lem0) true)
                             (Rewrite.term preterm:(lem3) true)
                          ))
       ) None).
  reflexivity ().
Undo 2.
  time (rewrite_strat (Rewrite.topdown
                         (Rewrite.choice
                              (Rewrite.choice
                                 (Rewrite.term preterm:(lem2) true)
                                 (Rewrite.term preterm:(lem1) true)
                              )
                              (Rewrite.choice
                                 (Rewrite.term preterm:(lem0) true)
                                 (Rewrite.term preterm:(lem3) true)
                              )
                         )
          ) None).
  reflexivity ().
Undo 2.
  time (rewrite_strat (Rewrite.topdown
                         (Rewrite.choice
                              (Rewrite.term preterm:(lem2) true)
                              (Rewrite.choice
                                 (Rewrite.term preterm:(lem1) true)
                                 (Rewrite.choice
                                    (Rewrite.term preterm:(lem0) true)
                                    (Rewrite.term preterm:(lem3) true)
                                 )
                            )
                         )
       ) None).
  reflexivity ().
Undo 2.
  time (rewrite_strat (Rewrite.topdown
                         (Rewrite.choices [
                              (Rewrite.term preterm:(lem2) true);
                              (Rewrite.term preterm:(lem1) true);
                              (Rewrite.term preterm:(lem0) true);
                              (Rewrite.term preterm:(lem3) true)
                            ]
                         )
          ) None).
  reflexivity ().
Undo 2.
  time (rewrite_strat (Rewrite.fix_
                         (fun f =>
                            Rewrite.seq
                              (Rewrite.choices [
                                   (Rewrite.term preterm:(lem2) true);
                                   (Rewrite.term preterm:(lem1) true);
                                   (Rewrite.term preterm:(lem0) true);
                                   (Rewrite.term preterm:(lem3) true);
                                   (Rewrite.progress (Rewrite.subterms f))
                                 ])
                            (Rewrite.try f)
                         )
       ) None).
  reflexivity ().
Qed.

Goal forall x, h 10 x = f x.
Proof.
  intros.
  time (rewrite_strat (Rewrite.topdown (hints @rew)) None).
  reflexivity ().
Qed.

Set Printing All.
Set Printing Depth 100000.

Ltac2 Notation "my_rewrite_strat" x(preterm) := rewrite_strat (Rewrite.topdown (Rewrite.term x true)) None.
Goal (forall x, S x = 0) -> 1 = 0.
intro H.
my_rewrite_strat H.
Abort.
