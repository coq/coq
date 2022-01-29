Require Import Ltac2.Ltac2.

Example Ex1: forall a : nat, True.
  intros a.
  Ltac2 Eval 'a.
  exact I.
Qed.
