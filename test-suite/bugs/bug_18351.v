Require Import Ltac2.Ltac2.

Set Default Goal Selector "!".

Goal True /\ True.
  split.
  Fail exact I. (* not focused *)
  1:{ exact I. }
  exact I.
Qed.
