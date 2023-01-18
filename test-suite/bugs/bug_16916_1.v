Require Import Ltac2.Ltac2.

Goal True -> True.
Proof.
  intros.
  Fail match! goal with [ h : (_ : ?t) |- _ ] => () end.
Abort.
