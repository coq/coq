From Ltac2 Require Import Ltac2.

Lemma zero_numgoals : True.
Proof.
  reflexivity.
  Ltac2 Eval Control.numgoals ().
Qed.
