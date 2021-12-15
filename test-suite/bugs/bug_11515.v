Require Import Ltac2.Ltac2.

Lemma foo :
  True.
Proof.
  Fail rewrite _.
Abort.
