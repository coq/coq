Require Import Ltac2.Ltac2.

Set Default Goal Selector "!".

Lemma foo : (False -> False) /\ True.
Proof.
  split.
  Fail ().
  all: ().
  1,2: ().
  Fail all: exact I.
  2: exact I.
  exact (fun x => x).
Qed.
