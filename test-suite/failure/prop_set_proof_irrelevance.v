Require Import ProofIrrelevance.

Lemma proof_irrelevance_set : forall (P : Set) (p1 p2 : P), p1 = p2.
  Fail exact proof_irrelevance.
(*Qed.

Lemma paradox : False.
  assert (H : 0 <> 1) by discriminate.
  apply H.
  Fail apply proof_irrelevance. (* inlined version is rejected *)
  apply proof_irrelevance_set.
Qed.*)
