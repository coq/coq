Lemma foo : forall x y:nat, x < y -> False.
Proof.
  intros x y H.
  induction H as [ |?y ?y ?y].
Abort.
