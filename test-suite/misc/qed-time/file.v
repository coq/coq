Lemma foo : True.
Proof.
  Axiom X : ltac:(try timeout 1 repeat pose True; exact nat).
  exact I.
Qed.
