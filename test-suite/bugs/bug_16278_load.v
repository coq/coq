Set Nested Proofs Allowed.

Lemma outer : True.
Proof.
  Lemma inner : True.
  Proof. constructor. Qed.
  exact inner.
Qed.
