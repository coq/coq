Lemma minbug (n : nat) (P : nat -> Prop) (pn : P n) : exists (m : nat) (p : P m), True.
Proof.
  exists _, pn.
  exact I.
Qed.
