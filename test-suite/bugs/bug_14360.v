Lemma foo : nat.
Proof.
  exact 0.
  Fail #[bar] Defined.
  Fail #[bar] Qed.
Defined.
