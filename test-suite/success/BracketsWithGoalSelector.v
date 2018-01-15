Goal forall A B, B \/ A -> A \/ B.
Proof.
  intros * [HB | HA].
  2: {
    left.
    exact HA.
  }
  right.
  exact HB.
Qed.
