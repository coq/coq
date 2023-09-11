Set Mangle Names.

Section test.
  Context (P Q : Prop).
  Lemma p_q : P <-> Q. Proof. Admitted.
  Lemma test : Q -> P.
  Proof.
    intros HQ. apply <-p_q.
    assumption.
  Qed.
End test.
