Section foo.
  Context (H : 0=0).

  Lemma bar : True \/ True -> True.
  Proof.
  clear H. intros H. destruct H.
  exact H.
  exact H.
  Qed.

End foo.
