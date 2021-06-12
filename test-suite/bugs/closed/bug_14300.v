Lemma foo : Prop = (True : Type) -> Prop.
Proof.
  intro H.
  pattern Prop.
  rewrite H.
  exact I.
Qed.
