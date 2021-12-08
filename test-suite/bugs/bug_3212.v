Lemma H : Prop = Prop.
reflexivity.
Qed.

Lemma foo : match H in (_ = X) return X with
  | eq_refl => True
end.
Proof.
Fail destruct H.
Abort.
