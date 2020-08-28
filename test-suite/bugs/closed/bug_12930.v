Section S.
  Variable v : Prop.
  Variable vv : v.
  Collection easy := Type*.

  Lemma ybar : v.
  Proof using easy.
    exact vv.
  Qed.
End S.
