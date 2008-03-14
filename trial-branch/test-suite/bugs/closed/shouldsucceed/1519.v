Section S.

  Variable A:Prop.
  Variable W:A.

  Remark T: A -> A.
    intro Z.
    rename W into Z_.
    rename Z into W.
    rename Z_ into Z.
    exact Z.
  Qed.

End S.
