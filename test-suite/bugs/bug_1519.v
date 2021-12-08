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

  (* bug :
     Error:
     Unbound reference: In environment
     A : Prop
     W : A
     Z : A
     The reference 2 is free
     *)

End S.
