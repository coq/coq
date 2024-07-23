
Module Left.
  Definition mayRet {A:Type} (a b:A): Prop := a=b.

  Lemma zarb A (k:  A) : mayRet k k.
  Proof.

    Succeed Constraint mayRet.u0 < eq.u0.

    apply eq_refl.

    Succeed Constraint mayRet.u0 < eq.u0.
  Defined.
End Left.

Module Right.
  Definition mayRet {A:Type} (a b:A): Prop := a=b.

  Definition mayRet_refl {A} k : @mayRet A k k := eq_refl.

  Lemma zarb A (k:  A) : k = k.
  Proof.
    Succeed Constraint mayRet.u0 < eq.u0.

    apply mayRet_refl.

    Succeed Constraint mayRet.u0 < eq.u0.
  Defined.
End Right.
