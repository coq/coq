Require Export BinNat BinPos Lia.

Module Pos.
  Lemma land_mono : forall a b, (Pos.land a b <= N.pos a)%N.
  Proof. induction a, b; cbn [Pos.land]; try specialize (IHa b); lia. Qed.

  Lemma ldiff_mono : forall a b, (Pos.ldiff a b <= N.pos a)%N.
  Proof. induction a, b; cbn [Pos.ldiff]; try specialize (IHa b); try lia. Qed.

  Lemma div2_le a : (Pos.div2 a <= a)%positive.
  Proof. induction a; cbn [Pos.div2]; lia. Qed.

  Lemma shiftr_mono a b : (Pos.shiftr a b <= a)%positive.
  Proof.
    case b as [|b]; cbn [Pos.shiftr]; [lia|].
    revert a; induction b; cbn [Pos.iter];
      repeat (etransitivity; [eapply div2_le || eapply IHb|]); reflexivity.
  Qed.

  Lemma shiftl_mono a b : (a <= Pos.shiftl a b)%positive.
  Proof.
    case b as [|b]; cbn [Pos.shiftl]; [lia|].
    revert a; induction b; cbn [Pos.iter]; intros;
      try pose (IHb (Pos.iter xO a b)); try pose (IHb a); lia.
  Qed.

  Import Pnat Nnat Znat.
  Lemma pow_add_r (a b c : positive) : (a^(b+c) = a^b * a^c)%positive.
  Proof.
    enough (N.pos (a ^ (b + c)) = N.pos (a ^ b * a ^ c)) by lia.
    rewrite <-(positive_nat_N (Pos.pow _ _)), Pos2Nat.inj_pow, Nat2N.inj_pow, 2positive_nat_N.
    replace (N.pos (b+c)) with (N.pos b + N.pos c)%N by lia; rewrite N.pow_add_r; lia.
  Qed.
End Pos.
