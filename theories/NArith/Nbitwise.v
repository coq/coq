Require Import BinPos_facts NArith Lia.

Module N.

Import BinNat.
Local Open Scope N_scope.

Lemma land_mono a b : N.land a b <= a.
Proof. case a, b; cbn [N.land]; trivial using Pos.land_mono; lia. Qed.

Lemma ldiff_mono a b : N.ldiff a b <= a.
Proof. case a, b; cbn [N.ldiff]; trivial using Pos.ldiff_mono; lia. Qed.

Lemma lnot_ones_same n : N.lnot (N.ones n) n = 0.
Proof.
  apply N.bits_inj; intro i; destruct (N.ltb_spec i n);
    rewrite ?N.lnot_spec_low, ?N.lnot_spec_high, ?N.ones_spec_low, ?N.ones_spec_high, ?N.bits_0 by lia; trivial.
Qed.

Lemma div2_le a : N.div2 a <= a.
Proof. case a; cbn; [lia|]. destruct p; lia. Qed.

Lemma shiftr_mono a b : N.shiftr a b <= a.
Proof.
  case b as [|b]; cbn [N.shiftr]; try lia.
  revert a; induction b; cbn [Pos.iter];
    repeat (etransitivity; [eapply div2_le || eapply IHb|]); reflexivity.
Qed.

Lemma shiftl_mono a b : a <= N.shiftl a b.
Proof. case a as []; [lia|]. apply Pos.shiftl_mono. Qed.

Lemma ones_succ n (H : N.le 0 n) : N.ones (N.succ n) = N.succ_double (N.ones n).
Proof. rewrite 2N.ones_equiv, N.pow_succ_r; lia. Qed.

End N.
