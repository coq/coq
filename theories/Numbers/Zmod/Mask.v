Require Import Coq.Numbers.Zmod.TODO_MOVE.

Require Import Coq.NArith.NArith Coq.ZArith.ZArith Coq.micromega.Lia.

Require Import Coq.Numbers.Zmod.Base.
Require Import Coq.Numbers.Zmod.FastPow2.

Local Open Scope Z_scope.
Import Coercions.

Definition mask' m (b : bool) : Zmod m.
  refine (of_small_N m (if b then Pos.pred_N m else 0) (fun _ => _)).
  abstract (case b; lia).
Defined.

Definition mask w (b : bool) : Zmod (2^w).
  refine (of_small_N (2^w) (if b then Pos.ones w else 0) (fun _ => _)).
  abstract (rewrite N.pos_ones, N.ones_equiv; case b; lia).
Defined.

Lemma to_N_mask' m b : to_N (mask' m b) = if b then Pos.pred_N m else N.zero.
Proof. case b; trivial. Qed.

Lemma to_N_mask w b : to_N (mask w b) = if b then N.ones w else N.zero.
Proof. cbv [mask]. rewrite to_N_of_small_N, N.pos_ones; trivial. Qed.

Lemma mask_correct w b : mask w b = mask' (2^w) b.
Proof. apply to_N_inj; rewrite to_N_mask', to_N_mask; trivial. Qed.

Lemma to_Z_mask' m b : to_Z (mask' m b) = if b then Pos.pred_N m else Z.zero.
Proof. case b; trivial. Qed.

Lemma signed_mask' (m : positive) (Hm : 2 <= m) b : signed (mask' m b) = - Z.b2z b.
Proof.
  rewrite <-smod_unsigned, to_Z_mask'; destruct b; cbn [Z.b2z].
  { cbv [Z.smodulo Z.omodulo]; rewrite <-Z.mod_add with (b:=-1), Z.mod_small;
    Z.to_euclidean_division_equations; nia. }
  { rewrite Z.smod_0_l; trivial. }
Qed.

Lemma to_Z_mask w b : to_Z (mask w b) = if b then Z.ones w else Z.zero.
Proof. cbv [mask]. rewrite to_Z_of_small_N. case b; trivial; apply Z.pos_ones. Qed.

Lemma signed_mask w b : signed (mask w b) = - Z.b2z b.
Proof.
  rewrite mask_correct. apply signed_mask'.
  zify; apply (Z.pow_le_mono_r 2 1); lia.
Qed.

Lemma mask'_inj {m} (Hm : Pos.le 2 m) a b (H : @mask' m a = @mask' m b) : a = b.
Proof. inversion H; case a, b in *; trivial; lia. Qed.

Lemma mask_inj {w} a b (H : @mask w a = @mask w b) : a = b.
Proof.
  rewrite 2 mask_correct in H; eapply mask'_inj; eauto.
  zify. transitivity (2^1)%Z; try eapply Z.pow_le_mono_r; lia.
Qed.

Lemma and_true_r {w} x : and x (mask w true) = x.
Proof.
  apply to_N_inj; rewrite to_N_and, to_N_mask, N.land_ones.
  apply N.mod_small, to_N_range.
Qed.

Lemma mask_negb w b : mask w (negb b) = not (mask _ b).
Proof.
  apply to_N_inj; rewrite to_N_not, 2to_N_mask; case b; cbn [negb].
  { rewrite ?N.lnot_ones_same; trivial. }
  (* work around rewrite *) setoid_rewrite N.lnot_0_l; trivial.
Qed.

Lemma mask_andb w a b : mask w (andb a b) = and (mask _ a) (mask _ b).
Proof.
  apply to_N_inj; rewrite to_N_and, 3to_N_mask; case a, b; cbn [andb];
    rewrite ?N.land_diag, ?N.land_0_r; trivial.
Qed.

Lemma mask_orb w a b : mask w (orb a b) = or (mask _ a) (mask _ b).
Proof.
  apply to_N_inj; rewrite to_N_or_pow2, 3to_N_mask; case a, b; cbn [orb];
    rewrite ?N.lor_diag, ?N.lor_0_r; trivial.
Qed.

Lemma mask_xorb w a b : mask w (xorb a b) = xor (mask _ a) (mask _ b).
Proof.
  apply to_N_inj; rewrite to_N_xor_pow2, 3to_N_mask; case a, b; cbn [xorb];
    rewrite ?N.lxor_nilpotent, ?N.lxor_0_r; trivial.
Qed.

Definition msb {w} x := @srs_N (2^w) x (Pos.pred_N w).

Lemma msb_correct_N w x : @msb w x = mask w (N.testbit x (Pos.pred_N w)).
Proof.
  cbv [msb]. apply signed_inj. rewrite signed_mask, signed_srs_N.
  rewrite <-Z.of_N_b2n, N.testbit_spec', Z.shiftr_div_pow2 by lia.
  assert ((2 ^ w)%positive = 2*2^Pos.pred_N w :> Z)
    by (rewrite Pos2Z.inj_pow, <-Z.pow_succ_r; f_equal; lia).
  pose proof to_Z_range x.
  rewrite N.mod_small by
    (apply N.Div0.div_lt_upper_bound; cbv [to_Z] in *; lia).
  rewrite N2Z.inj_div, N2Z.inj_pow; cbn.
  rewrite <-mod_to_N, N2Z.inj_mod, <-smod_unsigned, Z.smod_complement; trivial.
Qed.

Lemma msb_correct w x : @msb w x = mask w (Z.testbit x (Pos.pred_N w)).
Proof. rewrite msb_correct_N, <-Z.testbit_of_N; trivial. Qed.

Lemma msb_as_Nle w x : msb x = mask w (2^Pos.pred_N w <=? x)%N.
Proof. rewrite msb_correct_N; f_equal; apply testbit_le_N. Qed.

Lemma msb_as_le w x : msb x = mask w (2^Pos.pred_N w <=? x).
Proof. rewrite msb_correct, <-testbit_le; trivial. Qed.

Lemma msb_as_neg w x : msb x = mask w (signed x <? 0).
Proof. rewrite msb_correct, <-testbit_neg; trivial. Qed.

Lemma msb_not w x : @msb w (not x) = not (msb x).
Proof.
  rewrite 2msb_correct, to_Z_not, Z.mod_pow2_bits_low, Z.lnot_spec, mask_negb by lia; trivial.
Qed.

Lemma msb_and w x y : @msb w (and x y) = and (msb x) (msb y).
Proof. rewrite 3msb_correct, to_Z_and, Z.land_spec, mask_andb; trivial. Qed.

Lemma msb_or w x y : @msb w (or x y) = or (msb x) (msb y).
Proof. rewrite 3msb_correct, to_Z_or_pow2, Z.lor_spec, mask_orb; trivial. Qed.

Lemma msb_xor w x y : @msb w (xor x y) = xor (msb x) (msb y).
Proof. rewrite 3msb_correct, to_Z_xor_pow2, Z.lxor_spec, mask_xorb; trivial. Qed.

Definition nonzero {w} x := @msb w (or x (opp x)).

Lemma nonzero_correct w x : nonzero x = mask w (negb (eqb x zero)).
Proof. cbv [nonzero]. rewrite msb_correct; f_equal. apply testbit_neqb0. Qed.

Definition equal {w} x y : Zmod (2^w) := not (nonzero (xor x y)).

Lemma not_mask {w} b : not (mask (2^w) b) = mask _ (negb b).
Proof.
  apply to_N_inj. rewrite to_N_not, !to_N_mask.
  case b; cbn [negb]; rewrite ?N.lnot_ones_same, ?N.bits_0; trivial.
Qed.

Lemma equal_correct w x y : equal x y = mask (2^w) (eqb x y).
Proof.
  cbv [equal]; rewrite nonzero_correct, not_mask, Bool.negb_involutive, eqb_xor_zero; trivial.
Qed.

Lemma and_mask {w} a b : and (mask (2^w) a) (mask _ b) = mask _ (a && b).
Proof.
  apply to_N_inj. rewrite to_N_and, !to_N_mask.
  case a, b; rewrite ?N.land_spec, ?N.land_diag, ?N.land_0_r; trivial.
Qed.

Lemma or_mask {w} a b : or (mask (2^w) a) (mask _ b) = mask _ (a || b).
Proof.
  apply to_N_inj. rewrite to_N_or_pow2, !to_N_mask.
  case a, b; rewrite ?N.lor_spec, ?N.lor_diag, ?N.lor_0_r; trivial.
Qed.

Definition less {w} x y : Zmod (2^w) :=
  msb (xor x (or (xor x y) (xor (sub x y) x))).

Lemma less_correct w x y : less x y = mask (2^w) (x <? y)%N.
Proof.
  cbv [less]; repeat rewrite ?msb_xor, ?msb_or, ?msb_and; rewrite ?msb_correct_N.
  repeat rewrite <-?mask_xorb, <-?mask_orb, <-?mask_andb; f_equal.
  set (Pos.pred_N (2 ^ w)) as i.
  destruct (xorb (N.testbit x i) (N.testbit y i)) eqn:?; cbn [orb]; cycle 1.
  { rewrite Bool.xorb_comm, Bool.xorb_assoc, ?Bool.xorb_nilpotent.
    assert (xorb (N.testbit (sub x y) i) false = (x <? y)%N) by admit; trivial. }
  rewrite Bool.xorb_true_r, N.ltb_antisym; f_equal.
  assert (xorb (N.testbit x i) (N.testbit y i) = true -> N.testbit x i = (y <=? x)%N) by admit; auto.
Abort.
