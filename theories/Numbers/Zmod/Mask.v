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

Lemma mask_ok w b : mask w b = mask' (2^w) b.
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
  rewrite mask_ok. apply signed_mask'.
  zify; apply (Z.pow_le_mono_r 2 1); lia.
Qed.

Lemma and_true_r {w} x : and x (mask w true) = x.
Proof.
  apply to_N_inj; rewrite to_N_and, to_N_mask, N.land_ones.
  apply N.mod_small, to_N_range.
Qed.

Definition msb {w} x := @srs_N (2^w) x (Pos.pred_N w).

Lemma msb_correct w x : @msb w x = mask w (N.testbit x (Pos.pred_N w)).
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

Lemma to_N_msb w x : msb x = mask w (negb (to_N x <? 2^Pos.pred_N w)%N).
Proof. 
Abort.
