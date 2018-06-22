Require Export Rbase.
Require Import Lra.

Open Scope R_scope.

Lemma Rlt_mult_inv_pos : forall x y:R, 0 < x -> 0 < y -> 0 < x * / y.
intros x y H H0; try assumption.
replace 0 with (x * 0).
apply Rmult_lt_compat_l; auto with real.
ring.
Qed.

Lemma Rlt_zero_pos_plus1 : forall x:R, 0 < x -> 0 < 1 + x.
intros x H; try assumption.
rewrite Rplus_comm.
apply Rle_lt_0_plus_1.
red; auto with real.
Qed.

Lemma Rle_zero_pos_plus1 : forall x:R, 0 <= x -> 0 <= 1 + x.
  intros; lra.
Qed.

Lemma Rle_mult_inv_pos : forall x y:R, 0 <= x -> 0 < y -> 0 <= x * / y.
intros x y H H0; try assumption.
case H; intros.
red; left.
apply Rlt_mult_inv_pos; auto with real.
rewrite <- H1.
red; right; ring.
Qed.
