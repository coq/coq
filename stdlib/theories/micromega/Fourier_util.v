Require Export Rbase.
Require Import Lra.

Local Open Scope R_scope.

Lemma Rlt_mult_inv_pos : forall x y:R, 0 < x -> 0 < y -> 0 < x * / y.
Proof.
intros x y H H0; try assumption.
replace 0 with (x * 0).
- apply Rmult_lt_compat_l; auto with real.
- ring.
Qed.

Lemma Rlt_zero_pos_plus1 : forall x:R, 0 < x -> 0 < 1 + x.
Proof.
intros x H; try assumption.
rewrite Rplus_comm.
apply Rplus_lt_0_compat; [assumption | exact Rlt_0_1].
Qed.

Lemma Rle_zero_pos_plus1 : forall x:R, 0 <= x -> 0 <= 1 + x.
Proof.
  intros; lra.
Qed.

Lemma Rle_mult_inv_pos : forall x y:R, 0 <= x -> 0 < y -> 0 <= x * / y.
Proof.
intros x y H H0; try assumption.
case H; intros.
- red; left.
  apply Rlt_mult_inv_pos; auto with real.
- rewrite <- H1.
  red; right; ring.
Qed.
