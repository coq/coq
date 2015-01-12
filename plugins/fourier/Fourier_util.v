(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Export Rbase.
Comments "Lemmas used by the tactic Fourier".

Open Scope R_scope.

Lemma Rfourier_lt : forall x1 y1 a:R, x1 < y1 -> 0 < a -> a * x1 < a * y1.
intros; apply Rmult_lt_compat_l; assumption.
Qed.

Lemma Rfourier_le : forall x1 y1 a:R, x1 <= y1 -> 0 < a -> a * x1 <= a * y1.
red.
intros.
case H; auto with real.
Qed.

Lemma Rfourier_lt_lt :
 forall x1 y1 x2 y2 a:R,
   x1 < y1 -> x2 < y2 -> 0 < a -> x1 + a * x2 < y1 + a * y2.
intros x1 y1 x2 y2 a H H0 H1; try assumption.
apply Rplus_lt_compat.
try exact H.
apply Rfourier_lt.
try exact H0.
try exact H1.
Qed.

Lemma Rfourier_lt_le :
 forall x1 y1 x2 y2 a:R,
   x1 < y1 -> x2 <= y2 -> 0 < a -> x1 + a * x2 < y1 + a * y2.
intros x1 y1 x2 y2 a H H0 H1; try assumption.
case H0; intros.
apply Rplus_lt_compat.
try exact H.
apply Rfourier_lt; auto with real.
rewrite H2.
rewrite (Rplus_comm y1 (a * y2)).
rewrite (Rplus_comm x1 (a * y2)).
apply Rplus_lt_compat_l.
try exact H.
Qed.

Lemma Rfourier_le_lt :
 forall x1 y1 x2 y2 a:R,
   x1 <= y1 -> x2 < y2 -> 0 < a -> x1 + a * x2 < y1 + a * y2.
intros x1 y1 x2 y2 a H H0 H1; try assumption.
case H; intros.
apply Rfourier_lt_le; auto with real.
rewrite H2.
apply Rplus_lt_compat_l.
apply Rfourier_lt; auto with real.
Qed.

Lemma Rfourier_le_le :
 forall x1 y1 x2 y2 a:R,
   x1 <= y1 -> x2 <= y2 -> 0 < a -> x1 + a * x2 <= y1 + a * y2.
intros x1 y1 x2 y2 a H H0 H1; try assumption.
case H0; intros.
red.
left; try assumption.
apply Rfourier_le_lt; auto with real.
rewrite H2.
case H; intros.
red.
left; try assumption.
rewrite (Rplus_comm x1 (a * y2)).
rewrite (Rplus_comm y1 (a * y2)).
apply Rplus_lt_compat_l.
try exact H3.
rewrite H3.
red.
right; try assumption.
auto with real.
Qed.

Lemma Rlt_zero_pos_plus1 : forall x:R, 0 < x -> 0 < 1 + x.
intros x H; try assumption.
rewrite Rplus_comm.
apply Rle_lt_0_plus_1.
red; auto with real.
Qed.

Lemma Rlt_mult_inv_pos : forall x y:R, 0 < x -> 0 < y -> 0 < x * / y.
intros x y H H0; try assumption.
replace 0 with (x * 0).
apply Rmult_lt_compat_l; auto with real.
ring.
Qed.

Lemma Rlt_zero_1 : 0 < 1.
exact Rlt_0_1.
Qed.

Lemma Rle_zero_pos_plus1 : forall x:R, 0 <= x -> 0 <= 1 + x.
intros x H; try assumption.
case H; intros.
red.
left; try assumption.
apply Rlt_zero_pos_plus1; auto with real.
rewrite <- H0.
replace (1 + 0) with 1.
red; left.
exact Rlt_zero_1.
ring.
Qed.

Lemma Rle_mult_inv_pos : forall x y:R, 0 <= x -> 0 < y -> 0 <= x * / y.
intros x y H H0; try assumption.
case H; intros.
red; left.
apply Rlt_mult_inv_pos; auto with real.
rewrite <- H1.
red; right; ring.
Qed.

Lemma Rle_zero_1 : 0 <= 1.
red; left.
exact Rlt_zero_1.
Qed.

Lemma Rle_not_lt : forall n d:R, 0 <= n * / d -> ~ 0 < - n * / d.
intros n d H; red; intros H0; try exact H0.
generalize (Rgt_not_le 0 (n * / d)).
intros H1; elim H1; try assumption.
replace (n * / d) with (- - (n * / d)).
replace 0 with (- -0).
replace (- (n * / d)) with (- n * / d).
replace (-0) with 0.
red.
apply Ropp_gt_lt_contravar.
red.
exact H0.
ring.
ring.
ring.
ring.
Qed.

Lemma Rnot_lt0 : forall x:R, ~ 0 < 0 * x.
intros x; try assumption.
replace (0 * x) with 0.
apply Rlt_irrefl.
ring.
Qed.

Lemma Rlt_not_le_frac_opp : forall n d:R, 0 < n * / d -> ~ 0 <= - n * / d.
intros n d H; try assumption.
apply Rgt_not_le.
replace 0 with (-0).
replace (- n * / d) with (- (n * / d)).
apply Ropp_lt_gt_contravar.
try exact H.
ring.
ring.
Qed.

Lemma Rnot_lt_lt : forall x y:R, ~ 0 < y - x -> ~ x < y.
unfold not; intros.
apply H.
apply Rplus_lt_reg_l with x.
replace (x + 0) with x.
replace (x + (y - x)) with y.
try exact H0.
ring.
ring.
Qed.

Lemma Rnot_le_le : forall x y:R, ~ 0 <= y - x -> ~ x <= y.
unfold not; intros.
apply H.
case H0; intros.
left.
apply Rplus_lt_reg_l with x.
replace (x + 0) with x.
replace (x + (y - x)) with y.
try exact H1.
ring.
ring.
right.
rewrite H1; ring.
Qed.

Lemma Rfourier_gt_to_lt : forall x y:R, y > x -> x < y.
unfold Rgt; intros; assumption.
Qed.

Lemma Rfourier_ge_to_le : forall x y:R, y >= x -> x <= y.
intros x y; exact (Rge_le y x).
Qed.

Lemma Rfourier_eqLR_to_le : forall x y:R, x = y -> x <= y.
exact Req_le.
Qed.

Lemma Rfourier_eqRL_to_le : forall x y:R, y = x -> x <= y.
exact Req_le_sym.
Qed.

Lemma Rfourier_not_ge_lt : forall x y:R, (x >= y -> False) -> x < y.
exact Rnot_ge_lt.
Qed.

Lemma Rfourier_not_gt_le : forall x y:R, (x > y -> False) -> x <= y.
exact Rnot_gt_le.
Qed.

Lemma Rfourier_not_le_gt : forall x y:R, (x <= y -> False) -> x > y.
exact Rnot_le_lt.
Qed.

Lemma Rfourier_not_lt_ge : forall x y:R, (x < y -> False) -> x >= y.
exact Rnot_lt_ge.
Qed.
