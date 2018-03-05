(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

Require Export NMulOrder.

Module Type NSubProp (Import N : NAxiomsMiniSig').
Include NMulOrderProp N.

Theorem sub_0_l : forall n, 0 - n == 0.
Proof.
induct n.
apply sub_0_r.
intros n IH; rewrite sub_succ_r; rewrite IH. now apply pred_0.
Qed.

Theorem sub_succ : forall n m, S n - S m == n - m.
Proof.
intro n; induct m.
rewrite sub_succ_r. do 2 rewrite sub_0_r. now rewrite pred_succ.
intros m IH. rewrite sub_succ_r. rewrite IH. now rewrite sub_succ_r.
Qed.

Theorem sub_diag : forall n, n - n == 0.
Proof.
induct n. apply sub_0_r. intros n IH; rewrite sub_succ; now rewrite IH.
Qed.

Theorem sub_gt : forall n m, n > m -> n - m ~= 0.
Proof.
intros n m H; elim H using lt_ind_rel; clear n m H.
solve_proper.
intro; rewrite sub_0_r; apply neq_succ_0.
intros; now rewrite sub_succ.
Qed.

Theorem add_sub_assoc : forall n m p, p <= m -> n + (m - p) == (n + m) - p.
Proof.
intros n m p; induct p.
intro; now do 2 rewrite sub_0_r.
intros p IH H. do 2 rewrite sub_succ_r.
rewrite <- IH by (apply lt_le_incl; now apply le_succ_l).
rewrite add_pred_r by (apply sub_gt; now apply le_succ_l).
reflexivity.
Qed.

Theorem sub_succ_l : forall n m, n <= m -> S m - n == S (m - n).
Proof.
intros n m H. rewrite <- (add_1_l m). rewrite <- (add_1_l (m - n)).
symmetry; now apply add_sub_assoc.
Qed.

Theorem add_sub : forall n m, (n + m) - m == n.
Proof.
intros n m. rewrite <- add_sub_assoc by (apply le_refl).
rewrite sub_diag; now rewrite add_0_r.
Qed.

Theorem sub_add : forall n m, n <= m -> (m - n) + n == m.
Proof.
intros n m H. rewrite add_comm. rewrite add_sub_assoc by assumption.
rewrite add_comm. apply add_sub.
Qed.

Theorem add_sub_eq_l : forall n m p, m + p == n -> n - m == p.
Proof.
intros n m p H. symmetry.
assert (H1 : m + p - m == n - m) by now rewrite H.
rewrite add_comm in H1. now rewrite add_sub in H1.
Qed.

Theorem add_sub_eq_r : forall n m p, m + p == n -> n - p == m.
Proof.
intros n m p H; rewrite add_comm in H; now apply add_sub_eq_l.
Qed.

(* This could be proved by adding m to both sides. Then the proof would
use add_sub_assoc and sub_0_le, which is proven below. *)

Theorem add_sub_eq_nz : forall n m p, p ~= 0 -> n - m == p -> m + p == n.
Proof.
intros n m p H; double_induct n m.
intros m H1; rewrite sub_0_l in H1. symmetry in H1; false_hyp H1 H.
intro n; rewrite sub_0_r; now rewrite add_0_l.
intros n m IH H1. rewrite sub_succ in H1. apply IH in H1.
rewrite add_succ_l; now rewrite H1.
Qed.

Theorem sub_add_distr : forall n m p, n - (m + p) == (n - m) - p.
Proof.
intros n m; induct p.
rewrite add_0_r; now rewrite sub_0_r.
intros p IH. rewrite add_succ_r; do 2 rewrite sub_succ_r. now rewrite IH.
Qed.

Theorem add_sub_swap : forall n m p, p <= n -> n + m - p == n - p + m.
Proof.
intros n m p H.
rewrite (add_comm n m).
rewrite <- add_sub_assoc by assumption.
now rewrite (add_comm m (n - p)).
Qed.

(** Sub and order *)

Theorem le_sub_l : forall n m, n - m <= n.
Proof.
intro n; induct m.
rewrite sub_0_r; now apply eq_le_incl.
intros m IH. rewrite sub_succ_r.
apply le_trans with (n - m); [apply le_pred_l | assumption].
Qed.

Theorem sub_0_le : forall n m, n - m == 0 <-> n <= m.
Proof.
double_induct n m.
intro m; split; intro; [apply le_0_l | apply sub_0_l].
intro m; rewrite sub_0_r; split; intro H;
[false_hyp H neq_succ_0 | false_hyp H nle_succ_0].
intros n m H. rewrite <- succ_le_mono. now rewrite sub_succ.
Qed.

Theorem sub_add_le : forall n m, n <= n - m + m.
Proof.
intros.
destruct (le_ge_cases n m) as [LE|GE].
rewrite <- sub_0_le in LE. rewrite LE; nzsimpl.
now rewrite <- sub_0_le.
rewrite sub_add by assumption. apply le_refl.
Qed.

Theorem le_sub_le_add_r : forall n m p,
 n - p <= m <-> n <= m + p.
Proof.
intros n m p.
split; intros LE.
rewrite (add_le_mono_r _ _ p) in LE.
apply le_trans with (n-p+p); auto using sub_add_le.
destruct (le_ge_cases n p) as [LE'|GE].
rewrite <- sub_0_le in LE'. rewrite LE'. apply le_0_l.
rewrite (add_le_mono_r _ _ p). now rewrite sub_add.
Qed.

Theorem le_sub_le_add_l : forall n m p, n - m <= p <-> n <= m + p.
Proof.
intros n m p. rewrite add_comm; apply le_sub_le_add_r.
Qed.

Theorem lt_sub_lt_add_r : forall n m p,
 n - p < m -> n < m + p.
Proof.
intros n m p LT.
rewrite (add_lt_mono_r _ _ p) in LT.
apply le_lt_trans with (n-p+p); auto using sub_add_le.
Qed.

(** Unfortunately, we do not have [n < m + p -> n - p < m].
    For instance [1<0+2] but not [1-2<0]. *)

Theorem lt_sub_lt_add_l : forall n m p, n - m < p -> n < m + p.
Proof.
intros n m p. rewrite add_comm; apply lt_sub_lt_add_r.
Qed.

Theorem le_add_le_sub_r : forall n m p, n + p <= m -> n <= m - p.
Proof.
intros n m p LE.
apply (add_le_mono_r _ _ p).
rewrite sub_add. assumption.
apply le_trans with (n+p); trivial.
rewrite <- (add_0_l p) at 1. rewrite <- add_le_mono_r. apply le_0_l.
Qed.

(** Unfortunately, we do not have [n <= m - p -> n + p <= m].
    For instance [0<=1-2] but not [2+0<=1]. *)

Theorem le_add_le_sub_l : forall n m p, n + p <= m -> p <= m - n.
Proof.
intros n m p. rewrite add_comm; apply le_add_le_sub_r.
Qed.

Theorem lt_add_lt_sub_r : forall n m p, n + p < m <-> n < m - p.
Proof.
intros n m p.
destruct (le_ge_cases p m) as [LE|GE].
rewrite <- (sub_add p m) at 1 by assumption.
now rewrite <- add_lt_mono_r.
assert (GE' := GE). rewrite <- sub_0_le in GE'; rewrite GE'.
split; intros LT.
elim (lt_irrefl m). apply le_lt_trans with (n+p); trivial.
 rewrite <- (add_0_l m). apply add_le_mono. apply le_0_l. assumption.
now elim (nlt_0_r n).
Qed.

Theorem lt_add_lt_sub_l : forall n m p, n + p < m <-> p < m - n.
Proof.
intros n m p. rewrite add_comm; apply lt_add_lt_sub_r.
Qed.

Theorem sub_lt : forall n m, m <= n -> 0 < m -> n - m < n.
Proof.
intros n m LE LT.
assert (LE' := le_sub_l n m). rewrite lt_eq_cases in LE'.
destruct LE' as [LT'|EQ]. assumption.
apply add_sub_eq_nz in EQ; [|order].
rewrite (add_lt_mono_r _ _ n), add_0_l in LT. order.
Qed.

Lemma sub_le_mono_r : forall n m p, n <= m -> n-p <= m-p.
Proof.
 intros. rewrite le_sub_le_add_r. transitivity m. assumption. apply sub_add_le.
Qed.

Lemma sub_le_mono_l : forall n m p, n <= m -> p-m <= p-n.
Proof.
 intros. rewrite le_sub_le_add_r.
 transitivity (p-n+n); [ apply sub_add_le | now apply add_le_mono_l].
Qed.

(** Sub and mul *)

Theorem mul_pred_r : forall n m, n * (P m) == n * m - n.
Proof.
intros n m; cases m.
now rewrite pred_0, mul_0_r, sub_0_l.
intro m; rewrite pred_succ, mul_succ_r, <- add_sub_assoc.
now rewrite sub_diag, add_0_r.
now apply eq_le_incl.
Qed.

Theorem mul_sub_distr_r : forall n m p, (n - m) * p == n * p - m * p.
Proof.
intros n m p; induct n.
now rewrite sub_0_l, mul_0_l, sub_0_l.
intros n IH. destruct (le_gt_cases m n) as [H | H].
rewrite sub_succ_l by assumption. do 2 rewrite mul_succ_l.
rewrite (add_comm ((n - m) * p) p), (add_comm (n * p) p).
rewrite <- (add_sub_assoc p (n * p) (m * p)) by now apply mul_le_mono_r.
now apply add_cancel_l.
assert (H1 : S n <= m); [now apply le_succ_l |].
setoid_replace (S n - m) with 0 by now apply sub_0_le.
setoid_replace ((S n * p) - m * p) with 0 by (apply sub_0_le; now apply mul_le_mono_r).
apply mul_0_l.
Qed.

Theorem mul_sub_distr_l : forall n m p, p * (n - m) == p * n - p * m.
Proof.
intros n m p; rewrite (mul_comm p (n - m)), (mul_comm p n), (mul_comm p m).
apply mul_sub_distr_r.
Qed.

(** Alternative definitions of [<=] and [<] based on [+] *)

Definition le_alt n m := exists p, p + n == m.
Definition lt_alt n m := exists p, S p + n == m.

Lemma le_equiv : forall n m, le_alt n m <-> n <= m.
Proof.
split.
intros (p,H). rewrite <- H, add_comm. apply le_add_r.
intro H. exists (m-n). now apply sub_add.
Qed.

Lemma lt_equiv : forall n m, lt_alt n m <-> n < m.
Proof.
split.
intros (p,H). rewrite <- H, add_succ_l, lt_succ_r, add_comm. apply le_add_r.
intro H. exists (m-S n). rewrite add_succ_l, <- add_succ_r.
apply sub_add. now rewrite le_succ_l.
Qed.

Instance le_alt_wd : Proper (eq==>eq==>iff) le_alt.
Proof.
 intros x x' Hx y y' Hy; unfold le_alt.
 setoid_rewrite Hx. setoid_rewrite Hy. auto with *.
Qed.

Instance lt_alt_wd : Proper (eq==>eq==>iff) lt_alt.
Proof.
 intros x x' Hx y y' Hy; unfold lt_alt.
 setoid_rewrite Hx. setoid_rewrite Hy. auto with *.
Qed.

(** With these alternative definition, the dichotomy:

[forall n m, n <= m \/ m <= n]

becomes:

[forall n m, (exists p, p + n == m) \/ (exists p, p + m == n)]

We will need this in the proof of induction principle for integers
constructed as pairs of natural numbers. This formula can be proved
from know properties of [<=]. However, it can also be done directly. *)

Theorem le_alt_dichotomy : forall n m, le_alt n m \/ le_alt m n.
Proof.
intros n m; induct n.
left; exists m; apply add_0_r.
intros n IH.
destruct IH as [[p H] | [p H]].
destruct (zero_or_succ p) as [H1 | [p' H1]]; rewrite H1 in H.
rewrite add_0_l in H. right; exists (S 0); rewrite H, add_succ_l;
 now rewrite add_0_l.
left; exists p'; rewrite add_succ_r; now rewrite add_succ_l in H.
right; exists (S p). rewrite add_succ_l; now rewrite H.
Qed.

Theorem add_dichotomy :
  forall n m, (exists p, p + n == m) \/ (exists p, p + m == n).
Proof. exact le_alt_dichotomy. Qed.

End NSubProp.

