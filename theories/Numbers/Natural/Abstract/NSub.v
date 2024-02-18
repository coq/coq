(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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
Proof. exact (Private_nat_sub_0_l pred_0). Qed.

Theorem sub_gt : forall n m, n > m -> n - m ~= 0.
Proof. intros n m H%lt_0_sub%lt_neq; apply neq_sym; exact H. Qed.

Theorem add_sub_assoc : forall n m p, p <= m -> n + (m - p) == (n + m) - p.
Proof.
  intros n m p I; apply (add_cancel_r _ _ p); rewrite <-add_assoc.
  rewrite 2!Private_sub_add; [reflexivity | | exact I].
  rewrite <-(add_0_l p); apply add_le_mono; [exact (le_0_l _) | exact I].
Qed.

Theorem sub_succ_l : forall n m, n <= m -> S m - n == S (m - n).
Proof.
intros n m H. rewrite <- (add_1_l m). rewrite <- (add_1_l (m - n)).
symmetry; now apply add_sub_assoc.
Qed.

Theorem sub_add : forall n m, n <= m -> (m - n) + n == m.
Proof. exact Private_sub_add. Qed.

(* This could be proved by adding m to both sides. Then the proof would
use add_sub_assoc and sub_0_le, which is proven below. *)

Theorem add_sub_eq_nz : forall n m p, p ~= 0 -> n - m == p -> m + p == n.
Proof.
intros n m p H; double_induct n m.
- intros m H1; rewrite sub_0_l in H1. symmetry in H1; false_hyp H1 H.
- intro n; rewrite sub_0_r; now rewrite add_0_l.
- intros n m IH H1. rewrite sub_succ in H1. apply IH in H1.
  rewrite add_succ_l; now rewrite H1.
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
intros n m; induct m.
- rewrite sub_0_r; now apply eq_le_incl.
- intros m IH. rewrite sub_succ_r.
  apply le_trans with (n - m); [apply le_pred_l | assumption].
Qed.

Theorem sub_0_le : forall n m, n - m == 0 <-> n <= m.
Proof. exact (Private_nat_sub_0_le pred_0). Qed.

Theorem sub_pred_l : forall n m, P n - m == P (n - m).
Proof.
intros n m; destruct (zero_or_succ n) as [-> | [k ->]].
- rewrite pred_0, sub_0_l, pred_0; reflexivity.
- rewrite pred_succ; destruct (lt_ge_cases k m) as [H | H].
  + pose proof H as H'. apply lt_le_incl in H' as ->%sub_0_le.
    apply le_succ_l, sub_0_le in H as ->; rewrite pred_0; reflexivity.
  + rewrite sub_succ_l, pred_succ by (exact H); reflexivity.
Qed.

Theorem sub_pred_r : forall n m, m ~= 0 -> m <= n -> n - P m == S (n - m).
Proof.
intros n m H H'; destruct (zero_or_succ m) as [[]%H | [k Hk]]; rewrite Hk in *.
rewrite pred_succ, sub_succ_r, succ_pred; [reflexivity |].
apply sub_gt, le_succ_l; exact H'.
Qed.

Theorem sub_add_le : forall n m, n <= n - m + m.
Proof. exact Private_sub_add_le. Qed.

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
rewrite sub_add.
- assumption.
- apply le_trans with (n+p); trivial.
  rewrite <- (add_0_l p) at 1. rewrite <- add_le_mono_r. apply le_0_l.
Qed.

(** Unfortunately, we do not have [n <= m - p -> n + p <= m].
    For instance [0<=1-2] but not [2+0<=1]. *)

Theorem le_add_le_sub_l : forall n m p, n + p <= m -> p <= m - n.
Proof.
intros n m p. rewrite add_comm; apply le_add_le_sub_r.
Qed.

Theorem sub_lt : forall n m, m <= n -> 0 < m -> n - m < n.
Proof.
intros n m LE LT.
assert (LE' := le_sub_l n m). rewrite lt_eq_cases in LE'.
destruct LE' as [LT'|EQ].
- assumption.
- apply add_sub_eq_nz in EQ; [|order].
  rewrite (add_lt_mono_r _ _ n), add_0_l in LT. order.
Qed.

Lemma sub_le_mono_r : forall n m p, n <= m -> n-p <= m-p.
Proof.
 intros n m p. rewrite le_sub_le_add_r.
 transitivity m.
 - assumption.
 - apply sub_add_le.
Qed.

Lemma sub_le_mono_l : forall n m p, n <= m -> p-m <= p-n.
Proof.
 intros n m p. rewrite le_sub_le_add_r.
 transitivity (p-n+n); [ apply sub_add_le | now apply add_le_mono_l].
Qed.

Theorem sub_sub_distr :
  forall n m p, p <= m -> m <= n -> n - (m - p) == (n - m) + p.
Proof.
  intros n m p; revert n m; induct p.
  - intros n m _ _; rewrite add_0_r, sub_0_r; reflexivity.
  - intros p IH n m H1 H2; rewrite add_succ_r.
    destruct (zero_or_succ m) as [Hm | [k Hk]].
    + contradict H1; rewrite Hm; exact (nle_succ_0 _).
    + rewrite Hk in *; clear m Hk; rewrite sub_succ; apply <-succ_le_mono in H1.
      assert (n - k ~= 0) as ne by (apply sub_gt, le_succ_l; exact H2).
      rewrite sub_succ_r, add_pred_l by (exact ne).
      rewrite succ_pred by (intros [[]%ne _]%eq_add_0).
      apply IH with (1 := H1), le_trans with (2 := H2).
      exact (le_succ_diag_r _).
Qed.

(* TODO: deprecate this part in 8.20 and remove it in 8.22 *)
(** Alternative definitions of [<=] and [<] based on [+] *)

Definition le_alt n m := exists p, p + n == m.
Definition lt_alt n m := exists p, S p + n == m.

Lemma le_equiv : forall n m, le_alt n m <-> n <= m.
Proof.
intros n m; split.
- intros (p,H). rewrite <- H, add_comm. apply le_add_r.
- intro H. exists (m-n). now apply sub_add.
Qed.

Lemma lt_equiv : forall n m, lt_alt n m <-> n < m.
Proof.
intros n m; split.
- intros (p,H). rewrite <- H, add_succ_l, lt_succ_r, add_comm. apply le_add_r.
- intro H. exists (m-S n). rewrite add_succ_l, <- add_succ_r.
  apply sub_add. now rewrite le_succ_l.
Qed.

#[global]
Instance le_alt_wd : Proper (eq==>eq==>iff) le_alt.
Proof.
 intros x x' Hx y y' Hy; unfold le_alt.
 setoid_rewrite Hx. setoid_rewrite Hy. auto with *.
Qed.

#[global]
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
- left; exists m; apply add_0_r.
- intros n IH.
  destruct IH as [[p H] | [p H]].
  + destruct (zero_or_succ p) as [H1 | [p' H1]]; rewrite H1 in H.
    * rewrite add_0_l in H. right; exists (S 0); rewrite H, add_succ_l;
      now rewrite add_0_l.
    * left; exists p'; rewrite add_succ_r; now rewrite add_succ_l in H.
  + right; exists (S p). rewrite add_succ_l; now rewrite H.
Qed.

Theorem add_dichotomy :
  forall n m, (exists p, p + n == m) \/ (exists p, p + m == n).
Proof. exact le_alt_dichotomy. Qed.

End NSubProp.

