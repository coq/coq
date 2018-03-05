(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import BinInt Znat.
Local Open Scope Z_scope.

(** Factorization lemmas *)

Theorem Zred_factor0 n : n = n * 1.
Proof.
  now Z.nzsimpl.
Qed.

Theorem Zred_factor1 n : n + n = n * 2.
Proof.
  rewrite Z.mul_comm. apply Z.add_diag.
Qed.

Theorem Zred_factor2 n m : n + n * m = n * (1 + m).
Proof.
  rewrite Z.mul_add_distr_l; now Z.nzsimpl.
Qed.

Theorem Zred_factor3 n m : n * m + n = n * (1 + m).
Proof.
  now Z.nzsimpl.
Qed.

Theorem Zred_factor4 n m p : n * m + n * p = n * (m + p).
Proof.
  symmetry; apply Z.mul_add_distr_l.
Qed.

Theorem Zred_factor5 n m : n * 0 + m = m.
Proof.
  now Z.nzsimpl.
Qed.

Theorem Zred_factor6 n : n = n + 0.
Proof.
  now Z.nzsimpl.
Qed.

(** Other specific variants of theorems dedicated for the Omega tactic *)

Lemma new_var : forall x : Z, exists y : Z, x = y.
Proof.
intros x; now exists x.
Qed.

Lemma OMEGA1 x y : x = y -> 0 <= x -> 0 <= y.
Proof.
now intros ->.
Qed.

Lemma OMEGA2 x y : 0 <= x -> 0 <= y -> 0 <= x + y.
Proof.
Z.order_pos.
Qed.

Lemma OMEGA3 x y k : k > 0 -> x = y * k -> x = 0 -> y = 0.
Proof.
intros LT -> EQ. apply Z.mul_eq_0 in EQ. destruct EQ; now subst.
Qed.

Lemma OMEGA4 x y z : x > 0 -> y > x -> z * y + x <> 0.
Proof.
Z.swap_greater. intros Hx Hxy.
rewrite Z.add_move_0_l, <- Z.mul_opp_l.
destruct (Z.lt_trichotomy (-z) 1) as [LT|[->|GT]].
- intro. revert LT. apply Z.le_ngt, (Z.le_succ_l 0).
  apply Z.mul_pos_cancel_r with y; Z.order.
- Z.nzsimpl. Z.order.
- rewrite (Z.mul_lt_mono_pos_r y), Z.mul_1_l in GT; Z.order.
Qed.

Lemma OMEGA5 x y z : x = 0 -> y = 0 -> x + y * z = 0.
Proof.
now intros -> ->.
Qed.

Lemma OMEGA6 x y z : 0 <= x -> y = 0 -> 0 <= x + y * z.
Proof.
intros H ->. now Z.nzsimpl.
Qed.

Lemma OMEGA7 x y z t :
 z > 0 -> t > 0 -> 0 <= x -> 0 <= y -> 0 <= x * z + y * t.
Proof.
intros. Z.swap_greater. Z.order_pos.
Qed.

Lemma OMEGA8 x y : 0 <= x -> 0 <= y -> x = - y -> x = 0.
Proof.
intros H1 H2 H3. rewrite <- Z.opp_nonpos_nonneg in H2. Z.order.
Qed.

Lemma OMEGA9 x y z t : y = 0 -> x = z -> y + (- x + z) * t = 0.
Proof.
intros. subst. now rewrite Z.add_opp_diag_l.
Qed.

Lemma OMEGA10 v c1 c2 l1 l2 k1 k2 :
 (v * c1 + l1) * k1 + (v * c2 + l2) * k2 =
 v * (c1 * k1 + c2 * k2) + (l1 * k1 + l2 * k2).
Proof.
rewrite ?Z.mul_add_distr_r, ?Z.mul_add_distr_l, ?Z.mul_assoc.
rewrite <- !Z.add_assoc. f_equal. apply Z.add_shuffle3.
Qed.

Lemma OMEGA11 v1 c1 l1 l2 k1 :
 (v1 * c1 + l1) * k1 + l2 = v1 * (c1 * k1) + (l1 * k1 + l2).
Proof.
rewrite ?Z.mul_add_distr_r, ?Z.mul_add_distr_l, ?Z.mul_assoc.
now rewrite Z.add_assoc.
Qed.

Lemma OMEGA12 v2 c2 l1 l2 k2 :
 l1 + (v2 * c2 + l2) * k2 = v2 * (c2 * k2) + (l1 + l2 * k2).
Proof.
rewrite ?Z.mul_add_distr_r, ?Z.mul_add_distr_l, ?Z.mul_assoc.
apply Z.add_shuffle3.
Qed.

Lemma OMEGA13 (v l1 l2 : Z) (x : positive) :
 v * Zpos x + l1 + (v * Zneg x + l2) = l1 + l2.
Proof.
 rewrite Z.add_shuffle1.
 rewrite <- Z.mul_add_distr_l, <- Pos2Z.opp_neg, Z.add_opp_diag_r.
 now Z.nzsimpl.
Qed.

Lemma OMEGA14 (v l1 l2 : Z) (x : positive) :
 v * Zneg x + l1 + (v * Zpos x + l2) = l1 + l2.
Proof.
 rewrite Z.add_shuffle1.
 rewrite <- Z.mul_add_distr_l, <- Pos2Z.opp_neg, Z.add_opp_diag_r.
 now Z.nzsimpl.
Qed.

Lemma OMEGA15 v c1 c2 l1 l2 k2 :
 v * c1 + l1 + (v * c2 + l2) * k2 = v * (c1 + c2 * k2) + (l1 + l2 * k2).
Proof.
 rewrite ?Z.mul_add_distr_r, ?Z.mul_add_distr_l, ?Z.mul_assoc.
 apply Z.add_shuffle1.
Qed.

Lemma OMEGA16 v c l k : (v * c + l) * k = v * (c * k) + l * k.
Proof.
 now rewrite ?Z.mul_add_distr_r, ?Z.mul_add_distr_l, ?Z.mul_assoc.
Qed.

Lemma OMEGA17 x y z : Zne x 0 -> y = 0 -> Zne (x + y * z) 0.
Proof.
 unfold Zne, not. intros NE EQ. subst. now Z.nzsimpl.
Qed.

Lemma OMEGA18 x y k : x = y * k -> Zne x 0 -> Zne y 0.
Proof.
 unfold Zne, not. intros. subst; auto.
Qed.

Lemma OMEGA19 x : Zne x 0 -> 0 <= x + -1 \/ 0 <= x * -1 + -1.
Proof.
 unfold Zne. intros Hx. apply Z.lt_gt_cases in Hx.
 destruct Hx as [LT|GT].
 - right. change (-1) with (-(1)).
   rewrite Z.mul_opp_r, <- Z.opp_add_distr. Z.nzsimpl.
   rewrite Z.opp_nonneg_nonpos. now apply Z.le_succ_l.
 - left. now apply Z.lt_le_pred.
Qed.

Lemma OMEGA20 x y z : Zne x 0 -> y = 0 -> Zne (x + y * z) 0.
Proof.
 unfold Zne, not. intros H1 H2 H3; apply H1; rewrite H2 in H3;
 simpl in H3; rewrite Z.add_0_r in H3; trivial with arith.
Qed.

Definition fast_Zplus_comm (x y : Z) (P : Z -> Prop)
  (H : P (y + x)) := eq_ind_r P H (Z.add_comm x y).

Definition fast_Zplus_assoc_reverse (n m p : Z) (P : Z -> Prop)
  (H : P (n + (m + p))) := eq_ind_r P H (Zplus_assoc_reverse n m p).

Definition fast_Zplus_assoc (n m p : Z) (P : Z -> Prop)
  (H : P (n + m + p)) := eq_ind_r P H (Z.add_assoc n m p).

Definition fast_Zplus_permute (n m p : Z) (P : Z -> Prop)
  (H : P (m + (n + p))) := eq_ind_r P H (Z.add_shuffle3 n m p).

Definition fast_OMEGA10 (v c1 c2 l1 l2 k1 k2 : Z) (P : Z -> Prop)
  (H : P (v * (c1 * k1 + c2 * k2) + (l1 * k1 + l2 * k2))) :=
  eq_ind_r P H (OMEGA10 v c1 c2 l1 l2 k1 k2).

Definition fast_OMEGA11 (v1 c1 l1 l2 k1 : Z) (P : Z -> Prop)
  (H : P (v1 * (c1 * k1) + (l1 * k1 + l2))) :=
  eq_ind_r P H (OMEGA11 v1 c1 l1 l2 k1).
Definition fast_OMEGA12 (v2 c2 l1 l2 k2 : Z) (P : Z -> Prop)
  (H : P (v2 * (c2 * k2) + (l1 + l2 * k2))) :=
  eq_ind_r P H (OMEGA12 v2 c2 l1 l2 k2).

Definition fast_OMEGA15 (v c1 c2 l1 l2 k2 : Z) (P : Z -> Prop)
  (H : P (v * (c1 + c2 * k2) + (l1 + l2 * k2))) :=
  eq_ind_r P H (OMEGA15 v c1 c2 l1 l2 k2).
Definition fast_OMEGA16 (v c l k : Z) (P : Z -> Prop)
  (H : P (v * (c * k) + l * k)) := eq_ind_r P H (OMEGA16 v c l k).

Definition fast_OMEGA13 (v l1 l2 : Z) (x : positive) (P : Z -> Prop)
  (H : P (l1 + l2)) := eq_ind_r P H (OMEGA13 v l1 l2 x).

Definition fast_OMEGA14 (v l1 l2 : Z) (x : positive) (P : Z -> Prop)
  (H : P (l1 + l2)) := eq_ind_r P H (OMEGA14 v l1 l2 x).
Definition fast_Zred_factor0 (x : Z) (P : Z -> Prop)
  (H : P (x * 1)) := eq_ind_r P H (Zred_factor0 x).

Definition fast_Zopp_eq_mult_neg_1 (x : Z) (P : Z -> Prop)
  (H : P (x * -1)) := eq_ind_r P H (Z.opp_eq_mul_m1 x).

Definition fast_Zmult_comm (x y : Z) (P : Z -> Prop)
  (H : P (y * x)) := eq_ind_r P H (Z.mul_comm x y).

Definition fast_Zopp_plus_distr (x y : Z) (P : Z -> Prop)
  (H : P (- x + - y)) := eq_ind_r P H (Z.opp_add_distr x y).

Definition fast_Zopp_involutive (x : Z) (P : Z -> Prop) (H : P x) :=
  eq_ind_r P H (Z.opp_involutive x).

Definition fast_Zopp_mult_distr_r (x y : Z) (P : Z -> Prop)
  (H : P (x * - y)) := eq_ind_r P H (Zopp_mult_distr_r x y).

Definition fast_Zmult_plus_distr_l (n m p : Z) (P : Z -> Prop)
  (H : P (n * p + m * p)) := eq_ind_r P H (Z.mul_add_distr_r n m p).
Definition fast_Zmult_opp_comm (x y : Z) (P : Z -> Prop)
  (H : P (x * - y)) := eq_ind_r P H (Z.mul_opp_comm x y).

Definition fast_Zmult_assoc_reverse (n m p : Z) (P : Z -> Prop)
  (H : P (n * (m * p))) := eq_ind_r P H (Zmult_assoc_reverse n m p).

Definition fast_Zred_factor1 (x : Z) (P : Z -> Prop)
  (H : P (x * 2)) := eq_ind_r P H (Zred_factor1 x).

Definition fast_Zred_factor2 (x y : Z) (P : Z -> Prop)
  (H : P (x * (1 + y))) := eq_ind_r P H (Zred_factor2 x y).

Definition fast_Zred_factor3 (x y : Z) (P : Z -> Prop)
  (H : P (x * (1 + y))) := eq_ind_r P H (Zred_factor3 x y).

Definition fast_Zred_factor4 (x y z : Z) (P : Z -> Prop)
  (H : P (x * (y + z))) := eq_ind_r P H (Zred_factor4 x y z).

Definition fast_Zred_factor5 (x y : Z) (P : Z -> Prop)
  (H : P y) := eq_ind_r P H (Zred_factor5 x y).

Definition fast_Zred_factor6 (x : Z) (P : Z -> Prop)
  (H : P (x + 0)) := eq_ind_r P H (Zred_factor6 x).

Theorem intro_Z :
  forall n:nat,  exists y : Z, Z.of_nat n = y /\ 0 <= y * 1 + 0.
Proof.
  intros n; exists (Z.of_nat n); split; trivial.
  rewrite Z.mul_1_r, Z.add_0_r. apply Nat2Z.is_nonneg.
Qed.
