(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Rbase.
Require Import Rfunctions.
Require Import SeqSeries.
Require Import Rtrigo1.
Require Import Ranalysis1.
Require Import PSeries_reg.
Require Import Div2.
Require Import Even.
Require Import Max.
Require Import Omega.
Local Open Scope nat_scope.
Local Open Scope R_scope.

Definition E1 (x:R) (N:nat) : R :=
  sum_f_R0 (fun k:nat => / INR (fact k) * x ^ k) N.

Lemma E1_cvg : forall x:R, Un_cv (E1 x) (exp x).
Proof.
  intro; unfold exp; unfold projT1.
  case (exist_exp x); intro.
  unfold exp_in, Un_cv; unfold infinite_sum, E1; trivial.
Qed.

Definition Reste_E (x y:R) (N:nat) : R :=
  sum_f_R0
  (fun k:nat =>
    sum_f_R0
    (fun l:nat =>
      / INR (fact (S (l + k))) * x ^ S (l + k) *
      (/ INR (fact (N - l)) * y ^ (N - l))) (
        pred (N - k))) (pred N).

Lemma exp_form :
  forall (x y:R) (n:nat),
    (0 < n)%nat -> E1 x n * E1 y n - Reste_E x y n = E1 (x + y) n.
Proof.
  intros; unfold E1.
  rewrite cauchy_finite.
  unfold Reste_E; unfold Rminus; rewrite Rplus_assoc;
    rewrite Rplus_opp_r; rewrite Rplus_0_r; apply sum_eq;
      intros.
  rewrite binomial.
  rewrite scal_sum; apply sum_eq; intros.
  unfold C; unfold Rdiv; repeat rewrite Rmult_assoc;
    rewrite (Rmult_comm (INR (fact i))); repeat rewrite Rmult_assoc;
      rewrite <- Rinv_l_sym.
  rewrite Rmult_1_r; rewrite Rinv_mult_distr.
  ring.
  apply INR_fact_neq_0.
  apply INR_fact_neq_0.
  apply INR_fact_neq_0.
  apply H.
Qed.

Definition maj_Reste_E (x y:R) (N:nat) : R :=
  4 *
  (Rmax 1 (Rmax (Rabs x) (Rabs y)) ^ (2 * N) /
    Rsqr (INR (fact (div2 (pred N))))).

(**********)
Lemma div2_double : forall N:nat, div2 (2 * N) = N.
Proof.
  intro; induction  N as [| N HrecN].
  reflexivity.
  replace (2 * S N)%nat with (S (S (2 * N))).
  simpl; simpl in HrecN; rewrite HrecN; reflexivity.
  ring.
Qed.

Lemma div2_S_double : forall N:nat, div2 (S (2 * N)) = N.
Proof.
  intro; induction  N as [| N HrecN].
  reflexivity.
  replace (2 * S N)%nat with (S (S (2 * N))).
  simpl; simpl in HrecN; rewrite HrecN; reflexivity.
  ring.
Qed.

Lemma div2_not_R0 : forall N:nat, (1 < N)%nat -> (0 < div2 N)%nat.
Proof.
  intros; induction N as [| N HrecN].
  - elim (lt_n_O _ H).
  - cut ((1 < N)%nat \/ N = 1%nat).
    { intro; elim H0; intro.
      + destruct (even_odd_dec N) as [Heq|Heq].
        * rewrite <- (even_div2 _ Heq); apply HrecN; assumption.
        * rewrite <- (odd_div2 _ Heq); apply lt_O_Sn.
      + rewrite H1; simpl; apply lt_O_Sn. }
    inversion H.
    right; reflexivity.
    left; apply lt_le_trans with 2%nat; [ apply lt_n_Sn | apply H1 ].
Qed.

Lemma Reste_E_maj :
  forall (x y:R) (N:nat),
    (0 < N)%nat -> Rabs (Reste_E x y N) <= maj_Reste_E x y N.
Proof.
  intros; set (M := Rmax 1 (Rmax (Rabs x) (Rabs y))).
  apply Rle_trans with
    (M ^ (2 * N) *
      sum_f_R0
      (fun k:nat =>
        sum_f_R0 (fun l:nat => / Rsqr (INR (fact (div2 (S N)))))
        (pred (N - k))) (pred N)).
  unfold Reste_E.
  apply Rle_trans with
    (sum_f_R0
      (fun k:nat =>
        Rabs
        (sum_f_R0
          (fun l:nat =>
            / INR (fact (S (l + k))) * x ^ S (l + k) *
            (/ INR (fact (N - l)) * y ^ (N - l))) (
              pred (N - k)))) (pred N)).
  apply
    (Rsum_abs
      (fun k:nat =>
        sum_f_R0
        (fun l:nat =>
          / INR (fact (S (l + k))) * x ^ S (l + k) *
          (/ INR (fact (N - l)) * y ^ (N - l))) (
            pred (N - k))) (pred N)).
  apply Rle_trans with
    (sum_f_R0
      (fun k:nat =>
        sum_f_R0
        (fun l:nat =>
          Rabs
          (/ INR (fact (S (l + k))) * x ^ S (l + k) *
            (/ INR (fact (N - l)) * y ^ (N - l)))) (
              pred (N - k))) (pred N)).
  apply sum_Rle; intros.
  apply
    (Rsum_abs
      (fun l:nat =>
        / INR (fact (S (l + n))) * x ^ S (l + n) *
        (/ INR (fact (N - l)) * y ^ (N - l)))).
  apply Rle_trans with
    (sum_f_R0
      (fun k:nat =>
        sum_f_R0
        (fun l:nat =>
          M ^ (2 * N) * / INR (fact (S l)) * / INR (fact (N - l)))
        (pred (N - k))) (pred N)).
  apply sum_Rle; intros.
  apply sum_Rle; intros.
  repeat rewrite Rabs_mult.
  do 2 rewrite <- RPow_abs.
  rewrite (Rabs_right (/ INR (fact (S (n0 + n))))).
  rewrite (Rabs_right (/ INR (fact (N - n0)))).
  replace
  (/ INR (fact (S (n0 + n))) * Rabs x ^ S (n0 + n) *
    (/ INR (fact (N - n0)) * Rabs y ^ (N - n0))) with
  (/ INR (fact (N - n0)) * / INR (fact (S (n0 + n))) * Rabs x ^ S (n0 + n) *
    Rabs y ^ (N - n0)); [ idtac | ring ].
  rewrite <- (Rmult_comm (/ INR (fact (N - n0)))).
  repeat rewrite Rmult_assoc.
  apply Rmult_le_compat_l.
  left; apply Rinv_0_lt_compat; apply INR_fact_lt_0.
  apply Rle_trans with
    (/ INR (fact (S n0)) * Rabs x ^ S (n0 + n) * Rabs y ^ (N - n0)).
  rewrite (Rmult_comm (/ INR (fact (S (n0 + n)))));
    rewrite (Rmult_comm (/ INR (fact (S n0)))); repeat rewrite Rmult_assoc;
      apply Rmult_le_compat_l.
  apply pow_le; apply Rabs_pos.
  rewrite (Rmult_comm (/ INR (fact (S n0)))); apply Rmult_le_compat_l.
  apply pow_le; apply Rabs_pos.
  apply Rinv_le_contravar.
  apply INR_fact_lt_0.
  apply le_INR; apply fact_le; apply le_n_S.
  apply le_plus_l.
  rewrite (Rmult_comm (M ^ (2 * N))); rewrite Rmult_assoc;
    apply Rmult_le_compat_l.
  left; apply Rinv_0_lt_compat; apply INR_fact_lt_0.
  apply Rle_trans with (M ^ S (n0 + n) * Rabs y ^ (N - n0)).
  do 2 rewrite <- (Rmult_comm (Rabs y ^ (N - n0))).
  apply Rmult_le_compat_l.
  apply pow_le; apply Rabs_pos.
  apply pow_incr; split.
  apply Rabs_pos.
  apply Rle_trans with (Rmax (Rabs x) (Rabs y)).
  apply RmaxLess1.
  unfold M; apply RmaxLess2.
  apply Rle_trans with (M ^ S (n0 + n) * M ^ (N - n0)).
  apply Rmult_le_compat_l.
  apply pow_le; apply Rle_trans with 1.
  left; apply Rlt_0_1.
  unfold M; apply RmaxLess1.
  apply pow_incr; split.
  apply Rabs_pos.
  apply Rle_trans with (Rmax (Rabs x) (Rabs y)).
  apply RmaxLess2.
  unfold M; apply RmaxLess2.
  rewrite <- pow_add; replace (S (n0 + n) + (N - n0))%nat with (N + S n)%nat.
  apply Rle_pow.
  unfold M; apply RmaxLess1.
  replace (2 * N)%nat with (N + N)%nat; [ idtac | ring ].
  apply plus_le_compat_l.
  replace N with (S (pred N)).
  apply le_n_S; apply H0.
  symmetry ; apply S_pred with 0%nat; apply H.
  apply INR_eq; do 2 rewrite plus_INR; do 2 rewrite S_INR; rewrite plus_INR;
    rewrite minus_INR.
  ring.
  apply le_trans with (pred (N - n)).
  apply H1.
  apply le_S_n.
  replace (S (pred (N - n))) with (N - n)%nat.
  apply le_trans with N.
  apply (fun p n m:nat => plus_le_reg_l n m p) with n.
  rewrite <- le_plus_minus.
  apply le_plus_r.
  apply le_trans with (pred N).
  apply H0.
  apply le_pred_n.
  apply le_n_Sn.
  apply S_pred with 0%nat.
  apply plus_lt_reg_l with n.
  rewrite <- le_plus_minus.
  replace (n + 0)%nat with n; [ idtac | ring ].
  apply le_lt_trans with (pred N).
  apply H0.
  apply lt_pred_n_n.
  apply H.
  apply le_trans with (pred N).
  apply H0.
  apply le_pred_n.
  apply Rle_ge; left; apply Rinv_0_lt_compat; apply INR_fact_lt_0.
  apply Rle_ge; left; apply Rinv_0_lt_compat; apply INR_fact_lt_0.
  rewrite scal_sum.
  apply sum_Rle; intros.
  rewrite <- Rmult_comm.
  rewrite scal_sum.
  apply sum_Rle; intros.
  rewrite (Rmult_comm (/ Rsqr (INR (fact (div2 (S N)))))).
  rewrite Rmult_assoc; apply Rmult_le_compat_l.
  apply pow_le.
  apply Rle_trans with 1.
  left; apply Rlt_0_1.
  unfold M; apply RmaxLess1.
  assert (H2 := even_odd_cor N).
  elim H2; intros N0 H3.
  elim H3; intro.
  apply Rle_trans with (/ INR (fact n0) * / INR (fact (N - n0))).
  do 2 rewrite <- (Rmult_comm (/ INR (fact (N - n0)))).
  apply Rmult_le_compat_l.
  left; apply Rinv_0_lt_compat; apply INR_fact_lt_0.
  apply Rinv_le_contravar.
  apply INR_fact_lt_0.
  apply le_INR.
  apply fact_le.
  apply le_n_Sn.
  replace (/ INR (fact n0) * / INR (fact (N - n0))) with
  (C N n0 / INR (fact N)).
  pattern N at 1; rewrite H4.
  apply Rle_trans with (C N N0 / INR (fact N)).
  unfold Rdiv; do 2 rewrite <- (Rmult_comm (/ INR (fact N))).
  apply Rmult_le_compat_l.
  left; apply Rinv_0_lt_compat; apply INR_fact_lt_0.
  rewrite H4.
  apply C_maj.
  rewrite <- H4; apply le_trans with (pred (N - n)).
  apply H1.
  apply le_S_n.
  replace (S (pred (N - n))) with (N - n)%nat.
  apply le_trans with N.
  apply (fun p n m:nat => plus_le_reg_l n m p) with n.
  rewrite <- le_plus_minus.
  apply le_plus_r.
  apply le_trans with (pred N).
  apply H0.
  apply le_pred_n.
  apply le_n_Sn.
  apply S_pred with 0%nat.
  apply plus_lt_reg_l with n.
  rewrite <- le_plus_minus.
  replace (n + 0)%nat with n; [ idtac | ring ].
  apply le_lt_trans with (pred N).
  apply H0.
  apply lt_pred_n_n.
  apply H.
  apply le_trans with (pred N).
  apply H0.
  apply le_pred_n.
  replace (C N N0 / INR (fact N)) with (/ Rsqr (INR (fact N0))).
  rewrite H4; rewrite div2_S_double; right; reflexivity.
  unfold Rsqr, C, Rdiv.
  repeat rewrite Rinv_mult_distr.
  rewrite (Rmult_comm (INR (fact N))).
  repeat rewrite Rmult_assoc.
  rewrite <- Rinv_r_sym.
  rewrite Rmult_1_r; replace (N - N0)%nat with N0.
  ring.
  replace N with (N0 + N0)%nat.
  symmetry ; apply minus_plus.
  rewrite H4.
  ring.
  apply INR_fact_neq_0.
  apply INR_fact_neq_0.
  apply INR_fact_neq_0.
  apply INR_fact_neq_0.
  apply INR_fact_neq_0.
  unfold C, Rdiv.
  rewrite (Rmult_comm (INR (fact N))).
  repeat rewrite Rmult_assoc.
  rewrite <- Rinv_r_sym.
  rewrite Rinv_mult_distr.
  rewrite Rmult_1_r; ring.
  apply INR_fact_neq_0.
  apply INR_fact_neq_0.
  apply INR_fact_neq_0.
  replace (/ INR (fact (S n0)) * / INR (fact (N - n0))) with
  (C (S N) (S n0) / INR (fact (S N))).
  apply Rle_trans with (C (S N) (S N0) / INR (fact (S N))).
  unfold Rdiv; do 2 rewrite <- (Rmult_comm (/ INR (fact (S N)))).
  apply Rmult_le_compat_l.
  left; apply Rinv_0_lt_compat; apply INR_fact_lt_0.
  cut (S N = (2 * S N0)%nat).
  intro; rewrite H5; apply C_maj.
  rewrite <- H5; apply le_n_S.
  apply le_trans with (pred (N - n)).
  apply H1.
  apply le_S_n.
  replace (S (pred (N - n))) with (N - n)%nat.
  apply le_trans with N.
  apply (fun p n m:nat => plus_le_reg_l n m p) with n.
  rewrite <- le_plus_minus.
  apply le_plus_r.
  apply le_trans with (pred N).
  apply H0.
  apply le_pred_n.
  apply le_n_Sn.
  apply S_pred with 0%nat.
  apply plus_lt_reg_l with n.
  rewrite <- le_plus_minus.
  replace (n + 0)%nat with n; [ idtac | ring ].
  apply le_lt_trans with (pred N).
  apply H0.
  apply lt_pred_n_n.
  apply H.
  apply le_trans with (pred N).
  apply H0.
  apply le_pred_n.
  rewrite H4; ring.
  cut (S N = (2 * S N0)%nat).
  intro.
  replace (C (S N) (S N0) / INR (fact (S N))) with (/ Rsqr (INR (fact (S N0)))).
  rewrite H5; rewrite div2_double.
  right; reflexivity.
  unfold Rsqr, C, Rdiv.
  repeat rewrite Rinv_mult_distr.
  replace (S N - S N0)%nat with (S N0).
  rewrite (Rmult_comm (INR (fact (S N)))).
  repeat rewrite Rmult_assoc.
  rewrite <- Rinv_r_sym.
  rewrite Rmult_1_r; reflexivity.
  apply INR_fact_neq_0.
  replace (S N) with (S N0 + S N0)%nat.
  symmetry ; apply minus_plus.
  rewrite H5; ring.
  apply INR_fact_neq_0.
  apply INR_fact_neq_0.
  apply INR_fact_neq_0.
  apply INR_fact_neq_0.
  rewrite H4; ring.
  unfold C, Rdiv.
  rewrite (Rmult_comm (INR (fact (S N)))).
  rewrite Rmult_assoc; rewrite <- Rinv_r_sym.
  rewrite Rmult_1_r; rewrite Rinv_mult_distr.
  reflexivity.
  apply INR_fact_neq_0.
  apply INR_fact_neq_0.
  apply INR_fact_neq_0.
  unfold maj_Reste_E.
  unfold Rdiv; rewrite (Rmult_comm 4).
  rewrite Rmult_assoc.
  apply Rmult_le_compat_l.
  apply pow_le.
  apply Rle_trans with 1.
  left; apply Rlt_0_1.
  apply RmaxLess1.
  apply Rle_trans with
    (sum_f_R0 (fun k:nat => INR (N - k) * / Rsqr (INR (fact (div2 (S N)))))
      (pred N)).
  apply sum_Rle; intros.
  rewrite sum_cte.
  replace (S (pred (N - n))) with (N - n)%nat.
  right; apply Rmult_comm.
  apply S_pred with 0%nat.
  apply plus_lt_reg_l with n.
  rewrite <- le_plus_minus.
  replace (n + 0)%nat with n; [ idtac | ring ].
  apply le_lt_trans with (pred N).
  apply H0.
  apply lt_pred_n_n.
  apply H.
  apply le_trans with (pred N).
  apply H0.
  apply le_pred_n.
  apply Rle_trans with
    (sum_f_R0 (fun k:nat => INR N * / Rsqr (INR (fact (div2 (S N))))) (pred N)).
  apply sum_Rle; intros.
  do 2 rewrite <- (Rmult_comm (/ Rsqr (INR (fact (div2 (S N)))))).
  apply Rmult_le_compat_l.
  left; apply Rinv_0_lt_compat; apply Rsqr_pos_lt.
  apply INR_fact_neq_0.
  apply le_INR.
  apply (fun p n m:nat => plus_le_reg_l n m p) with n.
  rewrite <- le_plus_minus.
  apply le_plus_r.
  apply le_trans with (pred N).
  apply H0.
  apply le_pred_n.
  rewrite sum_cte; replace (S (pred N)) with N.
  cut (div2 (S N) = S (div2 (pred N))).
  intro; rewrite H0.
  rewrite fact_simpl; rewrite mult_comm; rewrite mult_INR; rewrite Rsqr_mult.
  rewrite Rinv_mult_distr.
  rewrite (Rmult_comm (INR N)); repeat rewrite Rmult_assoc;
    apply Rmult_le_compat_l.
  left; apply Rinv_0_lt_compat; apply Rsqr_pos_lt; apply INR_fact_neq_0.
  rewrite <- H0.
  cut (INR N <= INR (2 * div2 (S N))).
  intro; apply Rmult_le_reg_l with (Rsqr (INR (div2 (S N)))).
  apply Rsqr_pos_lt.
  apply not_O_INR; red; intro.
  cut (1 < S N)%nat.
  intro; assert (H4 := div2_not_R0 _ H3).
  rewrite H2 in H4; elim (lt_n_O _ H4).
  apply lt_n_S; apply H.
  repeat rewrite <- Rmult_assoc.
  rewrite <- Rinv_r_sym.
  rewrite Rmult_1_l.
  change 4 with (Rsqr 2).
  rewrite <- Rsqr_mult.
  apply Rsqr_incr_1.
  change 2 with (INR 2).
  rewrite Rmult_comm, <- mult_INR; apply H1.
  left; apply lt_INR_0; apply H.
  left; apply Rmult_lt_0_compat.
  apply lt_INR_0; apply div2_not_R0.
  apply lt_n_S; apply H.
  now apply IZR_lt.
  cut (1 < S N)%nat.
  intro; unfold Rsqr; apply prod_neq_R0; apply not_O_INR; intro;
    assert (H4 := div2_not_R0 _ H2); rewrite H3 in H4;
      elim (lt_n_O _ H4).
  apply lt_n_S; apply H.
  assert (H1 := even_odd_cor N).
  elim H1; intros N0 H2.
  elim H2; intro.
  pattern N at 2; rewrite H3.
  rewrite div2_S_double.
  right; rewrite H3; reflexivity.
  pattern N at 2; rewrite H3.
  replace (S (S (2 * N0))) with (2 * S N0)%nat.
  rewrite div2_double.
  rewrite H3.
  rewrite S_INR; do 2 rewrite mult_INR.
  rewrite (S_INR N0).
  rewrite Rmult_plus_distr_l.
  apply Rplus_le_compat_l.
  rewrite Rmult_1_r.
  simpl.
  pattern 1 at 1; rewrite <- Rplus_0_r; apply Rplus_le_compat_l; left;
    apply Rlt_0_1.
  ring.
  unfold Rsqr; apply prod_neq_R0; apply INR_fact_neq_0.
  unfold Rsqr; apply prod_neq_R0; apply not_O_INR; discriminate.
  assert (H0 := even_odd_cor N).
  elim H0; intros N0 H1.
  elim H1; intro.
  cut (0 < N0)%nat.
  intro; rewrite H2.
  rewrite div2_S_double.
  replace (2 * N0)%nat with (S (S (2 * pred N0))).
  replace (pred (S (S (2 * pred N0)))) with (S (2 * pred N0)).
  rewrite div2_S_double.
  apply S_pred with 0%nat; apply H3.
  reflexivity.
  omega.
  omega.
  rewrite H2.
  replace (pred (S (2 * N0))) with (2 * N0)%nat; [ idtac | reflexivity ].
  replace (S (S (2 * N0))) with (2 * S N0)%nat.
  do 2 rewrite div2_double.
  reflexivity.
  ring.
  apply S_pred with 0%nat; apply H.
Qed.

Lemma maj_Reste_cv_R0 : forall x y:R, Un_cv (maj_Reste_E x y) 0.
Proof.
  intros; assert (H := Majxy_cv_R0 x y).
  unfold Un_cv in H; unfold Un_cv; intros.
  cut (0 < eps / 4);
    [ intro
      | unfold Rdiv; apply Rmult_lt_0_compat;
        [ assumption | apply Rinv_0_lt_compat; prove_sup0 ] ].
  elim (H _ H1); intros N0 H2.
  exists (max (2 * S N0) 2); intros.
  unfold R_dist in H2; unfold R_dist; rewrite Rminus_0_r;
    unfold Majxy in H2; unfold maj_Reste_E.
  rewrite Rabs_right.
  apply Rle_lt_trans with
    (4 *
      (Rmax 1 (Rmax (Rabs x) (Rabs y)) ^ (4 * S (div2 (pred n))) /
        INR (fact (div2 (pred n))))).
  apply Rmult_le_compat_l.
  left; prove_sup0.
  unfold Rdiv, Rsqr; rewrite Rinv_mult_distr.
  rewrite (Rmult_comm (Rmax 1 (Rmax (Rabs x) (Rabs y)) ^ (2 * n)));
    rewrite
      (Rmult_comm (Rmax 1 (Rmax (Rabs x) (Rabs y)) ^ (4 * S (div2 (pred n)))))
      ; rewrite Rmult_assoc; apply Rmult_le_compat_l.
  left; apply Rinv_0_lt_compat; apply INR_fact_lt_0.
  apply Rle_trans with (Rmax 1 (Rmax (Rabs x) (Rabs y)) ^ (2 * n)).
  rewrite Rmult_comm;
    pattern (Rmax 1 (Rmax (Rabs x) (Rabs y)) ^ (2 * n)) at 2;
      rewrite <- Rmult_1_r; apply Rmult_le_compat_l.
  apply pow_le; apply Rle_trans with 1.
  left; apply Rlt_0_1.
  apply RmaxLess1.
  apply Rmult_le_reg_l with (INR (fact (div2 (pred n)))).
  apply INR_fact_lt_0.
  rewrite Rmult_1_r; rewrite <- Rinv_r_sym.
  apply (le_INR 1).
  apply lt_le_S.
  apply INR_lt.
  apply INR_fact_lt_0.
  apply INR_fact_neq_0.
  apply Rle_pow.
  apply RmaxLess1.
  assert (H4 := even_odd_cor n).
  elim H4; intros N1 H5.
  elim H5; intro.
  cut (0 < N1)%nat.
  intro.
  rewrite H6.
  replace (pred (2 * N1)) with (S (2 * pred N1)).
  rewrite div2_S_double.
  omega.
  omega.
  assert (0 < n)%nat.
  apply lt_le_trans with 2%nat.
  apply lt_O_Sn.
  apply le_trans with (max (2 * S N0) 2).
  apply le_max_r.
  apply H3.
  omega.
  rewrite H6.
  replace (pred (S (2 * N1))) with (2 * N1)%nat.
  rewrite div2_double.
  replace (4 * S N1)%nat with (2 * (2 * S N1))%nat.
  apply (fun m n p:nat => mult_le_compat_l p n m).
  replace (2 * S N1)%nat with (S (S (2 * N1))).
  apply le_n_Sn.
  ring.
  ring.
  reflexivity.
  apply INR_fact_neq_0.
  apply INR_fact_neq_0.
  apply Rmult_lt_reg_l with (/ 4).
  apply Rinv_0_lt_compat; prove_sup0.
  rewrite <- Rmult_assoc; rewrite <- Rinv_l_sym.
  rewrite Rmult_1_l; rewrite Rmult_comm.
  replace
  (Rmax 1 (Rmax (Rabs x) (Rabs y)) ^ (4 * S (div2 (pred n))) /
    INR (fact (div2 (pred n)))) with
  (Rabs
    (Rmax 1 (Rmax (Rabs x) (Rabs y)) ^ (4 * S (div2 (pred n))) /
      INR (fact (div2 (pred n))) - 0)).
  apply H2; unfold ge.
  cut (2 * S N0 <= n)%nat.
  intro; apply le_S_n.
  apply INR_le; apply Rmult_le_reg_l with (INR 2).
  simpl; prove_sup0.
  do 2 rewrite <- mult_INR; apply le_INR.
  apply le_trans with n.
  apply H4.
  assert (H5 := even_odd_cor n).
  elim H5; intros N1 H6.
  elim H6; intro.
  cut (0 < N1)%nat.
  intro.
  rewrite H7.
  apply (fun m n p:nat => mult_le_compat_l p n m).
  replace (pred (2 * N1)) with (S (2 * pred N1)).
  rewrite div2_S_double.
  replace (S (pred N1)) with N1.
  apply le_n.
  apply S_pred with 0%nat; apply H8.
  replace (2 * N1)%nat with (S (S (2 * pred N1))).
  reflexivity.
  pattern N1 at 2; replace N1 with (S (pred N1)).
  ring.
  symmetry ; apply S_pred with 0%nat; apply H8.
  apply INR_lt.
  apply Rmult_lt_reg_l with (INR 2).
  simpl; prove_sup0.
  rewrite Rmult_0_r; rewrite <- mult_INR.
  apply lt_INR_0.
  rewrite <- H7.
  apply lt_le_trans with 2%nat.
  apply lt_O_Sn.
  apply le_trans with (max (2 * S N0) 2).
  apply le_max_r.
  apply H3.
  rewrite H7.
  replace (pred (S (2 * N1))) with (2 * N1)%nat.
  rewrite div2_double.
  replace (2 * S N1)%nat with (S (S (2 * N1))).
  apply le_n_Sn.
  ring.
  reflexivity.
  apply le_trans with (max (2 * S N0) 2).
  apply le_max_l.
  apply H3.
  rewrite Rminus_0_r; apply Rabs_right.
  apply Rle_ge.
  unfold Rdiv; apply Rmult_le_pos.
  apply pow_le.
  apply Rle_trans with 1.
  left; apply Rlt_0_1.
  apply RmaxLess1.
  left; apply Rinv_0_lt_compat; apply INR_fact_lt_0.
  discrR.
  apply Rle_ge.
  unfold Rdiv; apply Rmult_le_pos.
  left; prove_sup0.
  apply Rmult_le_pos.
  apply pow_le.
  apply Rle_trans with 1.
  left; apply Rlt_0_1.
  apply RmaxLess1.
  left; apply Rinv_0_lt_compat; apply Rsqr_pos_lt; apply INR_fact_neq_0.
Qed.

(**********)
Lemma Reste_E_cv : forall x y:R, Un_cv (Reste_E x y) 0.
Proof.
  intros; assert (H := maj_Reste_cv_R0 x y).
  unfold Un_cv in H; unfold Un_cv; intros; elim (H _ H0); intros.
  exists (max x0 1); intros.
  unfold R_dist; rewrite Rminus_0_r.
  apply Rle_lt_trans with (maj_Reste_E x y n).
  apply Reste_E_maj.
  apply lt_le_trans with 1%nat.
  apply lt_O_Sn.
  apply le_trans with (max x0 1).
  apply le_max_r.
  apply H2.
  replace (maj_Reste_E x y n) with (R_dist (maj_Reste_E x y n) 0).
  apply H1.
  unfold ge; apply le_trans with (max x0 1).
  apply le_max_l.
  apply H2.
  unfold R_dist; rewrite Rminus_0_r; apply Rabs_right.
  apply Rle_ge; apply Rle_trans with (Rabs (Reste_E x y n)).
  apply Rabs_pos.
  apply Reste_E_maj.
  apply lt_le_trans with 1%nat.
  apply lt_O_Sn.
  apply le_trans with (max x0 1).
  apply le_max_r.
  apply H2.
Qed.

(**********)
Lemma exp_plus : forall x y:R, exp (x + y) = exp x * exp y.
Proof.
  intros; assert (H0 := E1_cvg x).
  assert (H := E1_cvg y).
  assert (H1 := E1_cvg (x + y)).
  eapply UL_sequence.
  apply H1.
  assert (H2 := CV_mult _ _ _ _ H0 H).
  assert (H3 := CV_minus _ _ _ _ H2 (Reste_E_cv x y)).
  unfold Un_cv; unfold Un_cv in H3; intros.
  elim (H3 _ H4); intros.
  exists (S x0); intros.
  rewrite <- (exp_form x y n).
  rewrite Rminus_0_r in H5.
  apply H5.
  unfold ge; apply le_trans with (S x0).
  apply le_n_Sn.
  apply H6.
  apply lt_le_trans with (S x0).
  apply lt_O_Sn.
  apply H6.
Qed.

(**********)
Lemma exp_pos_pos : forall x:R, 0 < x -> 0 < exp x.
Proof.
  intros; set (An := fun N:nat => / INR (fact N) * x ^ N).
  cut (Un_cv (fun n:nat => sum_f_R0 An n) (exp x)).
  intro; apply Rlt_le_trans with (sum_f_R0 An 0).
  unfold An; simpl; rewrite Rinv_1; rewrite Rmult_1_r;
    apply Rlt_0_1.
  apply sum_incr.
  assumption.
  intro; unfold An; left; apply Rmult_lt_0_compat.
  apply Rinv_0_lt_compat; apply INR_fact_lt_0.
  apply (pow_lt _ n H).
  unfold exp; unfold projT1; case (exist_exp x); intro.
  unfold exp_in; unfold infinite_sum, Un_cv; trivial.
Qed.

(**********)
Lemma exp_pos : forall x:R, 0 < exp x.
Proof.
  intro; destruct (total_order_T 0 x) as [[Hlt|<-]|Hgt].
  apply (exp_pos_pos _ Hlt).
  rewrite exp_0; apply Rlt_0_1.
  replace (exp x) with (1 / exp (- x)).
  unfold Rdiv; apply Rmult_lt_0_compat.
  apply Rlt_0_1.
  apply Rinv_0_lt_compat; apply exp_pos_pos.
  apply (Ropp_0_gt_lt_contravar _ Hgt).
  cut (exp (- x) <> 0).
  intro; unfold Rdiv; apply Rmult_eq_reg_l with (exp (- x)).
  rewrite Rmult_1_l; rewrite <- Rinv_r_sym.
  rewrite <- exp_plus.
  rewrite Rplus_opp_l; rewrite exp_0; reflexivity.
  apply H.
  apply H.
  assert (H := exp_plus x (- x)).
  rewrite Rplus_opp_r in H; rewrite exp_0 in H.
  red; intro; rewrite H0 in H.
  rewrite Rmult_0_r in H.
  elim R1_neq_R0; assumption.
Qed.

(* ((exp h)-1)/h -> 0 quand h->0 *)
Lemma derivable_pt_lim_exp_0 : derivable_pt_lim exp 0 1.
Proof.
  unfold derivable_pt_lim; intros.
  set (fn := fun (N:nat) (x:R) => x ^ N / INR (fact (S N))).
  cut (CVN_R fn).
  intro; cut (forall x:R, { l:R | Un_cv (fun N:nat => SP fn N x) l }).
  intro cv; cut (forall n:nat, continuity (fn n)).
  intro; cut (continuity (SFL fn cv)).
  intro; unfold continuity in H1.
  assert (H2 := H1 0).
  unfold continuity_pt in H2; unfold continue_in in H2; unfold limit1_in in H2;
    unfold limit_in in H2; simpl in H2; unfold R_dist in H2.
  elim (H2 _ H); intros alp H3.
  elim H3; intros.
  exists (mkposreal _ H4); intros.
  rewrite Rplus_0_l; rewrite exp_0.
  replace ((exp h - 1) / h) with (SFL fn cv h).
  replace 1 with (SFL fn cv 0).
  apply H5.
  split.
  unfold D_x, no_cond; split.
  trivial.
  apply (not_eq_sym H6).
  rewrite Rminus_0_r; apply H7.
  unfold SFL.
  case (cv 0) as (x,Hu).
  eapply UL_sequence.
  apply Hu.
  unfold Un_cv, SP in |- *.
  intros; exists 1%nat; intros.
  unfold R_dist; rewrite decomp_sum.
  rewrite (Rplus_comm (fn 0%nat 0)).
  replace (fn 0%nat 0) with 1.
  unfold Rminus; rewrite Rplus_assoc; rewrite Rplus_opp_r;
    rewrite Rplus_0_r.
  replace (sum_f_R0 (fun i:nat => fn (S i) 0) (pred n)) with 0.
  rewrite Rabs_R0; apply H8.
  symmetry ; apply sum_eq_R0; intros.
  unfold fn.
  simpl.
  unfold Rdiv; do 2 rewrite Rmult_0_l; reflexivity.
  unfold fn; simpl.
  unfold Rdiv; rewrite Rinv_1; rewrite Rmult_1_r; reflexivity.
  apply lt_le_trans with 1%nat; [ apply lt_n_Sn | apply H9 ].
  unfold SFL, exp.
  case (cv h) as (x0,Hu); case (exist_exp h) as (x,Hexp); simpl.
  eapply UL_sequence.
  apply Hu.
  unfold Un_cv; intros.
  unfold exp_in, infinite_sum in Hexp.
  cut (0 < eps0 * Rabs h).
  intro; elim (Hexp _ H9); intros N0 H10.
  exists N0; intros.
  unfold R_dist.
  apply Rmult_lt_reg_l with (Rabs h).
  apply Rabs_pos_lt; assumption.
  rewrite <- Rabs_mult.
  rewrite Rmult_minus_distr_l.
  replace (h * ((x - 1) / h)) with (x - 1).
  unfold R_dist in H10.
  replace (h * SP fn n h - (x - 1)) with
  (sum_f_R0 (fun i:nat => / INR (fact i) * h ^ i) (S n) - x).
  rewrite (Rmult_comm (Rabs h)).
  apply H10.
  unfold ge.
  apply le_trans with (S N0).
  apply le_n_Sn.
  apply le_n_S; apply H11.
  rewrite decomp_sum.
  replace (/ INR (fact 0) * h ^ 0) with 1.
  unfold Rminus.
  rewrite Ropp_plus_distr.
  rewrite Ropp_involutive.
  rewrite <- (Rplus_comm (- x)).
  rewrite <- (Rplus_comm (- x + 1)).
  rewrite Rplus_assoc; repeat apply Rplus_eq_compat_l.
  replace (pred (S n)) with n; [ idtac | reflexivity ].
  unfold SP.
  rewrite scal_sum.
  apply sum_eq; intros.
  unfold fn.
  replace (h ^ S i) with (h * h ^ i).
  unfold Rdiv; ring.
  simpl; ring.
  simpl; rewrite Rinv_1; rewrite Rmult_1_r; reflexivity.
  apply lt_O_Sn.
  unfold Rdiv.
  rewrite <- Rmult_assoc.
  symmetry ; apply Rinv_r_simpl_m.
  assumption.
  apply Rmult_lt_0_compat.
  apply H8.
  apply Rabs_pos_lt; assumption.
  apply SFL_continuity; assumption.
  intro; unfold fn.
  replace (fun x:R => x ^ n / INR (fact (S n))) with
  (pow_fct n / fct_cte (INR (fact (S n))))%F; [ idtac | reflexivity ].
  apply continuity_div.
  apply derivable_continuous; apply (derivable_pow n).
  apply derivable_continuous; apply derivable_const.
  intro; unfold fct_cte; apply INR_fact_neq_0.
  apply (CVN_R_CVS _ X).
  assert (H0 := Alembert_exp).
  unfold CVN_R.
  intro; unfold CVN_r.
  exists (fun N:nat => r ^ N / INR (fact (S N))).
  cut
    { l:R |
        Un_cv
        (fun n:nat =>
          sum_f_R0 (fun k:nat => Rabs (r ^ k / INR (fact (S k)))) n) l }.
  intros (x,p).
  exists x; intros.
  split.
  apply p.
  unfold Boule; intros.
  rewrite Rminus_0_r in H1.
  unfold fn.
  unfold Rdiv; rewrite Rabs_mult.
  cut (0 < INR (fact (S n))).
  intro.
  rewrite (Rabs_right (/ INR (fact (S n)))).
  do 2 rewrite <- (Rmult_comm (/ INR (fact (S n)))).
  apply Rmult_le_compat_l.
  left; apply Rinv_0_lt_compat; apply H2.
  rewrite <- RPow_abs.
  apply pow_maj_Rabs.
  rewrite Rabs_Rabsolu; left; apply H1.
  apply Rle_ge; left; apply Rinv_0_lt_compat; apply H2.
  apply INR_fact_lt_0.
  cut ((r:R) <> 0).
  intro; apply Alembert_C2.
  intro; apply Rabs_no_R0.
  unfold Rdiv; apply prod_neq_R0.
  apply pow_nonzero; assumption.
  apply Rinv_neq_0_compat; apply INR_fact_neq_0.
  unfold Un_cv in H0.
  unfold Un_cv; intros.
  cut (0 < eps0 / r);
    [ intro
      | unfold Rdiv; apply Rmult_lt_0_compat;
        [ assumption | apply Rinv_0_lt_compat; apply (cond_pos r) ] ].
  elim (H0 _ H3); intros N0 H4.
  exists N0; intros.
  cut (S n >= N0)%nat.
  intro hyp_sn.
  assert (H6 := H4 _ hyp_sn).
  unfold R_dist in H6; rewrite Rminus_0_r in H6.
  rewrite Rabs_Rabsolu in H6.
  unfold R_dist; rewrite Rminus_0_r.
  rewrite Rabs_Rabsolu.
  replace
  (Rabs (r ^ S n / INR (fact (S (S n)))) / Rabs (r ^ n / INR (fact (S n))))
    with (r * / INR (fact (S (S n))) * / / INR (fact (S n))).
  rewrite Rmult_assoc; rewrite Rabs_mult.
  rewrite (Rabs_right r).
  apply Rmult_lt_reg_l with (/ r).
  apply Rinv_0_lt_compat; apply (cond_pos r).
  rewrite <- Rmult_assoc; rewrite <- Rinv_l_sym.
  rewrite Rmult_1_l; rewrite <- (Rmult_comm eps0).
  apply H6.
  assumption.
  apply Rle_ge; left; apply (cond_pos r).
  unfold Rdiv.
  repeat rewrite Rabs_mult.
  repeat rewrite Rabs_Rinv.
  rewrite Rinv_mult_distr.
  repeat rewrite Rabs_right.
  rewrite Rinv_involutive.
  rewrite (Rmult_comm r).
  rewrite (Rmult_comm (r ^ S n)).
  repeat rewrite Rmult_assoc.
  apply Rmult_eq_compat_l.
  rewrite (Rmult_comm r).
  rewrite <- Rmult_assoc; rewrite <- (Rmult_comm (INR (fact (S n)))).
  apply Rmult_eq_compat_l.
  simpl.
  rewrite Rmult_assoc; rewrite <- Rinv_r_sym.
  ring.
  apply pow_nonzero; assumption.
  apply INR_fact_neq_0.
  apply Rle_ge; left; apply INR_fact_lt_0.
  apply Rle_ge; left; apply pow_lt; apply (cond_pos r).
  apply Rle_ge; left; apply INR_fact_lt_0.
  apply Rle_ge; left; apply pow_lt; apply (cond_pos r).
  apply Rabs_no_R0; apply pow_nonzero; assumption.
  apply Rinv_neq_0_compat; apply Rabs_no_R0; apply INR_fact_neq_0.
  apply INR_fact_neq_0.
  apply INR_fact_neq_0.
  unfold ge; apply le_trans with n.
  apply H5.
  apply le_n_Sn.
  assert (H1 := cond_pos r); red; intro; rewrite H2 in H1;
    elim (Rlt_irrefl _ H1).
Qed.

(**********)
Lemma derivable_pt_lim_exp : forall x:R, derivable_pt_lim exp x (exp x).
Proof.
  intro; assert (H0 := derivable_pt_lim_exp_0).
  unfold derivable_pt_lim in H0; unfold derivable_pt_lim; intros.
  cut (0 < eps / exp x);
    [ intro
      | unfold Rdiv; apply Rmult_lt_0_compat;
        [ apply H | apply Rinv_0_lt_compat; apply exp_pos ] ].
  elim (H0 _ H1); intros del H2.
  exists del; intros.
  assert (H5 := H2 _ H3 H4).
  rewrite Rplus_0_l in H5; rewrite exp_0 in H5.
  replace ((exp (x + h) - exp x) / h - exp x) with
  (exp x * ((exp h - 1) / h - 1)).
  rewrite Rabs_mult; rewrite (Rabs_right (exp x)).
  apply Rmult_lt_reg_l with (/ exp x).
  apply Rinv_0_lt_compat; apply exp_pos.
  rewrite <- Rmult_assoc; rewrite <- Rinv_l_sym.
  rewrite Rmult_1_l; rewrite <- (Rmult_comm eps).
  apply H5.
  assert (H6 := exp_pos x); red; intro; rewrite H7 in H6;
    elim (Rlt_irrefl _ H6).
  apply Rle_ge; left; apply exp_pos.
  rewrite Rmult_minus_distr_l.
  rewrite Rmult_1_r; unfold Rdiv; rewrite <- Rmult_assoc;
    rewrite Rmult_minus_distr_l.
  rewrite Rmult_1_r; rewrite exp_plus; reflexivity.
Qed.
