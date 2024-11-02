(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Rbase.
Require Import Rfunctions.
Require Import SeqSeries.
Require Import Rtrigo_def.
Require Import Cos_rel.
Require Import Lia Lra.
Require Import Arith.Factorial.
Local Open Scope nat_scope.
Local Open Scope R_scope.

Definition Majxy (x y:R) (n:nat) : R :=
  Rmax 1 (Rmax (Rabs x) (Rabs y)) ^ (4 * S n) / INR (fact n).

Lemma Majxy_cv_R0 : forall x y:R, Un_cv (Majxy x y) 0.
Proof.
  intros.
  set (C := Rmax 1 (Rmax (Rabs x) (Rabs y))).
  set (C0 := C ^ 4).
  assert (0 < C). {
    apply Rlt_le_trans with 1.
    - apply Rlt_0_1.
    - unfold C.
      apply RmaxLess1. }
  assert (0 < C0) by (unfold C0; apply pow_lt; assumption).
  assert (H1 := cv_speed_pow_fact C0).
  unfold Un_cv in H1; unfold Rdist in H1.
  unfold Un_cv; unfold Rdist; intros.
  cut (0 < eps / C0);
    [ intro
      | unfold Rdiv; apply Rmult_lt_0_compat;
        [ assumption | apply Rinv_0_lt_compat; assumption ] ].
  elim (H1 (eps / C0) H3); intros N0 H4.
  exists N0; intros.
  replace (Majxy x y n) with (C0 ^ S n / INR (fact n)).
  2:{ unfold Majxy.
      unfold C0.
      rewrite pow_mult.
      unfold C; reflexivity. }
  simpl.
  apply Rmult_lt_reg_l with (Rabs (/ C0)).
  { apply Rabs_pos_lt.
    apply Rinv_neq_0_compat. lra. }
  rewrite <- Rabs_mult.
  unfold Rminus; rewrite Rmult_plus_distr_l.
  rewrite Ropp_0; rewrite Rmult_0_r.
  unfold Rdiv; repeat rewrite <- Rmult_assoc.
  rewrite Rinv_l.
  2:nra.
  rewrite Rmult_1_l.
  rewrite (Rabs_right (/ C0)).
  2:apply Rle_ge; left; apply Rinv_0_lt_compat; assumption.
  rewrite <- (Rmult_comm eps).
  replace (C0 ^ n * / INR (fact n) + 0) with (C0 ^ n * / INR (fact n) - 0) by ring.
  unfold Rdiv in H4; apply H4; assumption.
Qed.

Lemma reste1_maj :
  forall (x y:R) (N:nat),
    (0 < N)%nat -> Rabs (Reste1 x y N) <= Majxy x y (pred N).
Proof.
  intros.
  set (C := Rmax 1 (Rmax (Rabs x) (Rabs y))).
  unfold Reste1.
  apply Rle_trans with
    (sum_f_R0
      (fun k:nat =>
        Rabs
        (sum_f_R0
          (fun l:nat =>
            (-1) ^ S (l + k) / INR (fact (2 * S (l + k))) *
            x ^ (2 * S (l + k)) *
            ((-1) ^ (N - l) / INR (fact (2 * (N - l)))) *
            y ^ (2 * (N - l))) (pred (N - k)))) (
        pred N)).
  { apply
    (Rsum_abs
      (fun k:nat =>
        sum_f_R0
        (fun l:nat =>
          (-1) ^ S (l + k) / INR (fact (2 * S (l + k))) *
          x ^ (2 * S (l + k)) * ((-1) ^ (N - l) / INR (fact (2 * (N - l)))) *
          y ^ (2 * (N - l))) (pred (N - k))) (pred N)). }
  apply Rle_trans with
    (sum_f_R0
      (fun k:nat =>
        sum_f_R0
        (fun l:nat =>
          Rabs
          ((-1) ^ S (l + k) / INR (fact (2 * S (l + k))) *
            x ^ (2 * S (l + k)) *
            ((-1) ^ (N - l) / INR (fact (2 * (N - l)))) *
            y ^ (2 * (N - l)))) (pred (N - k))) (
              pred N)).
  { apply sum_Rle.
    intros.
    apply
      (Rsum_abs
        (fun l:nat =>
          (-1) ^ S (l + n) / INR (fact (2 * S (l + n))) * x ^ (2 * S (l + n)) *
          ((-1) ^ (N - l) / INR (fact (2 * (N - l)))) *
          y ^ (2 * (N - l))) (pred (N - n))). }
  apply Rle_trans with
    (sum_f_R0
      (fun k:nat =>
        sum_f_R0
        (fun l:nat =>
          / INR (fact (2 * S (l + k)) * fact (2 * (N - l))) *
          C ^ (2 * S (N + k))) (pred (N - k))) (pred N)).
  { apply sum_Rle; intros.
    apply sum_Rle; intros.
    unfold Rdiv; repeat rewrite Rabs_mult.
    do 2 rewrite pow_1_abs.
    do 2 rewrite Rmult_1_l.
    rewrite (Rabs_right (/ INR (fact (2 * S (n0 + n))))).
    2:apply Rle_ge; left; apply Rinv_0_lt_compat; apply INR_fact_lt_0.
    rewrite (Rabs_right (/ INR (fact (2 * (N - n0))))).
    2:apply Rle_ge; left; apply Rinv_0_lt_compat; apply INR_fact_lt_0.
    rewrite mult_INR.
    rewrite Rinv_mult.
    repeat rewrite Rmult_assoc.
    apply Rmult_le_compat_l.
    { left; apply Rinv_0_lt_compat; apply INR_fact_lt_0. }
    rewrite <- Rmult_assoc.
    rewrite <- (Rmult_comm (/ INR (fact (2 * (N - n0))))).
    rewrite Rmult_assoc.
    apply Rmult_le_compat_l.
    { left; apply Rinv_0_lt_compat; apply INR_fact_lt_0. }
    do 2 rewrite <- RPow_abs.
    apply Rle_trans with (Rabs x ^ (2 * S (n0 + n)) * C ^ (2 * (N - n0))).
    { apply Rmult_le_compat_l.
      { apply pow_le; apply Rabs_pos. }
      apply pow_incr.
      split.
      { apply Rabs_pos. }
      unfold C.
      apply Rle_trans with (Rmax (Rabs x) (Rabs y)); apply RmaxLess2. }
    apply Rle_trans with (C ^ (2 * S (n0 + n)) * C ^ (2 * (N - n0))).
    { do 2 rewrite <- (Rmult_comm (C ^ (2 * (N - n0)))).
      apply Rmult_le_compat_l.
      { apply pow_le.
        apply Rle_trans with 1.
        { left; apply Rlt_0_1. }
        unfold C; apply RmaxLess1. }
      apply pow_incr.
      split.
      { apply Rabs_pos. }
      unfold C; apply Rle_trans with (Rmax (Rabs x) (Rabs y)).
      - apply RmaxLess1.
      - apply RmaxLess2. }
    right.
    replace (2 * S (N + n))%nat with (2 * (N - n0) + 2 * S (n0 + n))%nat by lia.
    rewrite pow_add.
    apply Rmult_comm. }
  apply Rle_trans with
    (sum_f_R0
       (fun k:nat =>
          sum_f_R0
            (fun l:nat =>
               / INR (fact (2 * S (l + k)) * fact (2 * (N - l))) * C ^ (4 * N))
            (pred (N - k))) (pred N)).
  { apply sum_Rle; intros.
    apply sum_Rle; intros.
    apply Rmult_le_compat_l.
    { left; apply Rinv_0_lt_compat.
      rewrite mult_INR; apply Rmult_lt_0_compat; apply INR_fact_lt_0. }
    apply Rle_pow.
    { unfold C; apply RmaxLess1. }
    lia. }
  apply Rle_trans with
    (sum_f_R0
       (fun k:nat =>
          sum_f_R0 (fun l:nat => C ^ (4 * N) * Rsqr (/ INR (fact (S (N + k)))))
                   (pred (N - k))) (pred N)).
  { apply sum_Rle; intros.
    apply sum_Rle; intros.
    rewrite <- (Rmult_comm (C ^ (4 * N))).
    apply Rmult_le_compat_l.
    { apply pow_le.
      left; apply Rlt_le_trans with 1.
      { apply Rlt_0_1. }
      unfold C; apply RmaxLess1. }
    replace (/ INR (fact (2 * S (n0 + n)) * fact (2 * (N - n0)))) with
      (Binomial.C (2 * S (N + n)) (2 * S (n0 + n)) / INR (fact (2 * S (N + n)))).
    2:{ unfold Rdiv; rewrite Rmult_comm.
        unfold Binomial.C.
        unfold Rdiv; repeat rewrite <- Rmult_assoc.
        rewrite Rinv_l.
        { rewrite Rmult_1_l.
          replace (2 * S (N + n) - 2 * S (n0 + n))%nat with (2 * (N - n0))%nat by lia.
          rewrite mult_INR.
          reflexivity. }
        apply INR_fact_neq_0. }
    apply Rle_trans with
      (Binomial.C (2 * S (N + n)) (S (N + n)) / INR (fact (2 * S (N + n)))).
    { unfold Rdiv;
        do 2 rewrite <- (Rmult_comm (/ INR (fact (2 * S (N + n))))).
      apply Rmult_le_compat_l.
      { left; apply Rinv_0_lt_compat; apply INR_fact_lt_0. }
      apply C_maj.
      lia. }
    right.
    unfold Rdiv; rewrite Rmult_comm.
    unfold Binomial.C.
    unfold Rdiv; repeat rewrite <- Rmult_assoc.
    rewrite Rinv_l.
    2:apply INR_fact_neq_0.
    rewrite Rmult_1_l.
    replace (2 * S (N + n) - S (N + n))%nat with (S (N + n)) by lia.
    rewrite Rinv_mult.
    unfold Rsqr; reflexivity.
  }
  apply Rle_trans with
    (sum_f_R0 (fun k:nat => INR N / INR (fact (S N)) * C ^ (4 * N)) (pred N)).
  { apply sum_Rle; intros.
    rewrite <- (scal_sum (fun _:nat => C ^ (4 * N)) (pred (N - n))
                        (Rsqr (/ INR (fact (S (N + n)))))).
    rewrite sum_cte.
    rewrite <- Rmult_assoc.
    do 2 rewrite <- (Rmult_comm (C ^ (4 * N))).
    rewrite Rmult_assoc.
    apply Rmult_le_compat_l.
    { apply pow_le.
      left; apply Rlt_le_trans with 1.
      { apply Rlt_0_1. }
      unfold C; apply RmaxLess1. }
    apply Rle_trans with (Rsqr (/ INR (fact (S (N + n)))) * INR N).
    { apply Rmult_le_compat_l.
      { apply Rle_0_sqr. }
      apply le_INR.
      lia. }
    rewrite Rmult_comm; unfold Rdiv; apply Rmult_le_compat_l.
    { apply pos_INR. }
    apply Rle_trans with (/ INR (fact (S (N + n)))).
    { pattern (/ INR (fact (S (N + n)))) at 2; rewrite <- Rmult_1_r.
      unfold Rsqr.
      apply Rmult_le_compat_l.
      { left; apply Rinv_0_lt_compat; apply INR_fact_lt_0. }
      apply Rmult_le_reg_l with (INR (fact (S (N + n)))).
      { apply INR_fact_lt_0. }
      rewrite Rinv_r.
      { rewrite Rmult_1_r.
        apply (le_INR 1).
        apply Nat.le_succ_l.
        apply INR_lt; apply INR_fact_lt_0. }
      apply INR_fact_neq_0. }
    apply Rmult_le_reg_l with (INR (fact (S (N + n)))).
    { apply INR_fact_lt_0. }
    rewrite Rinv_r.
    2:apply INR_fact_neq_0.
    apply Rmult_le_reg_l with (INR (fact (S N))).
    { apply INR_fact_lt_0. }
    rewrite Rmult_1_r.
    rewrite (Rmult_comm (INR (fact (S N)))).
    rewrite Rmult_assoc.
    rewrite Rinv_l.
    2:apply INR_fact_neq_0.
    rewrite Rmult_1_r.
    apply le_INR.
    apply fact_le.
    apply -> Nat.succ_le_mono.
    apply Nat.le_add_r.
  }
  rewrite sum_cte.
  apply Rle_trans with (C ^ (4 * N) / INR (fact (pred N))).
  2:{ right.
      unfold Majxy.
      unfold C.
      replace (S (pred N)) with N by lia.
      reflexivity. }
  rewrite <- (Rmult_comm (C ^ (4 * N))).
  unfold Rdiv; rewrite Rmult_assoc; apply Rmult_le_compat_l.
  { apply pow_le.
    left; apply Rlt_le_trans with 1.
    { apply Rlt_0_1. }
    unfold C; apply RmaxLess1. }
  assert (S (pred N) = N) by lia.
  rewrite H0.
  pattern N at 2; rewrite <- H0.
  do 2 rewrite fact_simpl.
  rewrite H0.
  repeat rewrite mult_INR.
  repeat rewrite Rinv_mult.
  rewrite (Rmult_comm (/ INR (S N))).
  repeat rewrite <- Rmult_assoc.
  rewrite Rinv_r.
  2:apply not_O_INR;lia.
  rewrite Rmult_1_l.
  pattern (/ INR (fact (pred N))) at 2; rewrite <- Rmult_1_r.
  rewrite Rmult_assoc.
  apply Rmult_le_compat_l.
  { left; apply Rinv_0_lt_compat; apply INR_fact_lt_0. }
  apply Rmult_le_reg_l with (INR (S N)).
  { apply lt_INR_0; apply Nat.lt_0_succ. }
  rewrite <- Rmult_assoc; rewrite Rinv_r.
  { rewrite Rmult_1_r; rewrite Rmult_1_l.
    apply le_INR; apply Nat.le_succ_diag_r. }
  apply not_O_INR; discriminate.
Qed.

Lemma reste2_maj :
  forall (x y:R) (N:nat), (0 < N)%nat -> Rabs (Reste2 x y N) <= Majxy x y N.
Proof.
  intros.
  set (C := Rmax 1 (Rmax (Rabs x) (Rabs y))).
  unfold Reste2.
  apply Rle_trans with
    (sum_f_R0
      (fun k:nat =>
        Rabs
        (sum_f_R0
          (fun l:nat =>
            (-1) ^ S (l + k) / INR (fact (2 * S (l + k) + 1)) *
            x ^ (2 * S (l + k) + 1) *
            ((-1) ^ (N - l) / INR (fact (2 * (N - l) + 1))) *
            y ^ (2 * (N - l) + 1)) (pred (N - k)))) (
              pred N)).
  { apply
    (Rsum_abs
      (fun k:nat =>
        sum_f_R0
        (fun l:nat =>
          (-1) ^ S (l + k) / INR (fact (2 * S (l + k) + 1)) *
          x ^ (2 * S (l + k) + 1) *
          ((-1) ^ (N - l) / INR (fact (2 * (N - l) + 1))) *
          y ^ (2 * (N - l) + 1)) (pred (N - k))) (
            pred N)). }
  apply Rle_trans with
    (sum_f_R0
      (fun k:nat =>
        sum_f_R0
        (fun l:nat =>
          Rabs
          ((-1) ^ S (l + k) / INR (fact (2 * S (l + k) + 1)) *
            x ^ (2 * S (l + k) + 1) *
            ((-1) ^ (N - l) / INR (fact (2 * (N - l) + 1))) *
            y ^ (2 * (N - l) + 1))) (pred (N - k))) (
              pred N)).
  { apply sum_Rle.
    intros.
    apply
    (Rsum_abs
      (fun l:nat =>
        (-1) ^ S (l + n) / INR (fact (2 * S (l + n) + 1)) *
        x ^ (2 * S (l + n) + 1) *
        ((-1) ^ (N - l) / INR (fact (2 * (N - l) + 1))) *
        y ^ (2 * (N - l) + 1)) (pred (N - n))). }
  apply Rle_trans with
    (sum_f_R0
      (fun k:nat =>
        sum_f_R0
        (fun l:nat =>
          / INR (fact (2 * S (l + k) + 1) * fact (2 * (N - l) + 1)) *
          C ^ (2 * S (S (N + k)))) (pred (N - k))) (
            pred N)).
  { apply sum_Rle; intros.
    apply sum_Rle; intros.
    unfold Rdiv; repeat rewrite Rabs_mult.
    do 2 rewrite pow_1_abs.
    do 2 rewrite Rmult_1_l.
    rewrite (Rabs_right (/ INR (fact (2 * S (n0 + n) + 1)))).
    2:{ apply Rle_ge; left; apply Rinv_0_lt_compat.
        apply INR_fact_lt_0. }
    rewrite (Rabs_right (/ INR (fact (2 * (N - n0) + 1)))).
    2:{ apply Rle_ge; left; apply Rinv_0_lt_compat.
        apply INR_fact_lt_0. }
    rewrite mult_INR.
    rewrite Rinv_mult.
    repeat rewrite Rmult_assoc.
    apply Rmult_le_compat_l.
    { left; apply Rinv_0_lt_compat; apply INR_fact_lt_0. }
    rewrite <- Rmult_assoc.
    rewrite <- (Rmult_comm (/ INR (fact (2 * (N - n0) + 1)))).
    rewrite Rmult_assoc.
    apply Rmult_le_compat_l.
    { left; apply Rinv_0_lt_compat; apply INR_fact_lt_0. }
    do 2 rewrite <- RPow_abs.
    apply Rle_trans with (Rabs x ^ (2 * S (n0 + n) + 1) * C ^ (2 * (N - n0) + 1)).
    { apply Rmult_le_compat_l.
      { apply pow_le; apply Rabs_pos. }
      apply pow_incr.
      split.
      { apply Rabs_pos. }
      unfold C.
      apply Rle_trans with (Rmax (Rabs x) (Rabs y)); apply RmaxLess2. }
    apply Rle_trans with (C ^ (2 * S (n0 + n) + 1) * C ^ (2 * (N - n0) + 1)).
    2:{ right.
        replace (2 * S (S (N + n)))%nat with
          (2 * (N - n0) + 1 + (2 * S (n0 + n) + 1))%nat by lia.
        repeat rewrite pow_add.
        ring. }
    do 2 rewrite <- (Rmult_comm (C ^ (2 * (N - n0) + 1))).
    apply Rmult_le_compat_l.
    { apply pow_le.
      apply Rle_trans with 1.
      { left; apply Rlt_0_1. }
      unfold C; apply RmaxLess1. }
    apply pow_incr.
    split.
    { apply Rabs_pos. }
    unfold C; apply Rle_trans with (Rmax (Rabs x) (Rabs y)).
    - apply RmaxLess1.
    - apply RmaxLess2. }
  apply Rle_trans with
    (sum_f_R0
      (fun k:nat =>
        sum_f_R0
        (fun l:nat =>
          / INR (fact (2 * S (l + k) + 1) * fact (2 * (N - l) + 1)) *
          C ^ (4 * S N)) (pred (N - k))) (pred N)).
  { apply sum_Rle; intros.
    apply sum_Rle; intros.
    apply Rmult_le_compat_l.
    { left; apply Rinv_0_lt_compat.
      rewrite mult_INR; apply Rmult_lt_0_compat; apply INR_fact_lt_0. }
    apply Rle_pow.
    { unfold C; apply RmaxLess1. }
    lia. }
  apply Rle_trans with
    (sum_f_R0
      (fun k:nat =>
        sum_f_R0
        (fun l:nat => C ^ (4 * S N) * Rsqr (/ INR (fact (S (S (N + k))))))
        (pred (N - k))) (pred N)).
  { apply sum_Rle; intros.
    apply sum_Rle; intros.
    rewrite <- (Rmult_comm (C ^ (4 * S N))).
    apply Rmult_le_compat_l.
    { apply pow_le.
      left; apply Rlt_le_trans with 1.
      { apply Rlt_0_1. }
      unfold C; apply RmaxLess1. }
    replace (/ INR (fact (2 * S (n0 + n) + 1) * fact (2 * (N - n0) + 1))) with
      (Binomial.C (2 * S (S (N + n))) (2 * S (n0 + n) + 1) /
                  INR (fact (2 * S (S (N + n))))).
    2:{ unfold Rdiv; rewrite Rmult_comm.
        unfold Binomial.C.
        unfold Rdiv; repeat rewrite <- Rmult_assoc.
        rewrite Rinv_l.
        2:{ apply INR_fact_neq_0. }
        rewrite Rmult_1_l.
        replace (2 * S (S (N + n)) - (2 * S (n0 + n) + 1))%nat with
          (2 * (N - n0) + 1)%nat by lia.
        rewrite mult_INR.
        reflexivity. }
    apply Rle_trans with
      (Binomial.C (2 * S (S (N + n))) (S (S (N + n))) /
                  INR (fact (2 * S (S (N + n))))).
    { unfold Rdiv;
        do 2 rewrite <- (Rmult_comm (/ INR (fact (2 * S (S (N + n)))))).
      apply Rmult_le_compat_l.
      { left; apply Rinv_0_lt_compat; apply INR_fact_lt_0. }
      apply C_maj.
      lia. }
    right.
    unfold Rdiv; rewrite Rmult_comm.
    unfold Binomial.C.
    unfold Rdiv; repeat rewrite <- Rmult_assoc.
    rewrite Rinv_l.
    2:{ apply INR_fact_neq_0. }
    rewrite Rmult_1_l.
    replace (2 * S (S (N + n)) - S (S (N + n)))%nat with (S (S (N + n))) by lia.
    rewrite Rinv_mult.
    unfold Rsqr; reflexivity. }
  apply Rle_trans with
    (sum_f_R0 (fun k:nat => INR N / INR (fact (S (S N))) * C ^ (4 * S N))
      (pred N)).
  { apply sum_Rle; intros.
    rewrite <-
            (scal_sum (fun _:nat => C ^ (4 * S N)) (pred (N - n))
                      (Rsqr (/ INR (fact (S (S (N + n))))))).
    rewrite sum_cte.
    rewrite <- Rmult_assoc.
    do 2 rewrite <- (Rmult_comm (C ^ (4 * S N))).
    rewrite Rmult_assoc.
    apply Rmult_le_compat_l.
    { apply pow_le.
      left; apply Rlt_le_trans with 1.
      { apply Rlt_0_1. }
      unfold C; apply RmaxLess1. }
    apply Rle_trans with (Rsqr (/ INR (fact (S (S (N + n))))) * INR N).
    { apply Rmult_le_compat_l.
      { apply Rle_0_sqr. }
      apply le_INR.
      lia. }
    rewrite Rmult_comm; unfold Rdiv; apply Rmult_le_compat_l.
    { apply pos_INR. }
    apply Rle_trans with (/ INR (fact (S (S (N + n))))).
    { pattern (/ INR (fact (S (S (N + n))))) at 2; rewrite <- Rmult_1_r.
      unfold Rsqr.
      apply Rmult_le_compat_l.
      { left; apply Rinv_0_lt_compat; apply INR_fact_lt_0. }
      apply Rmult_le_reg_l with (INR (fact (S (S (N + n))))).
      { apply INR_fact_lt_0. }
      rewrite Rinv_r.
      { rewrite Rmult_1_r.
        apply (le_INR 1).
        apply Nat.le_succ_l.
        apply INR_lt; apply INR_fact_lt_0. }
      apply INR_fact_neq_0. }
    apply Rmult_le_reg_l with (INR (fact (S (S (N + n))))).
    { apply INR_fact_lt_0. }
    rewrite Rinv_r.
    2:{ apply INR_fact_neq_0. }
    apply Rmult_le_reg_l with (INR (fact (S (S N)))).
    { apply INR_fact_lt_0. }
    rewrite Rmult_1_r.
    rewrite (Rmult_comm (INR (fact (S (S N))))).
    rewrite Rmult_assoc.
    rewrite Rinv_l.
    2:{ apply INR_fact_neq_0. }
    rewrite Rmult_1_r.
    apply le_INR.
    apply fact_le.
    lia. }
  rewrite sum_cte.
  apply Rle_trans with (C ^ (4 * S N) / INR (fact N)).
  2:{ right.
      unfold Majxy.
      unfold C.
      reflexivity. }
  rewrite <- (Rmult_comm (C ^ (4 * S N))).
  unfold Rdiv; rewrite Rmult_assoc; apply Rmult_le_compat_l.
  { apply pow_le.
    left; apply Rlt_le_trans with 1.
    { apply Rlt_0_1. }
    unfold C; apply RmaxLess1. }
  assert (S (pred N) = N) by lia.
  rewrite H0.
  do 2 rewrite fact_simpl.
  repeat rewrite mult_INR.
  repeat rewrite Rinv_mult.
  apply Rle_trans with
    (INR (S (S N)) * (/ INR (S (S N)) * (/ INR (S N) * / INR (fact N))) * INR N).
  { repeat rewrite Rmult_assoc.
    rewrite (Rmult_comm (INR N)).
    rewrite (Rmult_comm (INR (S (S N)))).
    apply Rmult_le_compat_l.
    2:{ apply le_INR. lia. }
    repeat apply Rmult_le_pos;
    left; try apply Rinv_0_lt_compat; try apply INR_fact_lt_0; apply lt_INR_0; try lia. }
  repeat rewrite <- Rmult_assoc.
  rewrite Rinv_r.
  2:{ apply not_O_INR; discriminate. }
  rewrite Rmult_1_l.
  apply Rle_trans with (/ INR (S N) * / INR (fact N) * INR (S N)).
  { repeat rewrite Rmult_assoc.
    repeat apply Rmult_le_compat_l.
    3:{ apply le_INR; apply Nat.le_succ_diag_r. }
    1,2:left; apply Rinv_0_lt_compat.
    { apply lt_INR_0;lia. }
    apply INR_fact_lt_0. }
  rewrite (Rmult_comm (/ INR (S N))).
  rewrite Rmult_assoc.
  rewrite Rinv_l.
  2:{ apply not_O_INR; discriminate. }
  rewrite Rmult_1_r; right; reflexivity.
Qed.

Lemma reste1_cv_R0 : forall x y:R, Un_cv (Reste1 x y) 0.
Proof.
  intros.
  assert (H := Majxy_cv_R0 x y).
  unfold Un_cv in H; unfold Rdist in H.
  unfold Un_cv; unfold Rdist; intros.
  elim (H eps H0); intros N0 H1.
  exists (S N0); intros.
  unfold Rminus; rewrite Ropp_0; rewrite Rplus_0_r.
  apply Rle_lt_trans with (Rabs (Majxy x y (pred n))).
  - rewrite (Rabs_right (Majxy x y (pred n))).
    + apply reste1_maj.
      apply Nat.lt_le_trans with (S N0).
      * apply Nat.lt_0_succ.
      * assumption.
    + apply Rle_ge.
      unfold Majxy.
      unfold Rdiv; apply Rmult_le_pos.
      * apply pow_le.
        apply Rle_trans with 1.
        -- left; apply Rlt_0_1.
        -- apply RmaxLess1.
      * left; apply Rinv_0_lt_compat; apply INR_fact_lt_0.
  - replace (Majxy x y (pred n)) with (Majxy x y (pred n) - 0); [ idtac | ring ].
    apply H1.
    unfold ge; apply le_S_n.
    replace (S (pred n)) with n.
    + assumption.
    + symmetry; apply Nat.lt_succ_pred with 0%nat.
      apply Nat.lt_le_trans with (S N0); [ apply Nat.lt_0_succ | assumption ].
Qed.

Lemma reste2_cv_R0 : forall x y:R, Un_cv (Reste2 x y) 0.
Proof.
  intros.
  assert (H := Majxy_cv_R0 x y).
  unfold Un_cv in H; unfold Rdist in H.
  unfold Un_cv; unfold Rdist; intros.
  elim (H eps H0); intros N0 H1.
  exists (S N0); intros.
  unfold Rminus; rewrite Ropp_0; rewrite Rplus_0_r.
  apply Rle_lt_trans with (Rabs (Majxy x y n)).
  - rewrite (Rabs_right (Majxy x y n)).
    + apply reste2_maj.
      apply Nat.lt_le_trans with (S N0).
      * apply Nat.lt_0_succ.
      * assumption.
    + apply Rle_ge.
      unfold Majxy.
      unfold Rdiv; apply Rmult_le_pos.
      * apply pow_le.
        apply Rle_trans with 1.
        -- left; apply Rlt_0_1.
        -- apply RmaxLess1.
      * left; apply Rinv_0_lt_compat; apply INR_fact_lt_0.
  - replace (Majxy x y n) with (Majxy x y n - 0); [ idtac | ring ].
    apply H1.
    unfold ge; apply Nat.le_trans with (S N0).
    + apply Nat.le_succ_diag_r.
    + exact H2.
Qed.

Lemma reste_cv_R0 : forall x y:R, Un_cv (Reste x y) 0.
Proof.
  intros.
  unfold Reste.
  set (An := fun n:nat => Reste2 x y n).
  set (Bn := fun n:nat => Reste1 x y (S n)).
  cut
    (Un_cv (fun n:nat => An n - Bn n) (0 - 0) ->
      Un_cv (fun N:nat => Reste2 x y N - Reste1 x y (S N)) 0).
  - intro.
    apply H.
    apply CV_minus.
    + unfold An.
      replace (fun n:nat => Reste2 x y n) with (Reste2 x y).
      * apply reste2_cv_R0.
      * reflexivity.
    + unfold Bn.
      assert (H0 := reste1_cv_R0 x y).
      unfold Un_cv in H0; unfold Rdist in H0.
      unfold Un_cv; unfold Rdist; intros.
      elim (H0 eps H1); intros N0 H2.
      exists N0; intros.
      apply H2.
      unfold ge; apply Nat.le_trans with (S N0).
      * apply Nat.le_succ_diag_r.
      * apply -> Nat.succ_le_mono; assumption.
  - unfold An, Bn.
    intro.
    replace 0 with (0 - 0); [ idtac | ring ].
    exact H.
Qed.

Theorem cos_plus : forall x y:R, cos (x + y) = cos x * cos y - sin x * sin y.
Proof.
  intros.
  cut (Un_cv (C1 x y) (cos x * cos y - sin x * sin y)).
  { assert (Un_cv (C1 x y) (cos (x + y))) by apply C1_cvg.
    intros.
    apply UL_sequence with (C1 x y); assumption. }
  unfold Un_cv; unfold Rdist.
  intros.
  assert (H0 := A1_cvg x).
  assert (H1 := A1_cvg y).
  assert (H2 := B1_cvg x).
  assert (H3 := B1_cvg y).
  assert (H4 := CV_mult _ _ _ _ H0 H1).
  assert (H5 := CV_mult _ _ _ _ H2 H3).
  assert (H6 := reste_cv_R0 x y).
  unfold Un_cv in H4; unfold Un_cv in H5; unfold Un_cv in H6.
  unfold Rdist in H4; unfold Rdist in H5; unfold Rdist in H6.
  cut (0 < eps / 3);
    [ intro
      | unfold Rdiv; apply Rmult_lt_0_compat;
        [ assumption | apply Rinv_0_lt_compat; prove_sup0 ] ].
  elim (H4 (eps / 3) H7); intros N1 H8.
  elim (H5 (eps / 3) H7); intros N2 H9.
  elim (H6 (eps / 3) H7); intros N3 H10.
  set (N := S (S (max (max N1 N2) N3))).
  exists N.
  intros.
  assert (n = S (pred n)) by lia.
  rewrite H12.
  rewrite <- cos_plus_form.
  2:lia.
  rewrite <- H12.
  apply Rle_lt_trans with
    (Rabs (A1 x n * A1 y n - cos x * cos y) +
      Rabs (sin x * sin y - B1 x (pred n) * B1 y (pred n) + Reste x y (pred n))).
  { replace
    (A1 x n * A1 y n - B1 x (pred n) * B1 y (pred n) + Reste x y (pred n) -
      (cos x * cos y - sin x * sin y)) with
    (A1 x n * A1 y n - cos x * cos y +
      (sin x * sin y - B1 x (pred n) * B1 y (pred n) + Reste x y (pred n)));
    [ apply Rabs_triang | ring ]. }
  replace eps with (eps / 3 + (eps / 3 + eps / 3)) by field.
  apply Rplus_lt_compat.
  { apply H8. lia. }
  apply Rle_lt_trans with
    (Rabs (sin x * sin y - B1 x (pred n) * B1 y (pred n)) +
       Rabs (Reste x y (pred n))).
  { apply Rabs_triang. }
  apply Rplus_lt_compat.
  { rewrite <- Rabs_Ropp.
    rewrite Ropp_minus_distr.
    apply H9. lia. }
  replace (Reste x y (pred n)) with (Reste x y (pred n) - 0) by ring.
  apply H10. lia.
Qed.
