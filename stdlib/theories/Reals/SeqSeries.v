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
Require Export Rseries.
Require Export SeqProp.
Require Export Rcomplete.
Require Export PartSum.
Require Export AltSeries.
Require Export Binomial.
Require Export Rsigma.
Require Export Rprod.
Require Export Cauchy_prod.
Require Export Alembert.
Require Import Lra.
Require Import Compare_dec.
Local Open Scope R_scope.

(**********)
Lemma sum_maj1 :
  forall (fn:nat -> R -> R) (An:nat -> R) (x l1 l2:R)
    (N:nat),
    Un_cv (fun n:nat => SP fn n x) l1 ->
    Un_cv (fun n:nat => sum_f_R0 An n) l2 ->
    (forall n:nat, Rabs (fn n x) <= An n) ->
    Rabs (l1 - SP fn N x) <= l2 - sum_f_R0 An N.
Proof.
  intros;
    assert (X:{ l:R | Un_cv (fun n => sum_f_R0 (fun l => fn (S N + l)%nat x) n) l }). {
    exists (l1 - SP fn N x).
    unfold Un_cv in H; unfold Un_cv; intros.
    elim (H eps H2); intros N0 H3.
    unfold Rdist in H3; exists N0; intros.
    unfold Rdist, SP.
    replace
      (sum_f_R0 (fun l:nat => fn (S N + l)%nat x) n -
         (l1 - sum_f_R0 (fun k:nat => fn k x) N)) with
      (sum_f_R0 (fun k:nat => fn k x) N +
         sum_f_R0 (fun l:nat => fn (S N + l)%nat x) n - l1);
      [ idtac | ring ].
    replace
      (sum_f_R0 (fun k:nat => fn k x) N +
         sum_f_R0 (fun l:nat => fn (S N + l)%nat x) n) with
      (sum_f_R0 (fun k:nat => fn k x) (S (N + n))).
    { unfold SP in H3; apply H3.
      unfold ge; apply Nat.le_trans with n.
      - apply H4.
      - apply Nat.le_trans with (N + n)%nat.
        + apply Nat.le_add_l.
        + apply Nat.le_succ_diag_r. }
    cut (0 <= N)%nat.
    2:{ apply Nat.le_0_l. }
    cut (N < S (N + n))%nat.
    2:{ apply Nat.lt_succ_r. apply Nat.le_add_r. }
    intros; assert (H7 := sigma_split (fun k:nat => fn k x) H6 H5).
    unfold sigma in H7.
    do 2 rewrite Nat.sub_0_r in H7.
    replace (sum_f_R0 (fun k:nat => fn k x) (S (N + n))) with
      (sum_f_R0 (fun k:nat => fn (0 + k)%nat x) (S (N + n))) by reflexivity.
    replace (sum_f_R0 (fun k:nat => fn k x) N) with
      (sum_f_R0 (fun k:nat => fn (0 + k)%nat x) N) by reflexivity.
    assert ((S (N + n) - S N)%nat = n). {
      apply INR_eq; rewrite minus_INR.
      - do 2 rewrite S_INR; rewrite plus_INR; ring.
      - apply -> Nat.succ_le_mono; apply Nat.le_add_r.
    }
    rewrite H8 in H7.
    apply H7.
  }
  assert { l:R | Un_cv (fun n => sum_f_R0 (fun l => An (S N + l)%nat) n) l } as X0. {
    exists (l2 - sum_f_R0 An N).
    unfold Un_cv in H0; unfold Un_cv; intros.
    elim (H0 eps H2); intros N0 H3.
    unfold Rdist in H3; exists N0; intros.
    unfold Rdist;
      replace (sum_f_R0 (fun l:nat => An (S N + l)%nat) n - (l2 - sum_f_R0 An N))
      with (sum_f_R0 An N + sum_f_R0 (fun l:nat => An (S N + l)%nat) n - l2);
      [ idtac | ring ].
    replace (sum_f_R0 An N + sum_f_R0 (fun l:nat => An (S N + l)%nat) n) with
      (sum_f_R0 An (S (N + n))).
    2:{ cut (0 <= N)%nat.
        2:{ apply Nat.le_0_l. }
        cut (N < S (N + n))%nat.
        2:{ apply Nat.lt_succ_r. apply Nat.le_add_r. }
        intros; assert (H7 := sigma_split An H6 H5).
        unfold sigma in H7.
        do 2 rewrite Nat.sub_0_r in H7.
        replace (sum_f_R0 An (S (N + n))) with
          (sum_f_R0 (fun k:nat => An (0 + k)%nat) (S (N + n))) by reflexivity.
        replace (sum_f_R0 An N) with (sum_f_R0 (fun k:nat => An (0 + k)%nat) N) by reflexivity.
        assert ((S (N + n) - S N)%nat = n). {
          apply INR_eq; rewrite minus_INR.
          - do 2 rewrite S_INR; rewrite plus_INR; ring.
          - apply -> Nat.succ_le_mono; apply Nat.le_add_r.
        }
        rewrite H8 in H7.
        apply H7.
    }
    apply H3; unfold ge; apply Nat.le_trans with n.
    - apply H4.
    - apply Nat.le_trans with (N + n)%nat.
      + apply Nat.le_add_l.
      + apply Nat.le_succ_diag_r.
  }
  elim X; intros l1N H2.
  elim X0; intros l2N H3.
  cut (l1 - SP fn N x = l1N).
  1:intro; cut (l2 - sum_f_R0 An N = l2N).
  { intro; rewrite H4; rewrite H5.
    apply sum_cv_maj with
      (fun l:nat => An (S N + l)%nat) (fun (l:nat) (x:R) => fn (S N + l)%nat x) x.
    - unfold SP; apply H2.
    - apply H3.
    - intros; apply H1. }
  { symmetry ; eapply UL_sequence.
    { apply H3. }
    unfold Un_cv in H0; unfold Un_cv; intros; elim (H0 eps H5);
      intros N0 H6.
    unfold Rdist in H6; exists N0; intros.
    unfold Rdist;
      replace (sum_f_R0 (fun l:nat => An (S N + l)%nat) n - (l2 - sum_f_R0 An N))
      with (sum_f_R0 An N + sum_f_R0 (fun l:nat => An (S N + l)%nat) n - l2);
      [ idtac | ring ].
    replace (sum_f_R0 An N + sum_f_R0 (fun l:nat => An (S N + l)%nat) n) with
      (sum_f_R0 An (S (N + n))).
    { apply H6; unfold ge; apply Nat.le_trans with n.
      - apply H7.
      - apply Nat.le_trans with (N + n)%nat.
        + apply Nat.le_add_l.
        + apply Nat.le_succ_diag_r. }
    cut (0 <= N)%nat.
    2:{ apply Nat.le_0_l. }
    cut (N < S (N + n))%nat.
    2:{ apply Nat.lt_succ_r. apply Nat.le_add_r. }
    intros; assert (H10 := sigma_split An H9 H8).
    unfold sigma in H10.
    do 2 rewrite Nat.sub_0_r in H10.
    replace (sum_f_R0 An (S (N + n))) with
      (sum_f_R0 (fun k:nat => An (0 + k)%nat) (S (N + n))) by reflexivity.
    replace (sum_f_R0 An N) with (sum_f_R0 (fun k:nat => An (0 + k)%nat) N) by reflexivity.
    cut ((S (N + n) - S N)%nat = n).
    { intro; rewrite H11 in H10.
      apply H10. }
    apply INR_eq; rewrite minus_INR.
    - do 2 rewrite S_INR; rewrite plus_INR; ring.
    - apply le_n_S; apply Nat.le_add_r. }
  symmetry ; eapply UL_sequence.
  { apply H2. }
  unfold Un_cv in H; unfold Un_cv; intros.
  elim (H eps H4); intros N0 H5.
  unfold Rdist in H5; exists N0; intros.
  unfold Rdist, SP;
    replace
      (sum_f_R0 (fun l:nat => fn (S N + l)%nat x) n -
         (l1 - sum_f_R0 (fun k:nat => fn k x) N)) with
    (sum_f_R0 (fun k:nat => fn k x) N +
       sum_f_R0 (fun l:nat => fn (S N + l)%nat x) n - l1);
    [ idtac | ring ].
  replace
    (sum_f_R0 (fun k:nat => fn k x) N +
       sum_f_R0 (fun l:nat => fn (S N + l)%nat x) n) with
    (sum_f_R0 (fun k:nat => fn k x) (S (N + n))).
  { unfold SP in H5; apply H5; unfold ge; apply Nat.le_trans with n.
    - apply H6.
    - apply Nat.le_trans with (N + n)%nat.
      + apply Nat.le_add_l.
      + apply Nat.le_succ_diag_r. }
  cut (0 <= N)%nat.
  2:{ apply Nat.le_0_l. }
  cut (N < S (N + n))%nat.
  2:{ apply Nat.lt_succ_r. apply Nat.le_add_r. }
  intros; assert (H9 := sigma_split (fun k:nat => fn k x) H8 H7).
  unfold sigma in H9.
  do 2 rewrite Nat.sub_0_r in H9.
  replace (sum_f_R0 (fun k:nat => fn k x) (S (N + n))) with
    (sum_f_R0 (fun k:nat => fn (0 + k)%nat x) (S (N + n))) by reflexivity.
  replace (sum_f_R0 (fun k:nat => fn k x) N) with
    (sum_f_R0 (fun k:nat => fn (0 + k)%nat x) N) by reflexivity.
  cut ((S (N + n) - S N)%nat = n).
  { intro; rewrite H10 in H9.
    apply H9. }
  apply INR_eq; rewrite minus_INR.
  - do 2 rewrite S_INR; rewrite plus_INR; ring.
  - apply le_n_S; apply Nat.le_add_r.
Qed.

(** Comparaison of convergence for series *)
Lemma Rseries_CV_comp :
  forall An Bn:nat -> R,
    (forall n:nat, 0 <= An n <= Bn n) ->
    { l:R | Un_cv (fun N:nat => sum_f_R0 Bn N) l } ->
    { l:R | Un_cv (fun N:nat => sum_f_R0 An N) l }.
Proof.
  intros An Bn H X; apply cv_cauchy_2.
  assert (H0 := cv_cauchy_1 _ X).
  unfold Cauchy_crit_series; unfold Cauchy_crit.
  intros; elim (H0 eps H1); intros.
  exists x; intros.
  cut
    (Rdist (sum_f_R0 An n) (sum_f_R0 An m) <=
      Rdist (sum_f_R0 Bn n) (sum_f_R0 Bn m)).
  { intro; apply Rle_lt_trans with (Rdist (sum_f_R0 Bn n) (sum_f_R0 Bn m)).
    - assumption.
    - apply H2; assumption. }
  destruct (lt_eq_lt_dec n m) as [[| -> ]|].
  - rewrite (tech2 An n m); [ idtac | assumption ].
    rewrite (tech2 Bn n m); [ idtac | assumption ].
    unfold Rdist; unfold Rminus; do 2 rewrite Ropp_plus_distr;
      do 2 rewrite <- Rplus_assoc; do 2 rewrite Rplus_opp_r;
        do 2 rewrite Rplus_0_l; do 2 rewrite Rabs_Ropp; repeat rewrite Rabs_right.
    + apply sum_Rle; intros.
      elim (H (S n + n0)%nat); intros H7 H8.
      apply H8.
    + apply Rle_ge; apply cond_pos_sum; intro.
      elim (H (S n + n0)%nat); intros.
      apply Rle_trans with (An (S n + n0)%nat); assumption.
    + apply Rle_ge; apply cond_pos_sum; intro.
      elim (H (S n + n0)%nat); intros; assumption.
  - unfold Rdist; unfold Rminus;
    do 2 rewrite Rplus_opp_r; rewrite Rabs_R0; right;
      reflexivity.
  - rewrite (tech2 An m n); [ idtac | assumption ].
    rewrite (tech2 Bn m n); [ idtac | assumption ].
    unfold Rdist; unfold Rminus; do 2 rewrite Rplus_assoc;
      rewrite (Rplus_comm (sum_f_R0 An m)); rewrite (Rplus_comm (sum_f_R0 Bn m));
        do 2 rewrite Rplus_assoc; do 2 rewrite Rplus_opp_l;
          do 2 rewrite Rplus_0_r; repeat rewrite Rabs_right.
    + apply sum_Rle; intros.
      elim (H (S m + n0)%nat); intros H7 H8; apply H8.
    + apply Rle_ge; apply cond_pos_sum; intro.
      elim (H (S m + n0)%nat); intros.
      apply Rle_trans with (An (S m + n0)%nat); assumption.
    + apply Rle_ge.
      apply cond_pos_sum; intro.
      elim (H (S m + n0)%nat); intros; assumption.
Qed.

(** Cesaro's theorem *)
Lemma Cesaro :
  forall (An Bn:nat -> R) (l:R),
    Un_cv Bn l ->
    (forall n:nat, 0 < An n) ->
    cv_infty (fun n:nat => sum_f_R0 An n) ->
    Un_cv (fun n:nat => sum_f_R0 (fun k:nat => An k * Bn k) n / sum_f_R0 An n)
    l.
Proof.
  unfold Un_cv; intros; assert (H3 : forall n:nat, 0 < sum_f_R0 An n).
  { intro; apply tech1; trivial. }
  assert (H4 : forall n:nat, sum_f_R0 An n <> 0).
  { intro; red; intro; assert (H5 := H3 n); rewrite H4 in H5;
    elim (Rlt_irrefl _ H5). }
  assert (H5 := cv_infty_cv_0 _ H1); assert (H6 : 0 < eps / 2).
  { unfold Rdiv; apply Rmult_lt_0_compat.
    - trivial.
    - apply Rinv_0_lt_compat; prove_sup. }
  elim (H _ H6); clear H; intros N1 H;
    set (C := Rabs (sum_f_R0 (fun k:nat => An k * (Bn k - l)) N1));
    assert (H7 : exists N : nat, (forall n:nat, (N <= n)%nat -> C / sum_f_R0 An n < eps / 2)).
  { case (Req_dec C 0); intro.
    - exists 0%nat; intros.
      rewrite H7; unfold Rdiv; rewrite Rmult_0_l; apply Rmult_lt_0_compat.
      + trivial.
      + apply Rinv_0_lt_compat; prove_sup.
    - assert (H8 : 0 < eps / (2 * Rabs C)).
      + unfold Rdiv; apply Rmult_lt_0_compat.
        * trivial.
        * apply Rinv_0_lt_compat; apply Rmult_lt_0_compat.
          -- prove_sup.
          -- apply Rabs_pos_lt;assumption.
      + elim (H5 _ H8); intros; exists x; intros; assert (H11 := H9 _ H10);
          unfold Rdist in H11; unfold Rminus in H11; rewrite Ropp_0 in H11;
          rewrite Rplus_0_r in H11.
        apply Rle_lt_trans with (Rabs (C / sum_f_R0 An n)).
        { apply RRle_abs. }
        unfold Rdiv; rewrite Rabs_mult; apply Rmult_lt_reg_l with (/ Rabs C).
        { apply Rinv_0_lt_compat; apply Rabs_pos_lt;assumption. }
        rewrite <- Rmult_assoc; rewrite Rinv_l.
        * rewrite Rmult_1_l; replace (/ Rabs C * (eps * / 2)) with (eps / (2 * Rabs C)).
          { trivial. }
          field.
          apply Rabs_no_R0;assumption.
        * apply Rabs_no_R0;assumption.
  }
  elim H7; clear H7; intros N2 H7; set (N := max N1 N2); exists (S N); intros;
    unfold Rdist;
    replace (sum_f_R0 (fun k:nat => An k * Bn k) n / sum_f_R0 An n - l) with
    (sum_f_R0 (fun k:nat => An k * (Bn k - l)) n / sum_f_R0 An n).
  2:{ replace (sum_f_R0 (fun k:nat => An k * (Bn k - l)) n) with
        (sum_f_R0 (fun k:nat => An k * Bn k) n +
         sum_f_R0 (fun k:nat => An k * - l) n).
      - rewrite <- (scal_sum An n (- l)); field. trivial.
      - rewrite <- plus_sum; apply sum_eq; intros; ring. }
  assert (H9 : (N1 < n)%nat).
  { apply Nat.lt_le_trans with (S N).
    - apply Nat.lt_succ_r; unfold N; apply Nat.le_max_l.
    - trivial. }
  rewrite (tech2 (fun k:nat => An k * (Bn k - l)) _ _ H9); unfold Rdiv;
    rewrite Rmult_plus_distr_r;
    apply Rle_lt_trans with
    (Rabs (sum_f_R0 (fun k:nat => An k * (Bn k - l)) N1 / sum_f_R0 An n) +
       Rabs (sum_f_R0 (fun i:nat => An (S N1 + i)%nat * (Bn (S N1 + i)%nat - l))
                      (n - S N1) / sum_f_R0 An n)).
  { apply Rabs_triang. }
  rewrite <-(Rplus_half_diag eps); apply Rplus_lt_compat.
  { unfold Rdiv; rewrite Rabs_mult; fold C; rewrite Rabs_right.
    - apply (H7 n); apply Nat.le_trans with (S N).
      + apply Nat.le_trans with N; [ unfold N; apply Nat.le_max_r | apply Nat.le_succ_diag_r ].
      + trivial.
    - apply Rle_ge; left; apply Rinv_0_lt_compat;trivial. }

  unfold Rdist in H; unfold Rdiv; rewrite Rabs_mult;
    rewrite (Rabs_right (/ sum_f_R0 An n)).
  2:{ apply Rle_ge; left; apply Rinv_0_lt_compat;trivial. }
  apply Rle_lt_trans with
    (sum_f_R0 (fun i:nat => Rabs (An (S N1 + i)%nat * (Bn (S N1 + i)%nat - l)))
      (n - S N1) * / sum_f_R0 An n).
  { do 2 rewrite <- (Rmult_comm (/ sum_f_R0 An n)); apply Rmult_le_compat_l.
    - left; apply Rinv_0_lt_compat;trivial.
    - apply (Rsum_abs (fun i:nat => An (S N1 + i)%nat * (Bn (S N1 + i)%nat - l)) (n - S N1)). }
  apply Rle_lt_trans with
    (sum_f_R0 (fun i:nat => An (S N1 + i)%nat * (eps / 2)) (n - S N1) *
      / sum_f_R0 An n).
  - do 2 rewrite <- (Rmult_comm (/ sum_f_R0 An n)); apply Rmult_le_compat_l.
    + left; apply Rinv_0_lt_compat. trivial.
    + apply sum_Rle; intros; rewrite Rabs_mult;
        pattern (An (S N1 + n0)%nat) at 2;
        rewrite <- (Rabs_right (An (S N1 + n0)%nat)).
      * apply Rmult_le_compat_l.
        -- apply Rabs_pos.
        -- left; apply H; unfold ge; apply Nat.le_trans with (S N1);
             [ apply Nat.le_succ_diag_r | apply Nat.le_add_r ].
      * apply Rle_ge; left. trivial.
  - rewrite <- (scal_sum (fun i:nat => An (S N1 + i)%nat) (n - S N1) (eps / 2));
      unfold Rdiv; repeat rewrite Rmult_assoc; apply Rmult_lt_compat_l.
    { trivial. }
    pattern (/ 2) at 2; rewrite <- Rmult_1_r; apply Rmult_lt_compat_l.
    + apply Rinv_0_lt_compat; prove_sup.
    + rewrite Rmult_comm; apply Rmult_lt_reg_l with (sum_f_R0 An n).
      { trivial. }
      rewrite <- Rmult_assoc; rewrite Rinv_r.
      2:{ trivial. }
      rewrite Rmult_1_l; rewrite Rmult_1_r; rewrite (tech2 An N1 n).
      2:{ trivial. }
      rewrite Rplus_comm;
        pattern (sum_f_R0 (fun i:nat => An (S N1 + i)%nat) (n - S N1)) at 1;
        rewrite <- Rplus_0_r; apply Rplus_lt_compat_l.
      trivial.
Qed.

Lemma Cesaro_1 :
  forall (An:nat -> R) (l:R),
    Un_cv An l -> Un_cv (fun n:nat => sum_f_R0 An (pred n) / INR n) l.
Proof.
  intros Bn l H; set (An := fun _:nat => 1).
  assert (H0 : forall n:nat, 0 < An n).
  { intro; unfold An; apply Rlt_0_1. }
  assert (H1 : forall n:nat, 0 < sum_f_R0 An n).
  { intro; apply tech1. trivial. }
  assert (H2 : cv_infty (fun n:nat => sum_f_R0 An n)).
  { unfold cv_infty; intro; destruct (Rle_dec M 0) as [Hle|Hnle].
    - exists 0%nat; intros; apply Rle_lt_trans with 0; trivial.
    - assert (H2 : 0 < M) by auto with real.
      clear Hnle; set (m := up M); elim (archimed M); intros;
        assert (H5 : (0 <= m)%Z).
      + apply le_IZR; unfold m; simpl; left; apply Rlt_trans with M; trivial.
      + elim (IZN _ H5); intros; exists x; intros; unfold An; rewrite sum_cte;
          rewrite Rmult_1_l; apply Rlt_trans with (IZR (up M));trivial.
        apply Rle_lt_trans with (INR x).
        * rewrite INR_IZR_INZ; fold m; rewrite <- H6; right. trivial.
        * apply lt_INR; apply Nat.lt_succ_r. trivial. }
  assert (H3 := Cesaro _ _ _ H H0 H2).
  unfold Un_cv; unfold Un_cv in H3; intros; elim (H3 _ H4); intros;
    exists (S x); intros; unfold Rdist; unfold Rdist in H5;
      apply Rle_lt_trans with
        (Rabs
          (sum_f_R0 (fun k:nat => An k * Bn k) (pred n) / sum_f_R0 An (pred n) - l)).
  - right;
      replace (sum_f_R0 Bn (pred n) / INR n - l) with
      (sum_f_R0 (fun k:nat => An k * Bn k) (pred n) / sum_f_R0 An (pred n) - l);trivial.
    unfold Rminus; do 2 rewrite <- (Rplus_comm (- l));
      apply Rplus_eq_compat_l.
    unfold An;
      replace (sum_f_R0 (fun k:nat => 1 * Bn k) (pred n)) with
      (sum_f_R0 Bn (pred n)).
    + rewrite sum_cte; rewrite Rmult_1_l; replace (S (pred n)) with n;trivial.
      symmetry; apply Nat.lt_succ_pred with 0%nat; apply Nat.lt_le_trans with (S x);trivial.
      apply Nat.lt_0_succ.
    + apply sum_eq; intros; ring.
  - apply H5; unfold ge; apply le_S_n; replace (S (pred n)) with n;trivial.
    symmetry; apply Nat.lt_succ_pred with 0%nat; apply Nat.lt_le_trans with (S x);trivial.
    apply Nat.lt_0_succ.
Qed.
