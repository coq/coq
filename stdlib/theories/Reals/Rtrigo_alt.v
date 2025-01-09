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
Require Import Lia Lra.
Require Import Arith.Factorial.
Local Open Scope R_scope.

(***************************************************************)
(** Using series definitions of cos and sin                    *)
(***************************************************************)

Definition sin_term (a:R) (i:nat) : R :=
  (-1) ^ i * (a ^ (2 * i + 1) / INR (fact (2 * i + 1))).

Definition cos_term (a:R) (i:nat) : R :=
  (-1) ^ i * (a ^ (2 * i) / INR (fact (2 * i))).

Definition sin_approx (a:R) (n:nat) : R := sum_f_R0 (sin_term a) n.

Definition cos_approx (a:R) (n:nat) : R := sum_f_R0 (cos_term a) n.

(**********)
(*
Lemma Alt_PI_4 : Alt_PI <= 4.
Proof.
  assert (H0 := PI_ineq 0).
  elim H0; clear H0; intros _ H0.
  unfold tg_alt, PI_tg in H0; simpl in H0.
  rewrite Rinv_1 in H0; rewrite Rmult_1_r in H0; unfold Rdiv in H0.
  apply Rmult_le_reg_l with (/ 4).
  apply Rinv_0_lt_compat; prove_sup0.
  rewrite Rinv_l; [ rewrite Rmult_comm; assumption | discrR ].
Qed.
*)
(**********)
Theorem pre_sin_bound :
  forall (a:R) (n:nat),
    0 <= a ->
    a <= 4 -> sin_approx a (2 * n + 1) <= sin a <= sin_approx a (2 * (n + 1)).
Proof.
  intros; case (Req_dec a 0); intro Hyp_a.
  { rewrite Hyp_a; rewrite sin_0; split; right; unfold sin_approx;
    apply sum_eq_R0 || (symmetry ; apply sum_eq_R0);
    intros; unfold sin_term; rewrite pow_add;
    simpl; unfold Rdiv; rewrite Rmult_0_l;
    ring. }
  unfold sin_approx; assert (Hyp_a_pos:0 < a) by lra.
  rewrite (decomp_sum (sin_term a) (2 * n + 1)). 2:lia.
  rewrite (decomp_sum (sin_term a) (2 * (n + 1))). 2:lia.
  replace (sin_term a 0) with a.
  2:{ unfold sin_term; simpl; unfold Rdiv; rewrite Rinv_1;
      ring. }
  assert
    (sum_f_R0 (fun i:nat => sin_term a (S i)) (pred (2 * n + 1)) <= sin a - a /\
      sin a - a <= sum_f_R0 (fun i:nat => sin_term a (S i)) (pred (2 * (n + 1))) ->
      a + sum_f_R0 (fun i:nat => sin_term a (S i)) (pred (2 * n + 1)) <= sin a /\
      sin a <= a + sum_f_R0 (fun i:nat => sin_term a (S i)) (pred (2 * (n + 1)))) by lra.
  apply H1.
  set (Un := fun n:nat => a ^ (2 * S n + 1) / INR (fact (2 * S n + 1))).
  replace (pred (2 * n + 1)) with (2 * n)%nat by lia.
  replace (pred (2 * (n + 1))) with (S (2 * n)) by lia.
  replace (sum_f_R0 (fun i:nat => sin_term a (S i)) (2 * n)) with
    (- sum_f_R0 (tg_alt Un) (2 * n)).
  2:{ replace (- sum_f_R0 (tg_alt Un) (2 * n)) with
      (-1 * sum_f_R0 (tg_alt Un) (2 * n)) by ring.
      rewrite scal_sum.
      apply sum_eq; intros.
      unfold sin_term, Un, tg_alt;
        change ((-1) ^ S i) with (-1 * (-1) ^ i).
      unfold Rdiv; ring. }
  replace (sum_f_R0 (fun i:nat => sin_term a (S i)) (S (2 * n))) with
  (- sum_f_R0 (tg_alt Un) (S (2 * n))).
  2:{ replace (- sum_f_R0 (tg_alt Un) (S (2 * n))) with
      (-1 * sum_f_R0 (tg_alt Un) (S (2 * n))); [ rewrite scal_sum | ring ].
      apply sum_eq; intros; unfold sin_term, Un, tg_alt;
        change ((-1) ^ S i) with (-1 * (-1) ^ i).
      unfold Rdiv; ring. }
  assert
    (sum_f_R0 (tg_alt Un) (S (2 * n)) <= a - sin a <=
      sum_f_R0 (tg_alt Un) (2 * n) ->
      - sum_f_R0 (tg_alt Un) (2 * n) <= sin a - a <=
      - sum_f_R0 (tg_alt Un) (S (2 * n))) by lra.
  apply H2.
  apply alternated_series_ineq.
  - unfold Un_decreasing, Un; intro;
      assert ((2 * S (S n0) + 1)%nat = S (S (2 * S n0 + 1))) by lia.
    rewrite H3.
    replace (a ^ S (S (2 * S n0 + 1))) with (a ^ (2 * S n0 + 1) * (a * a)) by (simpl;ring).
    unfold Rdiv; rewrite Rmult_assoc; apply Rmult_le_compat_l.
    { left; apply pow_lt; assumption. }
    apply Rmult_le_reg_l with (INR (fact (S (S (2 * S n0 + 1))))).
    { rewrite <- H3; apply lt_INR_0; apply Nat.neq_0_lt_0; red; intro;
      elim (fact_neq_0 _ H4). }
    rewrite <- H3; rewrite (Rmult_comm (INR (fact (2 * S (S n0) + 1))));
      rewrite Rmult_assoc; rewrite Rinv_l.
    2:{ apply INR_fact_neq_0. }
    rewrite Rmult_1_r; rewrite H3; do 2 rewrite fact_simpl; do 2 rewrite mult_INR;
      repeat rewrite Rmult_assoc; rewrite Rinv_r.
    2:{ apply INR_fact_neq_0. }
    rewrite Rmult_1_r.
    do 2 rewrite S_INR; rewrite plus_INR; rewrite mult_INR; repeat rewrite S_INR;
    simpl;
    replace
      (((0 + 1 + 1) * (INR n0 + 1) + (0 + 1) + 1 + 1) *
         ((0 + 1 + 1) * (INR n0 + 1) + (0 + 1) + 1)) with
      (4 * INR n0 * INR n0 + 18 * INR n0 + 20); [ idtac | ring ].
    apply Rle_trans with 20.
    + apply Rle_trans with 16.
      2:lra.
      replace 16 with (Rsqr 4); [ idtac | ring_Rsqr ].
      apply Rsqr_incr_1;lra.
    + rewrite <- (Rplus_0_l 20) at 1;
        apply Rplus_le_compat_r.
      pose proof (pos_INR n0). nra.
  - assert (H3 := cv_speed_pow_fact a); unfold Un; unfold Un_cv in H3;
      unfold Rdist in H3; unfold Un_cv; unfold Rdist;
      intros; elim (H3 eps H4); intros N H5.
    exists N; intros; apply H5.
    lia.
  - unfold sin.
    destruct (exist_sin (Rsqr a)) as (x,p).
    unfold sin_in, infinite_sum, Rdist in p;
      unfold Un_cv, Rdist;
      intros.
    assert (H4:0 < eps / Rabs a). {
      unfold Rdiv; apply Rmult_lt_0_compat.
      - assumption.
      - apply Rinv_0_lt_compat; apply Rabs_pos_lt; assumption.
    }
    destruct (p _ H4) as (N,H6).
    exists N; intros.
    replace (sum_f_R0 (tg_alt Un) n0) with
      (a * (1 - sum_f_R0 (fun i:nat => sin_n i * Rsqr a ^ i) (S n0))).
    { unfold Rminus; rewrite Rmult_plus_distr_l; rewrite Rmult_1_r;
      rewrite Ropp_plus_distr; rewrite Ropp_involutive;
      repeat rewrite Rplus_assoc; rewrite (Rplus_comm a);
      rewrite (Rplus_comm (- a)); repeat rewrite Rplus_assoc;
      rewrite Rplus_opp_l; rewrite Rplus_0_r; apply Rmult_lt_reg_l with (/ Rabs a).
      { apply Rinv_0_lt_compat; apply Rabs_pos_lt; assumption. }
      pattern (/ Rabs a) at 1; rewrite <- (Rabs_inv a).
      rewrite <- Rabs_mult, Rmult_plus_distr_l, <- 2!Rmult_assoc, Rinv_l;
      [ rewrite Rmult_1_l | assumption ];
      rewrite (Rmult_comm (/ Rabs a)), <- Rabs_Ropp, Ropp_plus_distr, Ropp_involutive, Rmult_1_l.
      unfold Rminus, Rdiv in H6. apply H6; unfold ge;
      apply Nat.le_trans with n0; [ exact H5 | apply Nat.le_succ_diag_r ]. }
    rewrite (decomp_sum (fun i:nat => sin_n i * Rsqr a ^ i) (S n0)).
    2:lia.
    replace (sin_n 0) with 1.
    2:{ unfold sin_n; unfold Rdiv; simpl; rewrite Rinv_1;
        rewrite Rmult_1_r; reflexivity. }
    simpl; rewrite Rmult_1_r; unfold Rminus;
      rewrite Ropp_plus_distr; rewrite <- Rplus_assoc; rewrite Rplus_opp_r;
      rewrite Rplus_0_l; rewrite Ropp_mult_distr_r_reverse;
      rewrite <- Ropp_mult_distr_l_reverse; rewrite scal_sum;
      apply sum_eq.
    intros; unfold sin_n, Un, tg_alt;
      replace ((-1) ^ S i) with (- (-1) ^ i) by (simpl;ring).
    replace (a ^ (2 * S i + 1)) with (Rsqr a * Rsqr a ^ i * a).
    { unfold Rdiv; ring. }
    rewrite pow_add; rewrite pow_Rsqr; simpl; ring.
Qed.

(**********)
Lemma pre_cos_bound :
  forall (a:R) (n:nat),
    - 2 <= a -> a <= 2 ->
    cos_approx a (2 * n + 1) <= cos a <= cos_approx a (2 * (n + 1)).
Proof.
  assert
    (H:(forall (a:R) (n:nat),
      0 <= a ->
      a <= 2 ->
      cos_approx a (2 * n + 1) <= cos a <= cos_approx a (2 * (n + 1))) ->
    forall (a:R) (n:nat),
      - 2 <= a ->
      a <= 2 ->
      cos_approx a (2 * n + 1) <= cos a <= cos_approx a (2 * (n + 1))). {
    intros; destruct (total_order_T 0 a) as [[Hlt|Heq]|Hgt];try (apply H;lra).
    assert (0 < - a) by lra.
    cut (forall (x:R) (n:nat), cos_approx x n = cos_approx (- x) n).
    { intro; rewrite H3; rewrite (H3 a (2 * (n + 1))%nat); rewrite cos_sym; apply H;lra. }
    intros; unfold cos_approx; apply sum_eq; intros;
      unfold cos_term; do 2 rewrite pow_Rsqr; rewrite Rsqr_neg;
      unfold Rdiv; reflexivity.
  }
  intros a n; apply H.
  intros; unfold cos_approx.
  rewrite (decomp_sum (cos_term a0) (2 * n0 + 1)). 2:lia.
  rewrite (decomp_sum (cos_term a0) (2 * (n0 + 1))). 2:lia.
  replace (cos_term a0 0) with 1.
  2:{ unfold cos_term; simpl; unfold Rdiv; rewrite Rinv_1;
      ring. }
  assert
    (sum_f_R0 (fun i:nat => cos_term a0 (S i)) (pred (2 * n0 + 1)) <= cos a0 - 1 /\
      cos a0 - 1 <=
      sum_f_R0 (fun i:nat => cos_term a0 (S i)) (pred (2 * (n0 + 1))) ->
      1 + sum_f_R0 (fun i:nat => cos_term a0 (S i)) (pred (2 * n0 + 1)) <= cos a0 /\
      cos a0 <=
      1 + sum_f_R0 (fun i:nat => cos_term a0 (S i)) (pred (2 * (n0 + 1)))). {
    intro; elim H2; intros; split;
    apply Rplus_le_reg_l with (-(1));
    rewrite <- Rplus_assoc; rewrite Rplus_opp_l; rewrite Rplus_0_l;
    rewrite (Rplus_comm (-1));assumption.
  }
  apply H2.
  set (Un := fun n:nat => a0 ^ (2 * S n) / INR (fact (2 * S n))).
  replace (pred (2 * n0 + 1)) with (2 * n0)%nat by lia.
  replace (pred (2 * (n0 + 1))) with (S (2 * n0)) by lia.
  replace (sum_f_R0 (fun i:nat => cos_term a0 (S i)) (2 * n0)) with
    (- sum_f_R0 (tg_alt Un) (2 * n0)).
  2:{ replace (- sum_f_R0 (tg_alt Un) (2 * n0)) with
    (-1 * sum_f_R0 (tg_alt Un) (2 * n0)); [ rewrite scal_sum | ring ];
      apply sum_eq; intros; unfold cos_term, Un, tg_alt;
      change ((-1) ^ S i) with (-1 * (-1) ^ i).
      unfold Rdiv; ring. }
  replace (sum_f_R0 (fun i:nat => cos_term a0 (S i)) (S (2 * n0))) with
    (- sum_f_R0 (tg_alt Un) (S (2 * n0))).
  2:{ replace (- sum_f_R0 (tg_alt Un) (S (2 * n0))) with
        (-1 * sum_f_R0 (tg_alt Un) (S (2 * n0))); [ rewrite scal_sum | ring ].
      apply sum_eq; intros; unfold cos_term, Un, tg_alt;
        change ((-1) ^ S i) with (-1 * (-1) ^ i).
      unfold Rdiv; ring. }
  assert
    (sum_f_R0 (tg_alt Un) (S (2 * n0)) <= 1 - cos a0 <=
      sum_f_R0 (tg_alt Un) (2 * n0) ->
      - sum_f_R0 (tg_alt Un) (2 * n0) <= cos a0 - 1 <=
      - sum_f_R0 (tg_alt Un) (S (2 * n0))) by lra.
  apply H3.
  apply alternated_series_ineq.
  - unfold Un_decreasing; intro; unfold Un.
    assert ((2 * S (S n1))%nat = S (S (2 * S n1))) by lia.
    rewrite H4;
      replace (a0 ^ S (S (2 * S n1))) with (a0 ^ (2 * S n1) * (a0 * a0)) by (simpl;ring).
    unfold Rdiv; rewrite Rmult_assoc; apply Rmult_le_compat_l.
    { apply pow_le; assumption. }
    apply Rmult_le_reg_l with (INR (fact (S (S (2 * S n1))))).
    { apply INR_fact_lt_0. }
    rewrite <- H4; rewrite (Rmult_comm (INR (fact (2 * S (S n1)))));
      rewrite Rmult_assoc; rewrite Rinv_l.
    2:(pose proof (INR_fact_lt_0  (2 * S (S n1)));lra).
    rewrite Rmult_1_r; rewrite H4; do 2 rewrite fact_simpl; do 2 rewrite mult_INR;
      repeat rewrite Rmult_assoc; rewrite Rinv_r.
    2:(pose proof (INR_fact_lt_0  (2 * S n1));lra).
    rewrite Rmult_1_r; do 2 rewrite S_INR; rewrite mult_INR; repeat rewrite S_INR;
      simpl;
      replace
        (((0 + 1 + 1) * (INR n1 + 1) + 1 + 1) * ((0 + 1 + 1) * (INR n1 + 1) + 1))
      with (4 * INR n1 * INR n1 + 14 * INR n1 + 12); [ idtac | ring ].
    apply Rle_trans with 12.
    { nra. }
    pose proof (pos_INR n1);nra.
  -  assert (H4 := cv_speed_pow_fact a0); unfold Un; unfold Un_cv in H4;
       unfold Rdist in H4; unfold Un_cv; unfold Rdist;
       intros; elim (H4 eps H5); intros N H6; exists N; intros.
     apply H6; nia.
  - unfold cos. destruct (exist_cos (Rsqr a0)) as (x,p).
    unfold cos_in, infinite_sum, Rdist in p;
      unfold Un_cv, Rdist; intros.
    destruct (p _ H4) as (N,H6).
    exists N; intros.
    replace (sum_f_R0 (tg_alt Un) n1) with
      (1 - sum_f_R0 (fun i:nat => cos_n i * Rsqr a0 ^ i) (S n1)).
    { unfold Rminus; rewrite Ropp_plus_distr; rewrite Ropp_involutive;
      repeat rewrite Rplus_assoc; rewrite (Rplus_comm 1);
      rewrite (Rplus_comm (-(1))); repeat rewrite Rplus_assoc;
      rewrite Rplus_opp_l; rewrite Rplus_0_r; rewrite <- Rabs_Ropp;
      rewrite Ropp_plus_distr; rewrite Ropp_involutive;
      unfold Rminus in H6; apply H6.
      lia. }
    rewrite (decomp_sum (fun i:nat => cos_n i * Rsqr a0 ^ i) (S n1)).
    2:lia.
    replace (cos_n 0) with 1.
    2:{ unfold cos_n; unfold Rdiv; simpl; rewrite Rinv_1;
        rewrite Rmult_1_r; reflexivity. }
    simpl; rewrite Rmult_1_r; unfold Rminus;
      rewrite Ropp_plus_distr; rewrite <- Rplus_assoc; rewrite Rplus_opp_r;
      rewrite Rplus_0_l;
      replace (- sum_f_R0 (fun i:nat => cos_n (S i) * (Rsqr a0 * Rsqr a0 ^ i)) n1)
      with
      (-1 * sum_f_R0 (fun i:nat => cos_n (S i) * (Rsqr a0 * Rsqr a0 ^ i)) n1);
      [ idtac | ring ]; rewrite scal_sum; apply sum_eq;
      intros; unfold cos_n, Un, tg_alt.
    replace ((-1) ^ S i) with (- (-1) ^ i) by (simpl;ring).
    replace (a0 ^ (2 * S i)) with (Rsqr a0 * Rsqr a0 ^ i) by (rewrite pow_Rsqr; reflexivity).
    unfold Rdiv; ring.
Qed.
