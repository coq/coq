(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Import Rbase.
Require Import Rfunctions.
Require Import SeqSeries.
Require Import Rtrigo_def.
Open Local Scope R_scope.

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
Lemma PI_4 : PI <= 4.
Proof.
  assert (H0 := PI_ineq 0).
  elim H0; clear H0; intros _ H0.
  unfold tg_alt, PI_tg in H0; simpl in H0.
  rewrite Rinv_1 in H0; rewrite Rmult_1_r in H0; unfold Rdiv in H0.
  apply Rmult_le_reg_l with (/ 4).
  apply Rinv_0_lt_compat; prove_sup0.
  rewrite <- Rinv_l_sym; [ rewrite Rmult_comm; assumption | discrR ].
Qed.

(**********)
Theorem sin_bound :
  forall (a:R) (n:nat),
    0 <= a ->
    a <= PI -> sin_approx a (2 * n + 1) <= sin a <= sin_approx a (2 * (n + 1)).
Proof.
  intros; case (Req_dec a 0); intro Hyp_a.
  rewrite Hyp_a; rewrite sin_0; split; right; unfold sin_approx in |- *;
    apply sum_eq_R0 || (symmetry  in |- *; apply sum_eq_R0);
      intros; unfold sin_term in |- *; rewrite pow_add;
        simpl in |- *; unfold Rdiv in |- *; rewrite Rmult_0_l;
          ring.
  unfold sin_approx in |- *; cut (0 < a).
  intro Hyp_a_pos.
  rewrite (decomp_sum (sin_term a) (2 * n + 1)).
  rewrite (decomp_sum (sin_term a) (2 * (n + 1))).
  replace (sin_term a 0) with a.
  cut
    (sum_f_R0 (fun i:nat => sin_term a (S i)) (pred (2 * n + 1)) <= sin a - a /\
      sin a - a <= sum_f_R0 (fun i:nat => sin_term a (S i)) (pred (2 * (n + 1))) ->
      a + sum_f_R0 (fun i:nat => sin_term a (S i)) (pred (2 * n + 1)) <= sin a /\
      sin a <= a + sum_f_R0 (fun i:nat => sin_term a (S i)) (pred (2 * (n + 1)))).
  intro; apply H1.
  set (Un := fun n:nat => a ^ (2 * S n + 1) / INR (fact (2 * S n + 1))).
  replace (pred (2 * n + 1)) with (2 * n)%nat.
  replace (pred (2 * (n + 1))) with (S (2 * n)).
  replace (sum_f_R0 (fun i:nat => sin_term a (S i)) (2 * n)) with
  (- sum_f_R0 (tg_alt Un) (2 * n)).
  replace (sum_f_R0 (fun i:nat => sin_term a (S i)) (S (2 * n))) with
  (- sum_f_R0 (tg_alt Un) (S (2 * n))).
  cut
    (sum_f_R0 (tg_alt Un) (S (2 * n)) <= a - sin a <=
      sum_f_R0 (tg_alt Un) (2 * n) ->
      - sum_f_R0 (tg_alt Un) (2 * n) <= sin a - a <=
      - sum_f_R0 (tg_alt Un) (S (2 * n))).
  intro; apply H2.
  apply alternated_series_ineq.
  unfold Un_decreasing, Un in |- *; intro;
    cut ((2 * S (S n0) + 1)%nat = S (S (2 * S n0 + 1))).
  intro; rewrite H3.
  replace (a ^ S (S (2 * S n0 + 1))) with (a ^ (2 * S n0 + 1) * (a * a)).
  unfold Rdiv in |- *; rewrite Rmult_assoc; apply Rmult_le_compat_l.
  left; apply pow_lt; assumption.
  apply Rmult_le_reg_l with (INR (fact (S (S (2 * S n0 + 1))))).
  rewrite <- H3; apply lt_INR_0; apply neq_O_lt; red in |- *; intro;
    assert (H5 := sym_eq H4); elim (fact_neq_0 _ H5).
  rewrite <- H3; rewrite (Rmult_comm (INR (fact (2 * S (S n0) + 1))));
    rewrite Rmult_assoc; rewrite <- Rinv_l_sym.
  rewrite Rmult_1_r; rewrite H3; do 2 rewrite fact_simpl; do 2 rewrite mult_INR;
    repeat rewrite Rmult_assoc; rewrite <- Rinv_r_sym.
  rewrite Rmult_1_r.
  do 2 rewrite S_INR; rewrite plus_INR; rewrite mult_INR; repeat rewrite S_INR;
    simpl in |- *;
      replace
      (((0 + 1 + 1) * (INR n0 + 1) + (0 + 1) + 1 + 1) *
        ((0 + 1 + 1) * (INR n0 + 1) + (0 + 1) + 1)) with
      (4 * INR n0 * INR n0 + 18 * INR n0 + 20); [ idtac | ring ].
  apply Rle_trans with 20.
  apply Rle_trans with 16.
  replace 16 with (Rsqr 4); [ idtac | ring_Rsqr ].
  replace (a * a) with (Rsqr a); [ idtac | reflexivity ].
  apply Rsqr_incr_1.
  apply Rle_trans with PI; [ assumption | apply PI_4 ].
  assumption.
  left; prove_sup0.
  rewrite <- (Rplus_0_r 16); replace 20 with (16 + 4);
    [ apply Rplus_le_compat_l; left; prove_sup0 | ring ].
  rewrite <- (Rplus_comm 20); pattern 20 at 1 in |- *; rewrite <- Rplus_0_r;
    apply Rplus_le_compat_l.
  apply Rplus_le_le_0_compat.
  repeat apply Rmult_le_pos.
  left; prove_sup0.
  left; prove_sup0.
  replace 0 with (INR 0); [ apply le_INR; apply le_O_n | reflexivity ].
  replace 0 with (INR 0); [ apply le_INR; apply le_O_n | reflexivity ].
  apply Rmult_le_pos.
  left; prove_sup0.
  replace 0 with (INR 0); [ apply le_INR; apply le_O_n | reflexivity ].
  apply INR_fact_neq_0.
  apply INR_fact_neq_0.
  simpl in |- *; ring.
  ring.
  assert (H3 := cv_speed_pow_fact a); unfold Un in |- *; unfold Un_cv in H3;
    unfold R_dist in H3; unfold Un_cv in |- *; unfold R_dist in |- *;
      intros; elim (H3 eps H4); intros N H5.
  exists N; intros; apply H5.
  replace (2 * S n0 + 1)%nat with (S (2 * S n0)).
  unfold ge in |- *; apply le_trans with (2 * S n0)%nat.
  apply le_trans with (2 * S N)%nat.
  apply le_trans with (2 * N)%nat.
  apply le_n_2n.
  apply (fun m n p:nat => mult_le_compat_l p n m); apply le_n_Sn.
  apply (fun m n p:nat => mult_le_compat_l p n m); apply le_n_S; assumption.
  apply le_n_Sn.
  ring.
  assert (X := exist_sin (Rsqr a)); elim X; intros.
  cut (x = sin a / a).
  intro; rewrite H3 in p; unfold sin_in in p; unfold infinite_sum in p;
    unfold R_dist in p; unfold Un_cv in |- *; unfold R_dist in |- *;
      intros.
  cut (0 < eps / Rabs a).
  intro; elim (p _ H5); intros N H6.
  exists N; intros.
  replace (sum_f_R0 (tg_alt Un) n0) with
  (a * (1 - sum_f_R0 (fun i:nat => sin_n i * Rsqr a ^ i) (S n0))).
  unfold Rminus in |- *; rewrite Rmult_plus_distr_l; rewrite Rmult_1_r;
    rewrite Ropp_plus_distr; rewrite Ropp_involutive;
      repeat rewrite Rplus_assoc; rewrite (Rplus_comm a);
        rewrite (Rplus_comm (- a)); repeat rewrite Rplus_assoc;
          rewrite Rplus_opp_l; rewrite Rplus_0_r; apply Rmult_lt_reg_l with (/ Rabs a).
  apply Rinv_0_lt_compat; apply Rabs_pos_lt; assumption.
  pattern (/ Rabs a) at 1 in |- *; rewrite <- (Rabs_Rinv a Hyp_a).
  rewrite <- Rabs_mult; rewrite Rmult_plus_distr_l; rewrite <- Rmult_assoc;
    rewrite <- Rinv_l_sym; [ rewrite Rmult_1_l | assumption ];
      rewrite (Rmult_comm (/ a)); rewrite (Rmult_comm (/ Rabs a));
        rewrite <- Rabs_Ropp; rewrite Ropp_plus_distr; rewrite Ropp_involutive;
          unfold Rminus, Rdiv in H6; apply H6; unfold ge in |- *;
            apply le_trans with n0; [ exact H7 | apply le_n_Sn ].
  rewrite (decomp_sum (fun i:nat => sin_n i * Rsqr a ^ i) (S n0)).
  replace (sin_n 0) with 1.
  simpl in |- *; rewrite Rmult_1_r; unfold Rminus in |- *;
    rewrite Ropp_plus_distr; rewrite <- Rplus_assoc; rewrite Rplus_opp_r;
      rewrite Rplus_0_l; rewrite Ropp_mult_distr_r_reverse;
        rewrite <- Ropp_mult_distr_l_reverse; rewrite scal_sum;
          apply sum_eq.
  intros; unfold sin_n, Un, tg_alt in |- *;
    replace ((-1) ^ S i) with (- (-1) ^ i).
  replace (a ^ (2 * S i + 1)) with (Rsqr a * Rsqr a ^ i * a).
  unfold Rdiv in |- *; ring.
  rewrite pow_add; rewrite pow_Rsqr; simpl in |- *; ring.
  simpl in |- *; ring.
  unfold sin_n in |- *; unfold Rdiv in |- *; simpl in |- *; rewrite Rinv_1;
    rewrite Rmult_1_r; reflexivity.
  apply lt_O_Sn.
  unfold Rdiv in |- *; apply Rmult_lt_0_compat.
  assumption.
  apply Rinv_0_lt_compat; apply Rabs_pos_lt; assumption.
  unfold sin in |- *; case (exist_sin (Rsqr a)).
  intros; cut (x = x0).
  intro; rewrite H3; unfold Rdiv in |- *.
  symmetry  in |- *; apply Rinv_r_simpl_m; assumption.
  unfold sin_in in p; unfold sin_in in s; eapply uniqueness_sum.
  apply p.
  apply s.
  intros; elim H2; intros.
  replace (sin a - a) with (- (a - sin a)); [ idtac | ring ].
  split; apply Ropp_le_contravar; assumption.
  replace (- sum_f_R0 (tg_alt Un) (S (2 * n))) with
  (-1 * sum_f_R0 (tg_alt Un) (S (2 * n))); [ rewrite scal_sum | ring ].
  apply sum_eq; intros; unfold sin_term, Un, tg_alt in |- *;
    replace ((-1) ^ S i) with (-1 * (-1) ^ i).
  unfold Rdiv in |- *; ring.
  reflexivity.
  replace (- sum_f_R0 (tg_alt Un) (2 * n)) with
  (-1 * sum_f_R0 (tg_alt Un) (2 * n)); [ rewrite scal_sum | ring ].
  apply sum_eq; intros.
  unfold sin_term, Un, tg_alt in |- *;
    replace ((-1) ^ S i) with (-1 * (-1) ^ i).
  unfold Rdiv in |- *; ring.
  reflexivity.
  replace (2 * (n + 1))%nat with (S (S (2 * n))).
  reflexivity.
  ring.
  replace (2 * n + 1)%nat with (S (2 * n)).
  reflexivity.
  ring.
  intro; elim H1; intros.
  split.
  apply Rplus_le_reg_l with (- a).
  rewrite <- Rplus_assoc; rewrite Rplus_opp_l; rewrite Rplus_0_l;
    rewrite (Rplus_comm (- a)); apply H2.
  apply Rplus_le_reg_l with (- a).
  rewrite <- Rplus_assoc; rewrite Rplus_opp_l; rewrite Rplus_0_l;
    rewrite (Rplus_comm (- a)); apply H3.
  unfold sin_term in |- *; simpl in |- *; unfold Rdiv in |- *; rewrite Rinv_1;
    ring.
  replace (2 * (n + 1))%nat with (S (S (2 * n))).
  apply lt_O_Sn.
  ring.
  replace (2 * n + 1)%nat with (S (2 * n)).
  apply lt_O_Sn.
  ring.
  inversion H; [ assumption | elim Hyp_a; symmetry  in |- *; assumption ].
Qed.

(**********)
Lemma cos_bound :
  forall (a:R) (n:nat),
    - PI / 2 <= a ->
    a <= PI / 2 ->
    cos_approx a (2 * n + 1) <= cos a <= cos_approx a (2 * (n + 1)).
Proof.
  cut
    ((forall (a:R) (n:nat),
      0 <= a ->
      a <= PI / 2 ->
      cos_approx a (2 * n + 1) <= cos a <= cos_approx a (2 * (n + 1))) ->
    forall (a:R) (n:nat),
      - PI / 2 <= a ->
      a <= PI / 2 ->
      cos_approx a (2 * n + 1) <= cos a <= cos_approx a (2 * (n + 1))).
  intros H a n; apply H.
  intros; unfold cos_approx in |- *.
  rewrite (decomp_sum (cos_term a0) (2 * n0 + 1)).
  rewrite (decomp_sum (cos_term a0) (2 * (n0 + 1))).
  replace (cos_term a0 0) with 1.
  cut
    (sum_f_R0 (fun i:nat => cos_term a0 (S i)) (pred (2 * n0 + 1)) <= cos a0 - 1 /\
      cos a0 - 1 <=
      sum_f_R0 (fun i:nat => cos_term a0 (S i)) (pred (2 * (n0 + 1))) ->
      1 + sum_f_R0 (fun i:nat => cos_term a0 (S i)) (pred (2 * n0 + 1)) <= cos a0 /\
      cos a0 <=
      1 + sum_f_R0 (fun i:nat => cos_term a0 (S i)) (pred (2 * (n0 + 1)))).
  intro; apply H2.
  set (Un := fun n:nat => a0 ^ (2 * S n) / INR (fact (2 * S n))).
  replace (pred (2 * n0 + 1)) with (2 * n0)%nat.
  replace (pred (2 * (n0 + 1))) with (S (2 * n0)).
  replace (sum_f_R0 (fun i:nat => cos_term a0 (S i)) (2 * n0)) with
  (- sum_f_R0 (tg_alt Un) (2 * n0)).
  replace (sum_f_R0 (fun i:nat => cos_term a0 (S i)) (S (2 * n0))) with
  (- sum_f_R0 (tg_alt Un) (S (2 * n0))).
  cut
    (sum_f_R0 (tg_alt Un) (S (2 * n0)) <= 1 - cos a0 <=
      sum_f_R0 (tg_alt Un) (2 * n0) ->
      - sum_f_R0 (tg_alt Un) (2 * n0) <= cos a0 - 1 <=
      - sum_f_R0 (tg_alt Un) (S (2 * n0))).
  intro; apply H3.
  apply alternated_series_ineq.
  unfold Un_decreasing in |- *; intro; unfold Un in |- *.
  cut ((2 * S (S n1))%nat = S (S (2 * S n1))).
  intro; rewrite H4;
    replace (a0 ^ S (S (2 * S n1))) with (a0 ^ (2 * S n1) * (a0 * a0)).
  unfold Rdiv in |- *; rewrite Rmult_assoc; apply Rmult_le_compat_l.
  apply pow_le; assumption.
  apply Rmult_le_reg_l with (INR (fact (S (S (2 * S n1))))).
  rewrite <- H4; apply lt_INR_0; apply neq_O_lt; red in |- *; intro;
    assert (H6 := sym_eq H5); elim (fact_neq_0 _ H6).
  rewrite <- H4; rewrite (Rmult_comm (INR (fact (2 * S (S n1)))));
    rewrite Rmult_assoc; rewrite <- Rinv_l_sym.
  rewrite Rmult_1_r; rewrite H4; do 2 rewrite fact_simpl; do 2 rewrite mult_INR;
    repeat rewrite Rmult_assoc; rewrite <- Rinv_r_sym.
  rewrite Rmult_1_r; do 2 rewrite S_INR; rewrite mult_INR; repeat rewrite S_INR;
    simpl in |- *;
      replace
      (((0 + 1 + 1) * (INR n1 + 1) + 1 + 1) * ((0 + 1 + 1) * (INR n1 + 1) + 1))
    with (4 * INR n1 * INR n1 + 14 * INR n1 + 12); [ idtac | ring ].
  apply Rle_trans with 12.
  apply Rle_trans with 4.
  replace 4 with (Rsqr 2); [ idtac | ring_Rsqr ].
  replace (a0 * a0) with (Rsqr a0); [ idtac | reflexivity ].
  apply Rsqr_incr_1.
  apply Rle_trans with (PI / 2).
  assumption.
  unfold Rdiv in |- *; apply Rmult_le_reg_l with 2.
  prove_sup0.
  rewrite <- Rmult_assoc; rewrite Rinv_r_simpl_m.
  replace 4 with 4; [ apply PI_4 | ring ].
  discrR.
  assumption.
  left; prove_sup0.
  pattern 4 at 1 in |- *; rewrite <- Rplus_0_r; replace 12 with (4 + 8);
    [ apply Rplus_le_compat_l; left; prove_sup0 | ring ].
  rewrite <- (Rplus_comm 12); pattern 12 at 1 in |- *; rewrite <- Rplus_0_r;
    apply Rplus_le_compat_l.
  apply Rplus_le_le_0_compat.
  repeat apply Rmult_le_pos.
  left; prove_sup0.
  left; prove_sup0.
  replace 0 with (INR 0); [ apply le_INR; apply le_O_n | reflexivity ].
  replace 0 with (INR 0); [ apply le_INR; apply le_O_n | reflexivity ].
  apply Rmult_le_pos.
  left; prove_sup0.
  replace 0 with (INR 0); [ apply le_INR; apply le_O_n | reflexivity ].
  apply INR_fact_neq_0.
  apply INR_fact_neq_0.
  simpl in |- *; ring.
  ring.
  assert (H4 := cv_speed_pow_fact a0); unfold Un in |- *; unfold Un_cv in H4;
    unfold R_dist in H4; unfold Un_cv in |- *; unfold R_dist in |- *;
      intros; elim (H4 eps H5); intros N H6; exists N; intros.
  apply H6; unfold ge in |- *; apply le_trans with (2 * S N)%nat.
  apply le_trans with (2 * N)%nat.
  apply le_n_2n.
  apply (fun m n p:nat => mult_le_compat_l p n m); apply le_n_Sn.
  apply (fun m n p:nat => mult_le_compat_l p n m); apply le_n_S; assumption.
  assert (X := exist_cos (Rsqr a0)); elim X; intros.
  cut (x = cos a0).
  intro; rewrite H4 in p; unfold cos_in in p; unfold infinite_sum in p;
    unfold R_dist in p; unfold Un_cv in |- *; unfold R_dist in |- *;
      intros.
  elim (p _ H5); intros N H6.
  exists N; intros.
  replace (sum_f_R0 (tg_alt Un) n1) with
  (1 - sum_f_R0 (fun i:nat => cos_n i * Rsqr a0 ^ i) (S n1)).
  unfold Rminus in |- *; rewrite Ropp_plus_distr; rewrite Ropp_involutive;
    repeat rewrite Rplus_assoc; rewrite (Rplus_comm 1);
      rewrite (Rplus_comm (-1)); repeat rewrite Rplus_assoc;
        rewrite Rplus_opp_l; rewrite Rplus_0_r; rewrite <- Rabs_Ropp;
          rewrite Ropp_plus_distr; rewrite Ropp_involutive;
            unfold Rminus in H6; apply H6.
  unfold ge in |- *; apply le_trans with n1.
  exact H7.
  apply le_n_Sn.
  rewrite (decomp_sum (fun i:nat => cos_n i * Rsqr a0 ^ i) (S n1)).
  replace (cos_n 0) with 1.
  simpl in |- *; rewrite Rmult_1_r; unfold Rminus in |- *;
    rewrite Ropp_plus_distr; rewrite <- Rplus_assoc; rewrite Rplus_opp_r;
      rewrite Rplus_0_l;
        replace (- sum_f_R0 (fun i:nat => cos_n (S i) * (Rsqr a0 * Rsqr a0 ^ i)) n1)
    with
      (-1 * sum_f_R0 (fun i:nat => cos_n (S i) * (Rsqr a0 * Rsqr a0 ^ i)) n1);
      [ idtac | ring ]; rewrite scal_sum; apply sum_eq;
        intros; unfold cos_n, Un, tg_alt in |- *.
  replace ((-1) ^ S i) with (- (-1) ^ i).
  replace (a0 ^ (2 * S i)) with (Rsqr a0 * Rsqr a0 ^ i).
  unfold Rdiv in |- *; ring.
  rewrite pow_Rsqr; reflexivity.
  simpl in |- *; ring.
  unfold cos_n in |- *; unfold Rdiv in |- *; simpl in |- *; rewrite Rinv_1;
    rewrite Rmult_1_r; reflexivity.
  apply lt_O_Sn.
  unfold cos in |- *; case (exist_cos (Rsqr a0)); intros; unfold cos_in in p;
    unfold cos_in in c; eapply uniqueness_sum.
  apply p.
  apply c.
  intros; elim H3; intros; replace (cos a0 - 1) with (- (1 - cos a0));
    [ idtac | ring ].
  split; apply Ropp_le_contravar; assumption.
  replace (- sum_f_R0 (tg_alt Un) (S (2 * n0))) with
  (-1 * sum_f_R0 (tg_alt Un) (S (2 * n0))); [ rewrite scal_sum | ring ].
  apply sum_eq; intros; unfold cos_term, Un, tg_alt in |- *;
    replace ((-1) ^ S i) with (-1 * (-1) ^ i).
  unfold Rdiv in |- *; ring.
  reflexivity.
  replace (- sum_f_R0 (tg_alt Un) (2 * n0)) with
  (-1 * sum_f_R0 (tg_alt Un) (2 * n0)); [ rewrite scal_sum | ring ];
  apply sum_eq; intros; unfold cos_term, Un, tg_alt in |- *;
    replace ((-1) ^ S i) with (-1 * (-1) ^ i).
  unfold Rdiv in |- *; ring.
  reflexivity.
  replace (2 * (n0 + 1))%nat with (S (S (2 * n0))).
  reflexivity.
  ring.
  replace (2 * n0 + 1)%nat with (S (2 * n0)).
  reflexivity.
  ring.
  intro; elim H2; intros; split.
  apply Rplus_le_reg_l with (-1).
  rewrite <- Rplus_assoc; rewrite Rplus_opp_l; rewrite Rplus_0_l;
    rewrite (Rplus_comm (-1)); apply H3.
  apply Rplus_le_reg_l with (-1).
  rewrite <- Rplus_assoc; rewrite Rplus_opp_l; rewrite Rplus_0_l;
    rewrite (Rplus_comm (-1)); apply H4.
  unfold cos_term in |- *; simpl in |- *; unfold Rdiv in |- *; rewrite Rinv_1;
    ring.
  replace (2 * (n0 + 1))%nat with (S (S (2 * n0))).
  apply lt_O_Sn.
  ring.
  replace (2 * n0 + 1)%nat with (S (2 * n0)).
  apply lt_O_Sn.
  ring.
  intros; case (total_order_T 0 a); intro.
  elim s; intro.
  apply H; [ left; assumption | assumption ].
  apply H; [ right; assumption | assumption ].
  cut (0 < - a).
  intro; cut (forall (x:R) (n:nat), cos_approx x n = cos_approx (- x) n).
  intro; rewrite H3; rewrite (H3 a (2 * (n + 1))%nat); rewrite cos_sym; apply H.
  left; assumption.
  rewrite <- (Ropp_involutive (PI / 2)); apply Ropp_le_contravar;
    unfold Rdiv in |- *; unfold Rdiv in H0; rewrite <- Ropp_mult_distr_l_reverse;
      exact H0.
  intros; unfold cos_approx in |- *; apply sum_eq; intros;
    unfold cos_term in |- *; do 2 rewrite pow_Rsqr; rewrite Rsqr_neg;
      unfold Rdiv in |- *; reflexivity.
  apply Ropp_0_gt_lt_contravar; assumption.
Qed.
