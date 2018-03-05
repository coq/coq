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
Require Import Ranalysis1.
Require Import Ranalysis2.
Local Open Scope R_scope.

(** Division *)
Theorem derivable_pt_lim_div :
  forall (f1 f2:R -> R) (x l1 l2:R),
    derivable_pt_lim f1 x l1 ->
    derivable_pt_lim f2 x l2 ->
    f2 x <> 0 ->
    derivable_pt_lim (f1 / f2) x ((l1 * f2 x - l2 * f1 x) / Rsqr (f2 x)).
Proof.
  intros f1 f2 x l1 l2 H H0 H1.
  cut (derivable_pt f2 x);
    [ intro X | unfold derivable_pt; exists l2; exact H0 ].
  assert (H2 := continuous_neq_0 _ _ (derivable_continuous_pt _ _ X) H1).
  elim H2; clear H2; intros eps_f2 H2.
  unfold div_fct.
  assert (H3 := derivable_continuous_pt _ _ X).
  unfold continuity_pt in H3; unfold continue_in in H3; unfold limit1_in in H3;
    unfold limit_in in H3; unfold dist in H3.
  simpl in H3; unfold R_dist in H3.
  elim (H3 (Rabs (f2 x) / 2));
    [ idtac
      | unfold Rdiv; change (0 < Rabs (f2 x) * / 2);
        apply Rmult_lt_0_compat;
          [ apply Rabs_pos_lt; assumption | apply Rinv_0_lt_compat; prove_sup0 ] ].
  clear H3; intros alp_f2 H3.
  cut
    (forall x0:R,
      Rabs (x0 - x) < alp_f2 -> Rabs (f2 x0 - f2 x) < Rabs (f2 x) / 2).
  intro H4.
  cut (forall a:R, Rabs (a - x) < alp_f2 -> Rabs (f2 x) / 2 < Rabs (f2 a)).
  intro H5.
  cut
    (forall a:R,
      Rabs a < Rmin eps_f2 alp_f2 -> / Rabs (f2 (x + a)) < 2 / Rabs (f2 x)).
  intro Maj.
  unfold derivable_pt_lim; intros.
  elim (H (Rabs (eps * f2 x / 8)));
    [ idtac
      | unfold Rdiv; change (0 < Rabs (eps * f2 x * / 8));
        apply Rabs_pos_lt; repeat apply prod_neq_R0;
          [ red; intro H7; rewrite H7 in H6; elim (Rlt_irrefl _ H6)
            | assumption
            | apply Rinv_neq_0_compat; discrR ] ].
  intros alp_f1d H7.
  case (Req_dec (f1 x) 0); intro.
  case (Req_dec l1 0); intro.
(***********************************)
(*              First case         *)
(*           (f1 x)=0  l1 =0       *)
(***********************************)
  cut (0 < Rmin eps_f2 (Rmin alp_f2 alp_f1d));
    [ intro
      | repeat apply Rmin_pos;
        [ apply (cond_pos eps_f2)
          | elim H3; intros; assumption
          | apply (cond_pos alp_f1d) ] ].
  exists (mkposreal (Rmin eps_f2 (Rmin alp_f2 alp_f1d)) H10).
  simpl; intros.
  assert (H13 := Rlt_le_trans _ _ _ H12 (Rmin_r _ _)).
  assert (H14 := Rlt_le_trans _ _ _ H12 (Rmin_l _ _)).
  assert (H15 := Rlt_le_trans _ _ _ H13 (Rmin_r _ _)).
  assert (H16 := Rlt_le_trans _ _ _ H13 (Rmin_l _ _)).
  assert (H17 := H7 _ H11 H15).
  rewrite formule; [ idtac | assumption | assumption | apply H2; apply H14 ].
  apply Rle_lt_trans with
    (Rabs (/ f2 (x + h) * ((f1 (x + h) - f1 x) / h - l1)) +
      Rabs (l1 / (f2 x * f2 (x + h)) * (f2 x - f2 (x + h))) +
      Rabs (f1 x / (f2 x * f2 (x + h)) * ((f2 (x + h) - f2 x) / h - l2)) +
      Rabs (l2 * f1 x / (Rsqr (f2 x) * f2 (x + h)) * (f2 (x + h) - f2 x))).
  unfold Rminus.
  rewrite <-
    (Rabs_Ropp (f1 x / (f2 x * f2 (x + h)) * ((f2 (x + h) + - f2 x) / h + - l2)))
    .
  apply Rabs_4.
  repeat rewrite Rabs_mult.
  apply Rlt_le_trans with (eps / 4 + eps / 4 + eps / 4 + eps / 4).
  cut (Rabs (/ f2 (x + h)) * Rabs ((f1 (x + h) - f1 x) / h - l1) < eps / 4).
  cut (Rabs (l1 / (f2 x * f2 (x + h))) * Rabs (f2 x - f2 (x + h)) < eps / 4).
  cut
    (Rabs (f1 x / (f2 x * f2 (x + h))) * Rabs ((f2 (x + h) - f2 x) / h - l2) <
      eps / 4).
  cut
    (Rabs (l2 * f1 x / (Rsqr (f2 x) * f2 (x + h))) * Rabs (f2 (x + h) - f2 x) <
      eps / 4).
  intros.
  apply Rlt_4; assumption.
  rewrite H8.
  unfold Rdiv; repeat rewrite Rmult_0_r || rewrite Rmult_0_l.
  rewrite Rabs_R0; rewrite Rmult_0_l.
  apply Rmult_lt_0_compat; [ assumption | apply Rinv_0_lt_compat; prove_sup ].
  rewrite H8.
  unfold Rdiv; repeat rewrite Rmult_0_r || rewrite Rmult_0_l.
  rewrite Rabs_R0; rewrite Rmult_0_l.
  apply Rmult_lt_0_compat; [ assumption | apply Rinv_0_lt_compat; prove_sup ].
  rewrite H9.
  unfold Rdiv; repeat rewrite Rmult_0_r || rewrite Rmult_0_l.
  rewrite Rabs_R0; rewrite Rmult_0_l.
  apply Rmult_lt_0_compat; [ assumption | apply Rinv_0_lt_compat; prove_sup ].
  rewrite <- Rabs_mult.
  apply (maj_term1 x h eps l1 alp_f2 eps_f2 alp_f1d f1 f2);
    try assumption || apply H2.
  apply H14.
  apply Rmin_2; assumption.
  right; symmetry ; apply quadruple_var.
(***********************************)
(*           Second case           *)
(*           (f1 x)=0  l1<>0       *)
(***********************************)
  assert (H10 := derivable_continuous_pt _ _ X).
  unfold continuity_pt in H10.
  unfold continue_in in H10.
  unfold limit1_in in H10.
  unfold limit_in in H10.
  unfold dist in H10.
  simpl in H10.
  unfold R_dist in H10.
  elim (H10 (Rabs (eps * Rsqr (f2 x) / (8 * l1)))).
  clear H10; intros alp_f2t2 H10.
  cut
    (forall a:R,
      Rabs a < alp_f2t2 ->
      Rabs (f2 (x + a) - f2 x) < Rabs (eps * Rsqr (f2 x) / (8 * l1))).
  intro H11.
  cut (0 < Rmin (Rmin eps_f2 alp_f1d) (Rmin alp_f2 alp_f2t2)).
  intro.
  exists (mkposreal (Rmin (Rmin eps_f2 alp_f1d) (Rmin alp_f2 alp_f2t2)) H12).
  simpl.
  intros.
  assert (H15 := Rlt_le_trans _ _ _ H14 (Rmin_r _ _)).
  assert (H16 := Rlt_le_trans _ _ _ H14 (Rmin_l _ _)).
  assert (H17 := Rlt_le_trans _ _ _ H15 (Rmin_l _ _)).
  assert (H18 := Rlt_le_trans _ _ _ H15 (Rmin_r _ _)).
  assert (H19 := Rlt_le_trans _ _ _ H16 (Rmin_l _ _)).
  assert (H20 := Rlt_le_trans _ _ _ H16 (Rmin_r _ _)).
  clear H14 H15 H16.
  rewrite formule; try assumption.
  apply Rle_lt_trans with
    (Rabs (/ f2 (x + h) * ((f1 (x + h) - f1 x) / h - l1)) +
      Rabs (l1 / (f2 x * f2 (x + h)) * (f2 x - f2 (x + h))) +
      Rabs (f1 x / (f2 x * f2 (x + h)) * ((f2 (x + h) - f2 x) / h - l2)) +
      Rabs (l2 * f1 x / (Rsqr (f2 x) * f2 (x + h)) * (f2 (x + h) - f2 x))).
  unfold Rminus.
  rewrite <-
    (Rabs_Ropp (f1 x / (f2 x * f2 (x + h)) * ((f2 (x + h) + - f2 x) / h + - l2)))
    .
  apply Rabs_4.
  repeat rewrite Rabs_mult.
  apply Rlt_le_trans with (eps / 4 + eps / 4 + eps / 4 + eps / 4).
  cut (Rabs (/ f2 (x + h)) * Rabs ((f1 (x + h) - f1 x) / h - l1) < eps / 4).
  cut (Rabs (l1 / (f2 x * f2 (x + h))) * Rabs (f2 x - f2 (x + h)) < eps / 4).
  cut
    (Rabs (f1 x / (f2 x * f2 (x + h))) * Rabs ((f2 (x + h) - f2 x) / h - l2) <
      eps / 4).
  cut
    (Rabs (l2 * f1 x / (Rsqr (f2 x) * f2 (x + h))) * Rabs (f2 (x + h) - f2 x) <
      eps / 4).
  intros.
  apply Rlt_4; assumption.
  rewrite H8.
  unfold Rdiv; repeat rewrite Rmult_0_r || rewrite Rmult_0_l.
  rewrite Rabs_R0; rewrite Rmult_0_l.
  apply Rmult_lt_0_compat; [ assumption | apply Rinv_0_lt_compat; prove_sup ].
  rewrite H8.
  unfold Rdiv; repeat rewrite Rmult_0_r || rewrite Rmult_0_l.
  rewrite Rabs_R0; rewrite Rmult_0_l.
  apply Rmult_lt_0_compat; [ assumption | apply Rinv_0_lt_compat; prove_sup ].
  rewrite <- Rabs_mult.
  apply (maj_term2 x h eps l1 alp_f2 alp_f2t2 eps_f2 f2); try assumption.
  apply H2; assumption.
  apply Rmin_2; assumption.
  rewrite <- Rabs_mult.
  apply (maj_term1 x h eps l1 alp_f2 eps_f2 alp_f1d f1 f2); try assumption.
  apply H2; assumption.
  apply Rmin_2; assumption.
  right; symmetry ; apply quadruple_var.
  apply H2; assumption.
  repeat apply Rmin_pos.
  apply (cond_pos eps_f2).
  apply (cond_pos alp_f1d).
  elim H3; intros; assumption.
  elim H10; intros; assumption.
  intros.
  elim H10; intros.
  case (Req_dec a 0); intro.
  rewrite H14; rewrite Rplus_0_r.
  unfold Rminus; rewrite Rplus_opp_r.
  rewrite Rabs_R0.
  apply Rabs_pos_lt.
  unfold Rdiv, Rsqr; repeat rewrite Rmult_assoc.
  repeat apply prod_neq_R0; try assumption.
  now apply Rgt_not_eq.
  apply Rinv_neq_0_compat; apply prod_neq_R0; [discrR | assumption].
  apply H13.
  split.
  apply D_x_no_cond; assumption.
  replace (x + a - x) with a; [ assumption | ring ].
  change (0 < Rabs (eps * Rsqr (f2 x) / (8 * l1))).
  apply Rabs_pos_lt; unfold Rdiv, Rsqr; repeat rewrite Rmult_assoc;
    repeat apply prod_neq_R0.
  red; intro; rewrite H11 in H6; elim (Rlt_irrefl _ H6).
  assumption.
  assumption.
  apply Rinv_neq_0_compat; apply prod_neq_R0; [discrR | assumption].
(***********************************)
(*        Third case               *)
(*     (f1 x)<>0  l1=0  l2=0       *)
(***********************************)
  case (Req_dec l1 0); intro.
  case (Req_dec l2 0); intro.
  elim (H0 (Rabs (Rsqr (f2 x) * eps / (8 * f1 x))));
    [ idtac
      | apply Rabs_pos_lt; unfold Rdiv, Rsqr; repeat rewrite Rmult_assoc;
        repeat apply prod_neq_R0 ;
          [ assumption
            | assumption
            | now apply Rgt_not_eq
            | apply Rinv_neq_0_compat; apply prod_neq_R0; discrR || assumption ] ].
  intros alp_f2d H12.
  cut (0 < Rmin (Rmin eps_f2 alp_f2) (Rmin alp_f1d alp_f2d)).
  intro.
  exists (mkposreal (Rmin (Rmin eps_f2 alp_f2) (Rmin alp_f1d alp_f2d)) H11).
  simpl.
  intros.
  assert (H15 := Rlt_le_trans _ _ _ H14 (Rmin_l _ _)).
  assert (H16 := Rlt_le_trans _ _ _ H14 (Rmin_r _ _)).
  assert (H17 := Rlt_le_trans _ _ _ H15 (Rmin_l _ _)).
  assert (H18 := Rlt_le_trans _ _ _ H15 (Rmin_r _ _)).
  assert (H19 := Rlt_le_trans _ _ _ H16 (Rmin_l _ _)).
  assert (H20 := Rlt_le_trans _ _ _ H16 (Rmin_r _ _)).
  clear H15 H16.
  rewrite formule; try assumption.
  apply Rle_lt_trans with
    (Rabs (/ f2 (x + h) * ((f1 (x + h) - f1 x) / h - l1)) +
      Rabs (l1 / (f2 x * f2 (x + h)) * (f2 x - f2 (x + h))) +
      Rabs (f1 x / (f2 x * f2 (x + h)) * ((f2 (x + h) - f2 x) / h - l2)) +
      Rabs (l2 * f1 x / (Rsqr (f2 x) * f2 (x + h)) * (f2 (x + h) - f2 x))).
  unfold Rminus.
  rewrite <-
    (Rabs_Ropp (f1 x / (f2 x * f2 (x + h)) * ((f2 (x + h) + - f2 x) / h + - l2)))
    .
  apply Rabs_4.
  repeat rewrite Rabs_mult.
  apply Rlt_le_trans with (eps / 4 + eps / 4 + eps / 4 + eps / 4).
  cut (Rabs (/ f2 (x + h)) * Rabs ((f1 (x + h) - f1 x) / h - l1) < eps / 4).
  cut (Rabs (l1 / (f2 x * f2 (x + h))) * Rabs (f2 x - f2 (x + h)) < eps / 4).
  cut
    (Rabs (f1 x / (f2 x * f2 (x + h))) * Rabs ((f2 (x + h) - f2 x) / h - l2) <
      eps / 4).
  cut
    (Rabs (l2 * f1 x / (Rsqr (f2 x) * f2 (x + h))) * Rabs (f2 (x + h) - f2 x) <
      eps / 4).
  intros.
  apply Rlt_4; assumption.
  rewrite H10.
  unfold Rdiv; repeat rewrite Rmult_0_r || rewrite Rmult_0_l.
  rewrite Rabs_R0; rewrite Rmult_0_l.
  apply Rmult_lt_0_compat; [ assumption | apply Rinv_0_lt_compat; prove_sup ].
  rewrite <- Rabs_mult.
  apply (maj_term3 x h eps l2 alp_f2 eps_f2 alp_f2d f1 f2); try assumption.
  apply H2; assumption.
  apply Rmin_2; assumption.
  rewrite H9.
  unfold Rdiv; repeat rewrite Rmult_0_r || rewrite Rmult_0_l.
  rewrite Rabs_R0; rewrite Rmult_0_l.
  apply Rmult_lt_0_compat; [ assumption | apply Rinv_0_lt_compat; prove_sup ].
  rewrite <- Rabs_mult.
  apply (maj_term1 x h eps l1 alp_f2 eps_f2 alp_f1d f1 f2); assumption || idtac.
  apply H2; assumption.
  apply Rmin_2; assumption.
  right; symmetry ; apply quadruple_var.
  apply H2; assumption.
  repeat apply Rmin_pos.
  apply (cond_pos eps_f2).
  elim H3; intros; assumption.
  apply (cond_pos alp_f1d).
  apply (cond_pos alp_f2d).
(***********************************)
(*      Fourth case                *)
(*    (f1 x)<>0  l1=0  l2<>0       *)
(***********************************)
  elim (H0 (Rabs (Rsqr (f2 x) * eps / (8 * f1 x))));
    [ idtac
      | apply Rabs_pos_lt; unfold Rsqr, Rdiv;
        repeat apply prod_neq_R0 ;
          [ assumption..
            | now apply Rgt_not_eq
            | apply Rinv_neq_0_compat; apply prod_neq_R0; discrR || assumption ] ].
  intros alp_f2d H11.
  assert (H12 := derivable_continuous_pt _ _ X).
  unfold continuity_pt in H12.
  unfold continue_in in H12.
  unfold limit1_in in H12.
  unfold limit_in in H12.
  unfold dist in H12.
  simpl in H12.
  unfold R_dist in H12.
  elim (H12 (Rabs (Rsqr (f2 x) * f2 x * eps / (8 * f1 x * l2)))).
  intros alp_f2c H13.
  cut (0 < Rmin (Rmin eps_f2 alp_f2) (Rmin alp_f1d (Rmin alp_f2d alp_f2c))).
  intro.
  exists
    (mkposreal (Rmin (Rmin eps_f2 alp_f2) (Rmin alp_f1d (Rmin alp_f2d alp_f2c)))
      H14).
  simpl; intros.
  assert (H17 := Rlt_le_trans _ _ _ H16 (Rmin_l _ _)).
  assert (H18 := Rlt_le_trans _ _ _ H16 (Rmin_r _ _)).
  assert (H19 := Rlt_le_trans _ _ _ H18 (Rmin_r _ _)).
  assert (H20 := Rlt_le_trans _ _ _ H19 (Rmin_l _ _)).
  assert (H21 := Rlt_le_trans _ _ _ H19 (Rmin_r _ _)).
  assert (H22 := Rlt_le_trans _ _ _ H18 (Rmin_l _ _)).
  assert (H23 := Rlt_le_trans _ _ _ H17 (Rmin_l _ _)).
  assert (H24 := Rlt_le_trans _ _ _ H17 (Rmin_r _ _)).
  clear H16 H17 H18 H19.
  cut
    (forall a:R,
      Rabs a < alp_f2c ->
      Rabs (f2 (x + a) - f2 x) <
      Rabs (Rsqr (f2 x) * f2 x * eps / (8 * f1 x * l2))).
  intro.
  rewrite formule; try assumption.
  apply Rle_lt_trans with
    (Rabs (/ f2 (x + h) * ((f1 (x + h) - f1 x) / h - l1)) +
      Rabs (l1 / (f2 x * f2 (x + h)) * (f2 x - f2 (x + h))) +
      Rabs (f1 x / (f2 x * f2 (x + h)) * ((f2 (x + h) - f2 x) / h - l2)) +
      Rabs (l2 * f1 x / (Rsqr (f2 x) * f2 (x + h)) * (f2 (x + h) - f2 x))).
  unfold Rminus.
  rewrite <-
    (Rabs_Ropp (f1 x / (f2 x * f2 (x + h)) * ((f2 (x + h) + - f2 x) / h + - l2)))
    .
  apply Rabs_4.
  repeat rewrite Rabs_mult.
  apply Rlt_le_trans with (eps / 4 + eps / 4 + eps / 4 + eps / 4).
  cut (Rabs (/ f2 (x + h)) * Rabs ((f1 (x + h) - f1 x) / h - l1) < eps / 4).
  cut (Rabs (l1 / (f2 x * f2 (x + h))) * Rabs (f2 x - f2 (x + h)) < eps / 4).
  cut
    (Rabs (f1 x / (f2 x * f2 (x + h))) * Rabs ((f2 (x + h) - f2 x) / h - l2) <
      eps / 4).
  cut
    (Rabs (l2 * f1 x / (Rsqr (f2 x) * f2 (x + h))) * Rabs (f2 (x + h) - f2 x) <
      eps / 4).
  intros.
  apply Rlt_4; assumption.
  rewrite <- Rabs_mult.
  apply (maj_term4 x h eps l2 alp_f2 alp_f2c eps_f2 f1 f2); try assumption.
  apply H2; assumption.
  apply Rmin_2; assumption.
  rewrite <- Rabs_mult.
  apply (maj_term3 x h eps l2 alp_f2 eps_f2 alp_f2d f1 f2); try assumption.
  apply H2; assumption.
  apply Rmin_2; assumption.
  rewrite H9.
  unfold Rdiv; repeat rewrite Rmult_0_r || rewrite Rmult_0_l.
  rewrite Rabs_R0; rewrite Rmult_0_l.
  apply Rmult_lt_0_compat; [ assumption | apply Rinv_0_lt_compat; prove_sup ].
  rewrite <- Rabs_mult.
  apply (maj_term1 x h eps l1 alp_f2 eps_f2 alp_f1d f1 f2); try assumption.
  apply H2; assumption.
  apply Rmin_2; assumption.
  right; symmetry ; apply quadruple_var.
  apply H2; assumption.
  intros.
  case (Req_dec a 0); intro.
  rewrite H17; rewrite Rplus_0_r.
  unfold Rminus; rewrite Rplus_opp_r; rewrite Rabs_R0.
  apply Rabs_pos_lt.
  unfold Rdiv, Rsqr.
  repeat rewrite Rinv_mult_distr; try assumption.
  repeat apply prod_neq_R0; try assumption.
  red; intro H18; rewrite H18 in H6; elim (Rlt_irrefl _ H6).
  apply Rinv_neq_0_compat; discrR.
  apply Rinv_neq_0_compat; assumption.
  apply Rinv_neq_0_compat; assumption.
  discrR.
  apply prod_neq_R0; [ discrR | assumption ].
  elim H13; intros.
  apply H19.
  split.
  apply D_x_no_cond; assumption.
  replace (x + a - x) with a; [ assumption | ring ].
  repeat apply Rmin_pos.
  apply (cond_pos eps_f2).
  elim H3; intros; assumption.
  apply (cond_pos alp_f1d).
  apply (cond_pos alp_f2d).
  elim H13; intros; assumption.
  change (0 < Rabs (Rsqr (f2 x) * f2 x * eps / (8 * f1 x * l2))).
  apply Rabs_pos_lt.
  unfold Rsqr, Rdiv.
  repeat rewrite Rinv_mult_distr; try assumption || discrR.
  repeat apply prod_neq_R0; try assumption.
  red; intro H13; rewrite H13 in H6; elim (Rlt_irrefl _ H6).
  apply Rinv_neq_0_compat; discrR.
  apply Rinv_neq_0_compat; assumption.
  apply Rinv_neq_0_compat; assumption.
  apply prod_neq_R0; [ discrR | assumption ].
(***********************************)
(*         Fifth case              *)
(*    (f1 x)<>0  l1<>0  l2=0       *)
(***********************************)
  case (Req_dec l2 0); intro.
  assert (H11 := derivable_continuous_pt _ _ X).
  unfold continuity_pt in H11.
  unfold continue_in in H11.
  unfold limit1_in in H11.
  unfold limit_in in H11.
  unfold dist in H11.
  simpl in H11.
  unfold R_dist in H11.
  elim (H11 (Rabs (eps * Rsqr (f2 x) / (8 * l1)))).
  clear H11; intros alp_f2t2 H11.
  elim (H0 (Rabs (Rsqr (f2 x) * eps / (8 * f1 x)))).
  intros alp_f2d H12.
  cut (0 < Rmin (Rmin eps_f2 alp_f2) (Rmin alp_f1d (Rmin alp_f2d alp_f2t2))).
  intro.
  exists
    (mkposreal
      (Rmin (Rmin eps_f2 alp_f2) (Rmin alp_f1d (Rmin alp_f2d alp_f2t2))) H13).
  simpl.
  intros.
  cut
    (forall a:R,
      Rabs a < alp_f2t2 ->
      Rabs (f2 (x + a) - f2 x) < Rabs (eps * Rsqr (f2 x) / (8 * l1))).
  intro.
  assert (H17 := Rlt_le_trans _ _ _ H15 (Rmin_l _ _)).
  assert (H18 := Rlt_le_trans _ _ _ H15 (Rmin_r _ _)).
  assert (H19 := Rlt_le_trans _ _ _ H17 (Rmin_r _ _)).
  assert (H20 := Rlt_le_trans _ _ _ H17 (Rmin_l _ _)).
  assert (H21 := Rlt_le_trans _ _ _ H18 (Rmin_r _ _)).
  assert (H22 := Rlt_le_trans _ _ _ H18 (Rmin_l _ _)).
  assert (H23 := Rlt_le_trans _ _ _ H21 (Rmin_l _ _)).
  assert (H24 := Rlt_le_trans _ _ _ H21 (Rmin_r _ _)).
  clear H15 H17 H18 H21.
  rewrite formule; try assumption.
  apply Rle_lt_trans with
    (Rabs (/ f2 (x + h) * ((f1 (x + h) - f1 x) / h - l1)) +
      Rabs (l1 / (f2 x * f2 (x + h)) * (f2 x - f2 (x + h))) +
      Rabs (f1 x / (f2 x * f2 (x + h)) * ((f2 (x + h) - f2 x) / h - l2)) +
      Rabs (l2 * f1 x / (Rsqr (f2 x) * f2 (x + h)) * (f2 (x + h) - f2 x))).
  unfold Rminus.
  rewrite <-
    (Rabs_Ropp (f1 x / (f2 x * f2 (x + h)) * ((f2 (x + h) + - f2 x) / h + - l2)))
    .
  apply Rabs_4.
  repeat rewrite Rabs_mult.
  apply Rlt_le_trans with (eps / 4 + eps / 4 + eps / 4 + eps / 4).
  cut (Rabs (/ f2 (x + h)) * Rabs ((f1 (x + h) - f1 x) / h - l1) < eps / 4).
  cut (Rabs (l1 / (f2 x * f2 (x + h))) * Rabs (f2 x - f2 (x + h)) < eps / 4).
  cut
    (Rabs (f1 x / (f2 x * f2 (x + h))) * Rabs ((f2 (x + h) - f2 x) / h - l2) <
      eps / 4).
  cut
    (Rabs (l2 * f1 x / (Rsqr (f2 x) * f2 (x + h))) * Rabs (f2 (x + h) - f2 x) <
      eps / 4).
  intros.
  apply Rlt_4; assumption.
  rewrite H10.
  unfold Rdiv; repeat rewrite Rmult_0_r || rewrite Rmult_0_l.
  rewrite Rabs_R0; rewrite Rmult_0_l.
  apply Rmult_lt_0_compat; [ assumption | apply Rinv_0_lt_compat; prove_sup ].
  rewrite <- Rabs_mult.
  apply (maj_term3 x h eps l2 alp_f2 eps_f2 alp_f2d f1 f2); try assumption.
  apply H2; assumption.
  apply Rmin_2; assumption.
  rewrite <- Rabs_mult.
  apply (maj_term2 x h eps l1 alp_f2 alp_f2t2 eps_f2 f2); try assumption.
  apply H2; assumption.
  apply Rmin_2; assumption.
  rewrite <- Rabs_mult.
  apply (maj_term1 x h eps l1 alp_f2 eps_f2 alp_f1d f1 f2); try assumption.
  apply H2; assumption.
  apply Rmin_2; assumption.
  right; symmetry ; apply quadruple_var.
  apply H2; assumption.
  intros.
  case (Req_dec a 0); intro.
  rewrite H17; rewrite Rplus_0_r; unfold Rminus; rewrite Rplus_opp_r;
    rewrite Rabs_R0.
  apply Rabs_pos_lt.
  unfold Rdiv; rewrite Rinv_mult_distr; try discrR || assumption.
  unfold Rsqr.
  repeat apply prod_neq_R0;
    assumption ||
      (apply Rinv_neq_0_compat; assumption) ||
        (apply Rinv_neq_0_compat; discrR) ||
          (red; intro H18; rewrite H18 in H6; elim (Rlt_irrefl _ H6)).
  elim H11; intros.
  apply H19.
  split.
  apply D_x_no_cond; assumption.
  replace (x + a - x) with a; [ assumption | ring ].
  repeat apply Rmin_pos.
  apply (cond_pos eps_f2).
  elim H3; intros; assumption.
  apply (cond_pos alp_f1d).
  apply (cond_pos alp_f2d).
  elim H11; intros; assumption.
  apply Rabs_pos_lt.
  unfold Rdiv, Rsqr; rewrite Rinv_mult_distr; try discrR || assumption.
  repeat apply prod_neq_R0;
    assumption ||
      (apply Rinv_neq_0_compat; assumption) ||
        (apply Rinv_neq_0_compat; discrR) ||
          (red; intro H12; rewrite H12 in H6; elim (Rlt_irrefl _ H6)).
  change (0 < Rabs (eps * Rsqr (f2 x) / (8 * l1))).
  apply Rabs_pos_lt.
  unfold Rdiv, Rsqr; rewrite Rinv_mult_distr; try discrR || assumption.
  repeat apply prod_neq_R0;
    assumption ||
      (apply Rinv_neq_0_compat; assumption) ||
        (apply Rinv_neq_0_compat; discrR) ||
          (red; intro H12; rewrite H12 in H6; elim (Rlt_irrefl _ H6)).
(***********************************)
(*       Sixth case                *)
(*    (f1 x)<>0  l1<>0  l2<>0      *)
(***********************************)
  elim (H0 (Rabs (Rsqr (f2 x) * eps / (8 * f1 x)))).
  intros alp_f2d H11.
  assert (H12 := derivable_continuous_pt _ _ X).
  unfold continuity_pt in H12.
  unfold continue_in in H12.
  unfold limit1_in in H12.
  unfold limit_in in H12.
  unfold dist in H12.
  simpl in H12.
  unfold R_dist in H12.
  elim (H12 (Rabs (Rsqr (f2 x) * f2 x * eps / (8 * f1 x * l2)))).
  intros alp_f2c H13.
  elim (H12 (Rabs (eps * Rsqr (f2 x) / (8 * l1)))).
  intros alp_f2t2 H14.
  cut
    (0 <
      Rmin (Rmin (Rmin eps_f2 alp_f2) (Rmin alp_f1d alp_f2d))
      (Rmin alp_f2c alp_f2t2)).
  intro.
  exists
    (mkposreal
      (Rmin (Rmin (Rmin eps_f2 alp_f2) (Rmin alp_f1d alp_f2d))
        (Rmin alp_f2c alp_f2t2)) H15).
  simpl.
  intros.
  assert (H18 := Rlt_le_trans _ _ _ H17 (Rmin_l _ _)).
  assert (H19 := Rlt_le_trans _ _ _ H17 (Rmin_r _ _)).
  assert (H20 := Rlt_le_trans _ _ _ H18 (Rmin_l _ _)).
  assert (H21 := Rlt_le_trans _ _ _ H18 (Rmin_r _ _)).
  assert (H22 := Rlt_le_trans _ _ _ H19 (Rmin_l _ _)).
  assert (H23 := Rlt_le_trans _ _ _ H19 (Rmin_r _ _)).
  assert (H24 := Rlt_le_trans _ _ _ H20 (Rmin_l _ _)).
  assert (H25 := Rlt_le_trans _ _ _ H20 (Rmin_r _ _)).
  assert (H26 := Rlt_le_trans _ _ _ H21 (Rmin_l _ _)).
  assert (H27 := Rlt_le_trans _ _ _ H21 (Rmin_r _ _)).
  clear H17 H18 H19 H20 H21.
  cut
    (forall a:R,
      Rabs a < alp_f2t2 ->
      Rabs (f2 (x + a) - f2 x) < Rabs (eps * Rsqr (f2 x) / (8 * l1))).
  cut
    (forall a:R,
      Rabs a < alp_f2c ->
      Rabs (f2 (x + a) - f2 x) <
      Rabs (Rsqr (f2 x) * f2 x * eps / (8 * f1 x * l2))).
  intros.
  rewrite formule; try assumption.
  apply Rle_lt_trans with
    (Rabs (/ f2 (x + h) * ((f1 (x + h) - f1 x) / h - l1)) +
      Rabs (l1 / (f2 x * f2 (x + h)) * (f2 x - f2 (x + h))) +
      Rabs (f1 x / (f2 x * f2 (x + h)) * ((f2 (x + h) - f2 x) / h - l2)) +
      Rabs (l2 * f1 x / (Rsqr (f2 x) * f2 (x + h)) * (f2 (x + h) - f2 x))).
  unfold Rminus.
  rewrite <-
    (Rabs_Ropp (f1 x / (f2 x * f2 (x + h)) * ((f2 (x + h) + - f2 x) / h + - l2)))
    .
  apply Rabs_4.
  repeat rewrite Rabs_mult.
  apply Rlt_le_trans with (eps / 4 + eps / 4 + eps / 4 + eps / 4).
  cut (Rabs (/ f2 (x + h)) * Rabs ((f1 (x + h) - f1 x) / h - l1) < eps / 4).
  cut (Rabs (l1 / (f2 x * f2 (x + h))) * Rabs (f2 x - f2 (x + h)) < eps / 4).
  cut
    (Rabs (f1 x / (f2 x * f2 (x + h))) * Rabs ((f2 (x + h) - f2 x) / h - l2) <
      eps / 4).
  cut
    (Rabs (l2 * f1 x / (Rsqr (f2 x) * f2 (x + h))) * Rabs (f2 (x + h) - f2 x) <
      eps / 4).
  intros.
  apply Rlt_4; assumption.
  rewrite <- Rabs_mult.
  apply (maj_term4 x h eps l2 alp_f2 alp_f2c eps_f2 f1 f2); try assumption.
  apply H2; assumption.
  apply Rmin_2; assumption.
  rewrite <- Rabs_mult.
  apply (maj_term3 x h eps l2 alp_f2 eps_f2 alp_f2d f1 f2); try assumption.
  apply H2; assumption.
  apply Rmin_2; assumption.
  rewrite <- Rabs_mult.
  apply (maj_term2 x h eps l1 alp_f2 alp_f2t2 eps_f2 f2); try assumption.
  apply H2; assumption.
  apply Rmin_2; assumption.
  rewrite <- Rabs_mult.
  apply (maj_term1 x h eps l1 alp_f2 eps_f2 alp_f1d f1 f2); try assumption.
  apply H2; assumption.
  apply Rmin_2; assumption.
  right; symmetry ; apply quadruple_var.
  apply H2; assumption.
  intros.
  case (Req_dec a 0); intro.
  rewrite H18; rewrite Rplus_0_r; unfold Rminus; rewrite Rplus_opp_r;
    rewrite Rabs_R0; apply Rabs_pos_lt.
  unfold Rdiv, Rsqr; rewrite Rinv_mult_distr.
  repeat apply prod_neq_R0;
    assumption ||
      (apply Rinv_neq_0_compat; assumption) ||
        (apply Rinv_neq_0_compat; discrR) ||
          (red; intro H28; rewrite H28 in H6; elim (Rlt_irrefl _ H6)).
  apply prod_neq_R0; [ discrR | assumption ].
  apply prod_neq_R0; [ discrR | assumption ].
  assumption.
  elim H13; intros.
  apply H20.
  split.
  apply D_x_no_cond; assumption.
  replace (x + a - x) with a; [ assumption | ring ].
  intros.
  case (Req_dec a 0); intro.
  rewrite H18; rewrite Rplus_0_r; unfold Rminus; rewrite Rplus_opp_r;
    rewrite Rabs_R0; apply Rabs_pos_lt.
  unfold Rdiv, Rsqr; rewrite Rinv_mult_distr.
  repeat apply prod_neq_R0;
    assumption ||
      (apply Rinv_neq_0_compat; assumption) ||
        (apply Rinv_neq_0_compat; discrR) ||
          (red; intro H28; rewrite H28 in H6; elim (Rlt_irrefl _ H6)).
  discrR.
  assumption.
  elim H14; intros.
  apply H20.
  split.
  unfold D_x, no_cond; split.
  trivial.
  apply Rminus_not_eq_right.
  replace (x + a - x) with a; [ assumption | ring ].
  replace (x + a - x) with a; [ assumption | ring ].
  repeat apply Rmin_pos.
  apply (cond_pos eps_f2).
  elim H3; intros; assumption.
  apply (cond_pos alp_f1d).
  apply (cond_pos alp_f2d).
  elim H13; intros; assumption.
  elim H14; intros; assumption.
  change (0 < Rabs (eps * Rsqr (f2 x) / (8 * l1))); apply Rabs_pos_lt.
  unfold Rdiv, Rsqr; rewrite Rinv_mult_distr; try discrR || assumption.
  repeat apply prod_neq_R0;
    assumption ||
      (apply Rinv_neq_0_compat; assumption) ||
        (apply Rinv_neq_0_compat; discrR) ||
          (red; intro H14; rewrite H14 in H6; elim (Rlt_irrefl _ H6)).
  change (0 < Rabs (Rsqr (f2 x) * f2 x * eps / (8 * f1 x * l2)));
    apply Rabs_pos_lt.
  unfold Rdiv, Rsqr; rewrite Rinv_mult_distr.
  repeat apply prod_neq_R0;
    assumption ||
      (apply Rinv_neq_0_compat; assumption) ||
        (apply Rinv_neq_0_compat; discrR) ||
          (red; intro H13; rewrite H13 in H6; elim (Rlt_irrefl _ H6)).
  apply prod_neq_R0; [ discrR | assumption ].
  apply prod_neq_R0; [ discrR | assumption ].
  assumption.
  apply Rabs_pos_lt.
  unfold Rdiv, Rsqr; rewrite Rinv_mult_distr;
    [ idtac | discrR | assumption ].
  repeat apply prod_neq_R0;
    assumption ||
      (apply Rinv_neq_0_compat; assumption) ||
        (apply Rinv_neq_0_compat; discrR) ||
          (red; intro H11; rewrite H11 in H6; elim (Rlt_irrefl _ H6)).
  intros.
  unfold Rdiv.
  apply Rmult_lt_reg_l with (Rabs (f2 (x + a))).
  apply Rabs_pos_lt; apply H2.
  apply Rlt_le_trans with (Rmin eps_f2 alp_f2).
  assumption.
  apply Rmin_l.
  rewrite <- Rinv_r_sym.
  apply Rmult_lt_reg_l with (Rabs (f2 x)).
  apply Rabs_pos_lt; assumption.
  rewrite Rmult_1_r.
  rewrite (Rmult_comm (Rabs (f2 x))).
  repeat rewrite Rmult_assoc.
  rewrite <- Rinv_l_sym.
  rewrite Rmult_1_r.
  apply Rmult_lt_reg_l with (/ 2).
  apply Rinv_0_lt_compat; prove_sup0.
  repeat rewrite (Rmult_comm (/ 2)).
  repeat rewrite Rmult_assoc.
  rewrite <- Rinv_r_sym.
  rewrite Rmult_1_r.
  unfold Rdiv in H5; apply H5.
  replace (x + a - x) with a.
  assert (H7 := Rlt_le_trans _ _ _ H6 (Rmin_r _ _)); assumption.
  ring.
  discrR.
  apply Rabs_no_R0; assumption.
  apply Rabs_no_R0; apply H2.
  assert (H7 := Rlt_le_trans _ _ _ H6 (Rmin_l _ _)); assumption.
  intros.
  assert (H6 := H4 a H5).
  rewrite <- (Rabs_Ropp (f2 a - f2 x)) in H6.
  rewrite Ropp_minus_distr in H6.
  assert (H7 := Rle_lt_trans _ _ _ (Rabs_triang_inv _ _) H6).
  apply Rplus_lt_reg_l with (- Rabs (f2 a) + Rabs (f2 x) / 2).
  rewrite Rplus_assoc.
  rewrite <- double_var.
  do 2 rewrite (Rplus_comm (- Rabs (f2 a))).
  rewrite Rplus_assoc; rewrite Rplus_opp_l; rewrite Rplus_0_r.
  unfold Rminus in H7; assumption.
  intros.
  case (Req_dec x x0); intro.
  rewrite <- H5; unfold Rminus; rewrite Rplus_opp_r; rewrite Rabs_R0;
    unfold Rdiv; apply Rmult_lt_0_compat;
      [ apply Rabs_pos_lt; assumption | apply Rinv_0_lt_compat; prove_sup0 ].
  elim H3; intros.
  apply H7.
  split.
  unfold D_x, no_cond; split.
  trivial.
  assumption.
  assumption.
Qed.

Lemma derivable_pt_div :
  forall (f1 f2:R -> R) (x:R),
    derivable_pt f1 x ->
    derivable_pt f2 x -> f2 x <> 0 -> derivable_pt (f1 / f2) x.
Proof.
  unfold derivable_pt.
  intros f1 f2 x X X0 H.
  elim X; intros.
  elim X0; intros.
  exists ((x0 * f2 x - x1 * f1 x) / Rsqr (f2 x)).
  apply derivable_pt_lim_div; assumption.
Qed.

Lemma derivable_div :
  forall f1 f2:R -> R,
    derivable f1 ->
    derivable f2 -> (forall x:R, f2 x <> 0) -> derivable (f1 / f2).
Proof.
  unfold derivable; intros f1 f2 X X0 H x.
  apply (derivable_pt_div _ _ _ (X x) (X0 x) (H x)).
Qed.

Lemma derive_pt_div :
  forall (f1 f2:R -> R) (x:R) (pr1:derivable_pt f1 x)
    (pr2:derivable_pt f2 x) (na:f2 x <> 0),
    derive_pt (f1 / f2) x (derivable_pt_div _ _ _ pr1 pr2 na) =
    (derive_pt f1 x pr1 * f2 x - derive_pt f2 x pr2 * f1 x) / Rsqr (f2 x).
Proof.
  intros.
  assert (H := derivable_derive f1 x pr1).
  assert (H0 := derivable_derive f2 x pr2).
  assert
    (H1 := derivable_derive (f1 / f2)%F x (derivable_pt_div _ _ _ pr1 pr2 na)).
  elim H; clear H; intros l1 H.
  elim H0; clear H0; intros l2 H0.
  elim H1; clear H1; intros l H1.
  rewrite H; rewrite H0; apply derive_pt_eq_0.
  assert (H3 := proj2_sig pr1).
  unfold derive_pt in H; rewrite H in H3.
  assert (H4 := proj2_sig pr2).
  unfold derive_pt in H0; rewrite H0 in H4.
  apply derivable_pt_lim_div; assumption.
Qed.
