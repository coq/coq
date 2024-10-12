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
Require Import Ranalysis1.
Require Import R_sqrt.
Require Import Lra.
Local Open Scope R_scope.

(**********)
Lemma sqrt_var_maj :
  forall h:R, Rabs h <= 1 -> Rabs (sqrt (1 + h) - 1) <= Rabs h.
Proof.
  intros; assert (0 <= 1 + h). {
    destruct (total_order_T h 0) as [[Hlt|Heq]|Hgt].
    + rewrite (Rabs_left h Hlt) in H.
      apply Rplus_le_reg_l with (- h).
      rewrite Rplus_0_r; rewrite Rplus_comm; rewrite Rplus_assoc;
        rewrite Rplus_opp_r; rewrite Rplus_0_r; exact H.
    + left; rewrite Heq; rewrite Rplus_0_r; apply Rlt_0_1.
    + left; apply Rplus_lt_0_compat.
      * apply Rlt_0_1.
      * apply Hgt.
  }
  apply Rle_trans with (Rabs (sqrt (Rsqr (1 + h)) - 1)).
  2:{ rewrite sqrt_Rsqr.
      - replace (1 + h - 1) with h; [ right; reflexivity | ring ].
      - apply H0. }
  destruct (total_order_T h 0) as [[Hlt|Heq]|Hgt].
  - repeat rewrite Rabs_left.
    + unfold Rminus; do 2 rewrite <- (Rplus_comm (-1)).
      change (-1) with (-(1)).
      do 2 rewrite Ropp_plus_distr; rewrite Ropp_involutive;
      apply Rplus_le_compat_l.
      apply Ropp_le_contravar; apply sqrt_le_1.
      * apply Rle_0_sqr.
      * apply H0.
      * pattern (1 + h) at 2; rewrite <- Rmult_1_r; unfold Rsqr;
          apply Rmult_le_compat_l; lra.
    + apply Rplus_lt_reg_l with 1; rewrite Rplus_0_r; rewrite Rplus_comm;
        unfold Rminus; rewrite Rplus_assoc; rewrite Rplus_opp_l;
        rewrite Rplus_0_r.
      pattern 1 at 2; rewrite <- sqrt_1; apply sqrt_lt_1.
      * apply Rle_0_sqr.
      * left; apply Rlt_0_1.
      * pattern 1 at 2; rewrite <- Rsqr_1; apply Rsqr_incrst_1;lra.
    + apply Rplus_lt_reg_l with 1; rewrite Rplus_0_r; rewrite Rplus_comm;
        unfold Rminus; rewrite Rplus_assoc; rewrite Rplus_opp_l;
        rewrite Rplus_0_r.
      pattern 1 at 2; rewrite <- sqrt_1; apply sqrt_lt_1;lra.
  - rewrite Heq; rewrite Rplus_0_r; rewrite Rsqr_1; rewrite sqrt_1; right;
      reflexivity.
  - repeat rewrite Rabs_right.
    + unfold Rminus; do 2 rewrite <- (Rplus_comm (-1));
        apply Rplus_le_compat_l.
      apply sqrt_le_1.
      * apply H0.
      * apply Rle_0_sqr.
      * pattern (1 + h) at 1; rewrite <- Rmult_1_r; unfold Rsqr;
          apply Rmult_le_compat_l;lra.
    + apply Rle_ge; apply Rplus_le_reg_l with 1.
      rewrite Rplus_0_r; rewrite Rplus_comm; unfold Rminus;
        rewrite Rplus_assoc; rewrite Rplus_opp_l; rewrite Rplus_0_r.
      pattern 1 at 1; rewrite <- sqrt_1; apply sqrt_le_1.
      * left; apply Rlt_0_1.
      * apply Rle_0_sqr.
      * pattern 1 at 1; rewrite <- Rsqr_1; apply Rsqr_incr_1;lra.
    + apply Rle_ge; left; apply Rplus_lt_reg_l with 1.
      rewrite Rplus_0_r; rewrite Rplus_comm; unfold Rminus;
        rewrite Rplus_assoc; rewrite Rplus_opp_l; rewrite Rplus_0_r.
      pattern 1 at 1; rewrite <- sqrt_1; apply sqrt_lt_1;lra.
Qed.

(** sqrt is continuous in 1 *)
Lemma sqrt_continuity_pt_R1 : continuity_pt sqrt 1.
Proof.
  unfold continuity_pt; unfold continue_in;
    unfold limit1_in; unfold limit_in;
      unfold dist; simpl; unfold Rdist;
        intros.
  set (alpha := Rmin eps 1).
  exists alpha; intros.
  split.
  - unfold alpha; unfold Rmin; case (Rle_dec eps 1); intro.
    + assumption.
    + apply Rlt_0_1.
  - intros; elim H0; intros.
    rewrite sqrt_1; replace x with (1 + (x - 1)); [ idtac | ring ];
      apply Rle_lt_trans with (Rabs (x - 1)).
    + apply sqrt_var_maj.
      apply Rle_trans with alpha.
      * left; apply H2.
      * unfold alpha; apply Rmin_r.
    + apply Rlt_le_trans with alpha;
        [ apply H2 | unfold alpha; apply Rmin_l ].
Qed.

(** sqrt is continuous forall x>0 *)
Lemma sqrt_continuity_pt : forall x:R, 0 < x -> continuity_pt sqrt x.
Proof.
  intros; generalize sqrt_continuity_pt_R1.
  unfold continuity_pt; unfold continue_in;
    unfold limit1_in; unfold limit_in;
      unfold dist; simpl; unfold Rdist;
        intros.
  assert (0 < eps / sqrt x). {
    unfold Rdiv; apply Rmult_lt_0_compat.
    - apply H1.
    - apply Rinv_0_lt_compat; apply sqrt_lt_R0; apply H.
  }
  elim (H0 _ H2); intros alp_1 H3.
  elim H3; intros.
  set (alpha := alp_1 * x).
  exists (Rmin alpha x); intros.
  split.
  { change (0 < Rmin alpha x); unfold Rmin;
    case (Rle_dec alpha x); intro.
    - unfold alpha; apply Rmult_lt_0_compat; assumption.
    - apply H. }
  intros; replace x0 with (x + (x0 - x)); [ idtac | ring ];
    replace (sqrt (x + (x0 - x)) - sqrt x) with
    (sqrt x * (sqrt (1 + (x0 - x) / x) - sqrt 1)).
  2:{ unfold Rminus; rewrite Rmult_plus_distr_l;
      rewrite Ropp_mult_distr_r_reverse; repeat rewrite <- sqrt_mult.
      - rewrite Rmult_1_r; rewrite Rmult_plus_distr_l; rewrite Rmult_1_r;
          unfold Rdiv; rewrite Rmult_comm; rewrite Rmult_assoc;
          rewrite Rinv_l.
        + rewrite Rmult_1_r; reflexivity.
        + red; intro; rewrite H7 in H; elim (Rlt_irrefl _ H).
      - left; apply H.
      - left; apply Rlt_0_1.
      - left; apply H.
      - elim H6; intros.
        destruct (Rcase_abs (x0 - x)) as [Hlt|Hgt].
        + rewrite (Rabs_left (x0 - x) Hlt) in H8.
          rewrite Rplus_comm.
          apply Rplus_le_reg_l with (- ((x0 - x) / x)).
          rewrite Rplus_0_r; rewrite <- Rplus_assoc; rewrite Rplus_opp_l;
            rewrite Rplus_0_l; unfold Rdiv; rewrite <- Ropp_mult_distr_l_reverse.
          apply Rmult_le_reg_l with x.
          * apply H.
          * rewrite Rmult_1_r; rewrite Rmult_comm; rewrite Rmult_assoc;
              rewrite Rinv_l.
            -- rewrite Rmult_1_r; left; apply Rlt_le_trans with (Rmin alpha x).
               ++ apply H8.
               ++ apply Rmin_r.
            -- lra.
        + apply Rplus_le_le_0_compat.
          * lra.
          * unfold Rdiv; apply Rmult_le_pos.
            -- lra.
            -- left; apply Rinv_0_lt_compat; apply H. }
  rewrite Rabs_mult; rewrite (Rabs_right (sqrt x)).
  2:{ apply Rle_ge; apply sqrt_positivity.
      left; apply H. }
  apply Rmult_lt_reg_l with (/ sqrt x).
  { apply Rinv_0_lt_compat; apply sqrt_lt_R0; assumption. }
  rewrite <- Rmult_assoc; rewrite Rinv_l.
  2:{ assert (H7 := sqrt_lt_R0 x H). lra. }
  rewrite Rmult_1_l; rewrite Rmult_comm.
  unfold Rdiv in H5.
  case (Req_dec x x0); intro.
  { rewrite H7; unfold Rminus, Rdiv; rewrite Rplus_opp_r;
    rewrite Rmult_0_l; rewrite Rplus_0_r; rewrite Rplus_opp_r;
    rewrite Rabs_R0.
    apply Rmult_lt_0_compat.
    - assumption.
    - apply Rinv_0_lt_compat; rewrite <- H7; apply sqrt_lt_R0; assumption. }
  apply H5.
  split.
  - unfold D_x, no_cond.
    split.
    + trivial.
    + red; intro.
      assert ((x0 - x) * / x = 0) by lra.
      elim (Rmult_integral _ _ H9); intro.
      { lra. }
      assert (H11 := Rmult_eq_0_compat_r _ x H10).
      rewrite Rinv_l in H11;lra.
  - unfold Rminus; rewrite Rplus_comm; rewrite <- Rplus_assoc;
      rewrite Rplus_opp_l; rewrite Rplus_0_l; elim H6; intros.
    unfold Rdiv; rewrite Rabs_mult.
    rewrite Rabs_inv.
    rewrite (Rabs_right x).
    + rewrite Rmult_comm; apply Rmult_lt_reg_l with x.
      { apply H. }
      rewrite <- Rmult_assoc; rewrite Rinv_r.
      2:{ lra. }
      rewrite Rmult_1_l; rewrite Rmult_comm; fold alpha.
      apply Rlt_le_trans with (Rmin alpha x).
      * apply H9.
      * apply Rmin_l.
    + apply Rle_ge; left; apply H.
Qed.

(** sqrt is derivable for all x>0 *)
Lemma derivable_pt_lim_sqrt :
  forall x:R, 0 < x -> derivable_pt_lim sqrt x (/ (2 * sqrt x)).
Proof.
  intros; set (g := fun h:R => sqrt x + sqrt (x + h)).
  assert (continuity_pt g 0). {
    replace g with (fct_cte (sqrt x) + comp sqrt (fct_cte x + id))%F;
      [ idtac | reflexivity ].
    apply continuity_pt_plus.
    - apply continuity_pt_const; unfold constant, fct_cte; intro;
        reflexivity.
    - apply continuity_pt_comp.
      + apply continuity_pt_plus.
        * apply continuity_pt_const; unfold constant, fct_cte; intro;
            reflexivity.
        * apply derivable_continuous_pt; apply derivable_pt_id.
      + apply sqrt_continuity_pt.
        unfold plus_fct, fct_cte, id; rewrite Rplus_0_r; apply H.
  }
  assert (g 0 <> 0). {
    unfold g; rewrite Rplus_0_r.
    assert (0 < sqrt x + sqrt x);[|lra].
    apply Rplus_lt_0_compat; apply sqrt_lt_R0; apply H.
  }
  intro; assert (H2 := continuity_pt_inv g 0 H0 H1).
  unfold derivable_pt_lim; intros; unfold continuity_pt in H2;
    unfold continue_in in H2; unfold limit1_in in H2;
      unfold limit_in in H2; simpl in H2; unfold Rdist in H2.
  elim (H2 eps H3); intros alpha H4.
  elim H4; intros.
  set (alpha1 := Rmin alpha x).
  assert (0 < alpha1). {
    unfold alpha1; unfold Rmin; case (Rle_dec alpha x); intro;lra.
  }
  exists (mkposreal alpha1 H7); intros.
  replace ((sqrt (x + h) - sqrt x) / h) with (/ (sqrt x + sqrt (x + h))).
  { unfold inv_fct, g in H6; replace (2 * sqrt x) with (sqrt x + sqrt (x + 0)).
    - apply H6.
      split.
      + unfold D_x, no_cond.
        split.
        * trivial.
        * apply (not_eq_sym (A:=R)); exact H8.
      + unfold Rminus; rewrite Ropp_0; rewrite Rplus_0_r;
          apply Rlt_le_trans with alpha1.
        * exact H9.
        * unfold alpha1; apply Rmin_l.
    - rewrite Rplus_0_r; ring. }
  assert (0 <= x + h). {
    destruct (Rcase_abs h) as [Hlt|Hgt].
    2:lra.
    rewrite (Rabs_left h Hlt) in H9.
    apply Rplus_le_reg_l with (- h).
    rewrite Rplus_0_r; rewrite Rplus_comm; rewrite Rplus_assoc;
      rewrite Rplus_opp_r; rewrite Rplus_0_r; left; apply Rlt_le_trans with alpha1.
    - apply H9.
    - unfold alpha1; apply Rmin_r.
  }
  assert (0 < sqrt x + sqrt (x + h)). {
    apply Rplus_lt_le_0_compat.
    - apply sqrt_lt_R0; apply H.
    - apply sqrt_positivity; apply H10.
  }
  apply Rmult_eq_reg_l with (sqrt x + sqrt (x + h)).
  2:lra.
  rewrite Rinv_r.
  2:lra.
  rewrite Rplus_comm; unfold Rdiv; rewrite <- Rmult_assoc;
    rewrite Rsqr_plus_minus; repeat rewrite Rsqr_sqrt.
  2,3: lra.
  rewrite Rplus_comm; unfold Rminus; rewrite Rplus_assoc;
    rewrite Rplus_opp_r; rewrite Rplus_0_r; rewrite Rinv_r;lra.
Qed.

(**********)
Lemma derivable_pt_sqrt : forall x:R, 0 < x -> derivable_pt sqrt x.
Proof.
  unfold derivable_pt; intros.
  exists (/ (2 * sqrt x)).
  apply derivable_pt_lim_sqrt; assumption.
Qed.

(**********)
Lemma derive_pt_sqrt :
  forall (x:R) (pr:0 < x),
    derive_pt sqrt x (derivable_pt_sqrt _ pr) = / (2 * sqrt x).
Proof.
  intros.
  apply derive_pt_eq_0.
  apply derivable_pt_lim_sqrt; assumption.
Qed.

(** We show that sqrt is continuous for all x>=0 *)
(** Remark : by definition of sqrt (as extension of Rsqrt on |R),
   we could also show that sqrt is continuous for all x *)
Lemma continuity_pt_sqrt : forall x:R, 0 <= x -> continuity_pt sqrt x.
Proof.
  intros; case (Rtotal_order 0 x); intro.
  { apply (sqrt_continuity_pt x H0). }
  elim H0; intro.
  2:exfalso;lra.
  unfold continuity_pt; unfold continue_in;
    unfold limit1_in; unfold limit_in;
    simpl; unfold Rdist; intros.
  exists (Rsqr eps); intros.
  split.
  { change (0 < Rsqr eps); apply Rsqr_pos_lt;lra. }
  intros; elim H3; intros.
  rewrite <- H1; rewrite sqrt_0; unfold Rminus; rewrite Ropp_0;
    rewrite Rplus_0_r; rewrite <- H1 in H5; unfold Rminus in H5;
    rewrite Ropp_0 in H5; rewrite Rplus_0_r in H5.
  destruct (Rcase_abs x0) as [Hlt|Hgt] eqn:Heqs.
  { unfold sqrt. rewrite Heqs.
    rewrite Rabs_R0; apply H2. }
  rewrite Rabs_right.
  2: apply Rle_ge; apply sqrt_positivity; apply Rge_le; exact Hgt.
  apply Rsqr_incrst_0.
  - rewrite Rsqr_sqrt.
    + rewrite (Rabs_right x0 Hgt) in H5; apply H5.
    + apply Rge_le; exact Hgt.
  - apply sqrt_positivity; apply Rge_le; exact Hgt.
  - left; exact H2.
Qed.
