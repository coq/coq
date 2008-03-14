(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Import Rbase.
Require Import Rbasic_fun. Open Local Scope R_scope.

(****************************************************)
(** Rsqr : some results                             *)
(****************************************************)

Ltac ring_Rsqr := unfold Rsqr in |- *; ring.

Lemma Rsqr_neg : forall x:R, Rsqr x = Rsqr (- x).
Proof.
  intros; ring_Rsqr.
Qed.

Lemma Rsqr_mult : forall x y:R, Rsqr (x * y) = Rsqr x * Rsqr y.
Proof.
  intros; ring_Rsqr.
Qed.

Lemma Rsqr_plus : forall x y:R, Rsqr (x + y) = Rsqr x + Rsqr y + 2 * x * y.
Proof.
  intros; ring_Rsqr.
Qed.

Lemma Rsqr_minus : forall x y:R, Rsqr (x - y) = Rsqr x + Rsqr y - 2 * x * y.
Proof.
  intros; ring_Rsqr.
Qed.

Lemma Rsqr_neg_minus : forall x y:R, Rsqr (x - y) = Rsqr (y - x).
Proof.
  intros; ring_Rsqr.
Qed.

Lemma Rsqr_1 : Rsqr 1 = 1.
Proof.
  ring_Rsqr.
Qed.

Lemma Rsqr_gt_0_0 : forall x:R, 0 < Rsqr x -> x <> 0.
Proof.
  intros; red in |- *; intro; rewrite H0 in H; rewrite Rsqr_0 in H;
    elim (Rlt_irrefl 0 H).
Qed.

Lemma Rsqr_pos_lt : forall x:R, x <> 0 -> 0 < Rsqr x.
Proof.
  intros; case (Rtotal_order 0 x); intro;
    [ unfold Rsqr in |- *; apply Rmult_lt_0_compat; assumption
      | elim H0; intro;
        [ elim H; symmetry  in |- *; exact H1
          | rewrite Rsqr_neg; generalize (Ropp_lt_gt_contravar x 0 H1);
            rewrite Ropp_0; intro; unfold Rsqr in |- *; 
              apply Rmult_lt_0_compat; assumption ] ].
Qed.

Lemma Rsqr_div : forall x y:R, y <> 0 -> Rsqr (x / y) = Rsqr x / Rsqr y.
Proof.
  intros; unfold Rsqr in |- *.
  unfold Rdiv in |- *.
  rewrite Rinv_mult_distr.
  repeat rewrite Rmult_assoc.
  apply Rmult_eq_compat_l.
  pattern x at 2 in |- *; rewrite Rmult_comm.
  repeat rewrite Rmult_assoc.
  apply Rmult_eq_compat_l.
  reflexivity.
  assumption.
  assumption.
Qed.

Lemma Rsqr_eq_0 : forall x:R, Rsqr x = 0 -> x = 0.
Proof.
  unfold Rsqr in |- *; intros; generalize (Rmult_integral x x H); intro;
    elim H0; intro; assumption.
Qed.

Lemma Rsqr_minus_plus : forall a b:R, (a - b) * (a + b) = Rsqr a - Rsqr b.
Proof.
  intros; ring_Rsqr.
Qed.

Lemma Rsqr_plus_minus : forall a b:R, (a + b) * (a - b) = Rsqr a - Rsqr b.
Proof.
  intros; ring_Rsqr.
Qed.

Lemma Rsqr_incr_0 :
  forall x y:R, Rsqr x <= Rsqr y -> 0 <= x -> 0 <= y -> x <= y.
Proof.
  intros; case (Rle_dec x y); intro;
    [ assumption
      | cut (y < x);
        [ intro; unfold Rsqr in H;
          generalize (Rmult_le_0_lt_compat y x y x H1 H1 H2 H2); 
            intro; generalize (Rle_lt_trans (x * x) (y * y) (x * x) H H3); 
              intro; elim (Rlt_irrefl (x * x) H4)
          | auto with real ] ].
Qed.

Lemma Rsqr_incr_0_var : forall x y:R, Rsqr x <= Rsqr y -> 0 <= y -> x <= y.
Proof.
  intros; case (Rle_dec x y); intro;
    [ assumption
      | cut (y < x);
        [ intro; unfold Rsqr in H;
          generalize (Rmult_le_0_lt_compat y x y x H0 H0 H1 H1); 
            intro; generalize (Rle_lt_trans (x * x) (y * y) (x * x) H H2); 
              intro; elim (Rlt_irrefl (x * x) H3)
          | auto with real ] ].
Qed.

Lemma Rsqr_incr_1 :
  forall x y:R, x <= y -> 0 <= x -> 0 <= y -> Rsqr x <= Rsqr y.
Proof.
  intros; unfold Rsqr in |- *; apply Rmult_le_compat; assumption.
Qed.

Lemma Rsqr_incrst_0 :
  forall x y:R, Rsqr x < Rsqr y -> 0 <= x -> 0 <= y -> x < y.
Proof.
  intros; case (Rtotal_order x y); intro;
    [ assumption
      | elim H2; intro;
        [ rewrite H3 in H; elim (Rlt_irrefl (Rsqr y) H)
          | generalize (Rmult_le_0_lt_compat y x y x H1 H1 H3 H3); intro;
            unfold Rsqr in H; generalize (Rlt_trans (x * x) (y * y) (x * x) H H4);
              intro; elim (Rlt_irrefl (x * x) H5) ] ].
Qed.

Lemma Rsqr_incrst_1 :
  forall x y:R, x < y -> 0 <= x -> 0 <= y -> Rsqr x < Rsqr y.
Proof.
  intros; unfold Rsqr in |- *; apply Rmult_le_0_lt_compat; assumption.
Qed.

Lemma Rsqr_neg_pos_le_0 :
  forall x y:R, Rsqr x <= Rsqr y -> 0 <= y -> - y <= x.
Proof.
  intros; case (Rcase_abs x); intro.
  generalize (Ropp_lt_gt_contravar x 0 r); rewrite Ropp_0; intro;
    generalize (Rlt_le 0 (- x) H1); intro; rewrite (Rsqr_neg x) in H;
      generalize (Rsqr_incr_0 (- x) y H H2 H0); intro;
        rewrite <- (Ropp_involutive x); apply Ropp_ge_le_contravar; 
          apply Rle_ge; assumption.
  apply Rle_trans with 0;
    [ rewrite <- Ropp_0; apply Ropp_ge_le_contravar; apply Rle_ge; assumption
      | apply Rge_le; assumption ].
Qed.

Lemma Rsqr_neg_pos_le_1 :
  forall x y:R, - y <= x -> x <= y -> 0 <= y -> Rsqr x <= Rsqr y.
Proof.
  intros; case (Rcase_abs x); intro.
  generalize (Ropp_lt_gt_contravar x 0 r); rewrite Ropp_0; intro;
    generalize (Rlt_le 0 (- x) H2); intro;
      generalize (Ropp_le_ge_contravar (- y) x H); rewrite Ropp_involutive; 
        intro; generalize (Rge_le y (- x) H4); intro; rewrite (Rsqr_neg x);
          apply Rsqr_incr_1; assumption.
  generalize (Rge_le x 0 r); intro; apply Rsqr_incr_1; assumption.
Qed.

Lemma neg_pos_Rsqr_le : forall x y:R, - y <= x -> x <= y -> Rsqr x <= Rsqr y.
Proof.
  intros; case (Rcase_abs x); intro.
  generalize (Ropp_lt_gt_contravar x 0 r); rewrite Ropp_0; intro;
    generalize (Ropp_le_ge_contravar (- y) x H); rewrite Ropp_involutive; 
      intro; generalize (Rge_le y (- x) H2); intro; generalize (Rlt_le 0 (- x) H1);
        intro; generalize (Rle_trans 0 (- x) y H4 H3); intro; 
          rewrite (Rsqr_neg x); apply Rsqr_incr_1; assumption.
  generalize (Rge_le x 0 r); intro; generalize (Rle_trans 0 x y H1 H0); intro;
    apply Rsqr_incr_1; assumption.
Qed.

Lemma Rsqr_abs : forall x:R, Rsqr x = Rsqr (Rabs x).
Proof.
  intro; unfold Rabs in |- *; case (Rcase_abs x); intro;
    [ apply Rsqr_neg | reflexivity ].
Qed.

Lemma Rsqr_le_abs_0 : forall x y:R, Rsqr x <= Rsqr y -> Rabs x <= Rabs y.
Proof.
  intros; apply Rsqr_incr_0; repeat rewrite <- Rsqr_abs;
    [ assumption | apply Rabs_pos | apply Rabs_pos ].
Qed.

Lemma Rsqr_le_abs_1 : forall x y:R, Rabs x <= Rabs y -> Rsqr x <= Rsqr y.
Proof.
  intros; rewrite (Rsqr_abs x); rewrite (Rsqr_abs y);
    apply (Rsqr_incr_1 (Rabs x) (Rabs y) H (Rabs_pos x) (Rabs_pos y)).
Qed.

Lemma Rsqr_lt_abs_0 : forall x y:R, Rsqr x < Rsqr y -> Rabs x < Rabs y.
Proof.
  intros; apply Rsqr_incrst_0; repeat rewrite <- Rsqr_abs;
    [ assumption | apply Rabs_pos | apply Rabs_pos ].
Qed.

Lemma Rsqr_lt_abs_1 : forall x y:R, Rabs x < Rabs y -> Rsqr x < Rsqr y.
Proof.
  intros; rewrite (Rsqr_abs x); rewrite (Rsqr_abs y);
    apply (Rsqr_incrst_1 (Rabs x) (Rabs y) H (Rabs_pos x) (Rabs_pos y)).
Qed.

Lemma Rsqr_inj : forall x y:R, 0 <= x -> 0 <= y -> Rsqr x = Rsqr y -> x = y.
Proof.
  intros; generalize (Rle_le_eq (Rsqr x) (Rsqr y)); intro; elim H2; intros _ H3;
    generalize (H3 H1); intro; elim H4; intros; apply Rle_antisym;
      apply Rsqr_incr_0; assumption.
Qed.

Lemma Rsqr_eq_abs_0 : forall x y:R, Rsqr x = Rsqr y -> Rabs x = Rabs y.
Proof.
  intros; unfold Rabs in |- *; case (Rcase_abs x); case (Rcase_abs y); intros.
  rewrite (Rsqr_neg x) in H; rewrite (Rsqr_neg y) in H;
    generalize (Ropp_lt_gt_contravar y 0 r);
      generalize (Ropp_lt_gt_contravar x 0 r0); rewrite Ropp_0; 
        intros; generalize (Rlt_le 0 (- x) H0); generalize (Rlt_le 0 (- y) H1);
          intros; apply Rsqr_inj; assumption.
  rewrite (Rsqr_neg x) in H; generalize (Rge_le y 0 r); intro;
    generalize (Ropp_lt_gt_contravar x 0 r0); rewrite Ropp_0; 
      intro; generalize (Rlt_le 0 (- x) H1); intro; apply Rsqr_inj; 
        assumption.
  rewrite (Rsqr_neg y) in H; generalize (Rge_le x 0 r0); intro;
    generalize (Ropp_lt_gt_contravar y 0 r); rewrite Ropp_0; 
      intro; generalize (Rlt_le 0 (- y) H1); intro; apply Rsqr_inj; 
        assumption.
  generalize (Rge_le x 0 r0); generalize (Rge_le y 0 r); intros; apply Rsqr_inj;
    assumption.
Qed.

Lemma Rsqr_eq_asb_1 : forall x y:R, Rabs x = Rabs y -> Rsqr x = Rsqr y.
Proof.
  intros; cut (Rsqr (Rabs x) = Rsqr (Rabs y)).
  intro; repeat rewrite <- Rsqr_abs in H0; assumption.
  rewrite H; reflexivity.
Qed.

Lemma triangle_rectangle :
  forall x y z:R,
    0 <= z -> Rsqr x + Rsqr y <= Rsqr z -> - z <= x <= z /\ - z <= y <= z.
Proof.
  intros;
    generalize (plus_le_is_le (Rsqr x) (Rsqr y) (Rsqr z) (Rle_0_sqr y) H0);
      rewrite Rplus_comm in H0;
        generalize (plus_le_is_le (Rsqr y) (Rsqr x) (Rsqr z) (Rle_0_sqr x) H0);
          intros; split;
            [ split;
              [ apply Rsqr_neg_pos_le_0; assumption
                | apply Rsqr_incr_0_var; assumption ]
              | split;
                [ apply Rsqr_neg_pos_le_0; assumption
                  | apply Rsqr_incr_0_var; assumption ] ].
Qed.

Lemma triangle_rectangle_lt :
  forall x y z:R,
    Rsqr x + Rsqr y < Rsqr z -> Rabs x < Rabs z /\ Rabs y < Rabs z.
Proof.
  intros; split;
    [ generalize (plus_lt_is_lt (Rsqr x) (Rsqr y) (Rsqr z) (Rle_0_sqr y) H);
      intro; apply Rsqr_lt_abs_0; assumption
      | rewrite Rplus_comm in H;
        generalize (plus_lt_is_lt (Rsqr y) (Rsqr x) (Rsqr z) (Rle_0_sqr x) H);
          intro; apply Rsqr_lt_abs_0; assumption ].
Qed.

Lemma triangle_rectangle_le :
  forall x y z:R,
    Rsqr x + Rsqr y <= Rsqr z -> Rabs x <= Rabs z /\ Rabs y <= Rabs z.
Proof.
  intros; split;
    [ generalize (plus_le_is_le (Rsqr x) (Rsqr y) (Rsqr z) (Rle_0_sqr y) H);
      intro; apply Rsqr_le_abs_0; assumption
      | rewrite Rplus_comm in H;
        generalize (plus_le_is_le (Rsqr y) (Rsqr x) (Rsqr z) (Rle_0_sqr x) H);
          intro; apply Rsqr_le_abs_0; assumption ].
Qed.

Lemma Rsqr_inv : forall x:R, x <> 0 -> Rsqr (/ x) = / Rsqr x.
Proof.
  intros; unfold Rsqr in |- *.
  rewrite Rinv_mult_distr; try reflexivity || assumption.
Qed.

Lemma canonical_Rsqr :
  forall (a:nonzeroreal) (b c x:R),
    a * Rsqr x + b * x + c =
    a * Rsqr (x + b / (2 * a)) + (4 * a * c - Rsqr b) / (4 * a).
Proof.
  intros.
  rewrite Rsqr_plus.
  repeat rewrite Rmult_plus_distr_l.
  repeat rewrite Rplus_assoc.
  apply Rplus_eq_compat_l.
  unfold Rdiv, Rminus in |- *.
  replace (2 * 1 + 2 * 1) with 4; [ idtac | ring ].
  rewrite (Rmult_plus_distr_r (4 * a * c) (- Rsqr b) (/ (4 * a))).
  rewrite Rsqr_mult.
  repeat rewrite Rinv_mult_distr.
  repeat rewrite (Rmult_comm a).
  repeat rewrite Rmult_assoc.
  rewrite <- Rinv_l_sym.
  rewrite Rmult_1_r.
  rewrite (Rmult_comm 2).
  repeat rewrite Rmult_assoc.
  rewrite <- Rinv_l_sym.
  rewrite Rmult_1_r.
  rewrite (Rmult_comm (/ 2)).
  rewrite (Rmult_comm 2).
  repeat rewrite Rmult_assoc; rewrite <- Rinv_l_sym.
  rewrite Rmult_1_r.
  rewrite (Rmult_comm a).
  repeat rewrite Rmult_assoc.
  rewrite <- Rinv_l_sym.
  rewrite Rmult_1_r.
  rewrite (Rmult_comm 2).
  repeat rewrite Rmult_assoc; rewrite <- Rinv_l_sym.
  rewrite Rmult_1_r.
  repeat rewrite Rplus_assoc.
  rewrite (Rplus_comm (Rsqr b * (Rsqr (/ a * / 2) * a))).
  repeat rewrite Rplus_assoc.
  rewrite (Rmult_comm x).
  apply Rplus_eq_compat_l.
  rewrite (Rmult_comm (/ a)).
  unfold Rsqr in |- *; repeat rewrite Rmult_assoc.
  rewrite <- Rinv_l_sym.
  rewrite Rmult_1_r.
  ring.
  apply (cond_nonzero a).
  discrR.
  apply (cond_nonzero a).
  discrR.
  discrR.
  apply (cond_nonzero a).
  discrR.
  discrR.
  discrR.
  apply (cond_nonzero a).
  discrR.
  apply (cond_nonzero a).
Qed.

Lemma Rsqr_eq : forall x y:R, Rsqr x = Rsqr y -> x = y \/ x = - y.
Proof.
  intros; unfold Rsqr in H;
    generalize (Rplus_eq_compat_l (- (y * y)) (x * x) (y * y) H);
      rewrite Rplus_opp_l; replace (- (y * y) + x * x) with ((x - y) * (x + y)).
  intro; generalize (Rmult_integral (x - y) (x + y) H0); intro; elim H1; intros.
  left; apply Rminus_diag_uniq; assumption.
  right; apply Rminus_diag_uniq; unfold Rminus in |- *; rewrite Ropp_involutive;
    assumption.
  ring.
Qed.
