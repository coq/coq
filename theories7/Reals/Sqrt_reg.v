(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
 
(*i $Id$ i*)

Require Rbase.
Require Rfunctions.
Require Ranalysis1.
Require R_sqrt.
V7only [Import R_scope.]. Open Local Scope R_scope.

(**********)
Lemma sqrt_var_maj : (h:R) ``(Rabsolu h) <= 1`` -> ``(Rabsolu ((sqrt (1+h))-1))<=(Rabsolu h)``.
Intros; Cut ``0<=1+h``.
Intro; Apply Rle_trans with ``(Rabsolu ((sqrt (Rsqr (1+h)))-1))``.
Case (total_order_T h R0); Intro.
Elim s; Intro.
Repeat Rewrite Rabsolu_left.
Unfold Rminus; Do 2 Rewrite <- (Rplus_sym ``-1``).
Do 2 Rewrite Ropp_distr1;Rewrite Ropp_Ropp; Apply Rle_compatibility.
Apply Rle_Ropp1; Apply sqrt_le_1.
Apply pos_Rsqr.
Apply H0.
Pattern 2 ``1+h``; Rewrite <- Rmult_1r; Unfold Rsqr; Apply Rle_monotony.
Apply H0.
Pattern 2 R1; Rewrite <- Rplus_Or; Apply Rle_compatibility; Left; Assumption.
Apply Rlt_anti_compatibility with R1; Rewrite Rplus_Or; Rewrite Rplus_sym; Unfold Rminus; Rewrite Rplus_assoc; Rewrite Rplus_Ropp_l; Rewrite Rplus_Or.
Pattern 2 R1; Rewrite <- sqrt_1; Apply sqrt_lt_1.
Apply pos_Rsqr.
Left; Apply Rlt_R0_R1.
Pattern 2 R1; Rewrite <- Rsqr_1; Apply Rsqr_incrst_1.
Pattern 2 R1; Rewrite <- Rplus_Or; Apply Rlt_compatibility; Assumption.
Apply H0.
Left; Apply Rlt_R0_R1.
Apply Rlt_anti_compatibility with R1; Rewrite Rplus_Or; Rewrite Rplus_sym; Unfold Rminus; Rewrite Rplus_assoc; Rewrite Rplus_Ropp_l; Rewrite Rplus_Or.
Pattern 2 R1; Rewrite <- sqrt_1; Apply sqrt_lt_1.
Apply H0.
Left; Apply Rlt_R0_R1.
Pattern 2 R1; Rewrite <- Rplus_Or; Apply Rlt_compatibility; Assumption.
Rewrite b; Rewrite Rplus_Or; Rewrite Rsqr_1; Rewrite sqrt_1; Right; Reflexivity.
Repeat Rewrite Rabsolu_right.
Unfold Rminus; Do 2 Rewrite <- (Rplus_sym ``-1``); Apply Rle_compatibility.
Apply sqrt_le_1.
Apply H0.
Apply pos_Rsqr.
Pattern 1 ``1+h``; Rewrite <- Rmult_1r; Unfold Rsqr; Apply Rle_monotony.
Apply H0.
Pattern 1 R1; Rewrite <- Rplus_Or; Apply Rle_compatibility; Left; Assumption.
Apply Rle_sym1; Apply Rle_anti_compatibility with R1.
Rewrite Rplus_Or; Rewrite Rplus_sym; Unfold Rminus; Rewrite Rplus_assoc; Rewrite Rplus_Ropp_l; Rewrite Rplus_Or.
Pattern 1 R1; Rewrite <- sqrt_1; Apply sqrt_le_1.
Left; Apply Rlt_R0_R1.
Apply pos_Rsqr.
Pattern 1 R1; Rewrite <- Rsqr_1; Apply Rsqr_incr_1.
Pattern 1 R1; Rewrite <- Rplus_Or; Apply Rle_compatibility; Left; Assumption.
Left; Apply Rlt_R0_R1.
Apply H0.
Apply Rle_sym1; Left; Apply Rlt_anti_compatibility with R1.
Rewrite Rplus_Or; Rewrite Rplus_sym; Unfold Rminus; Rewrite Rplus_assoc; Rewrite Rplus_Ropp_l; Rewrite Rplus_Or.
Pattern 1 R1; Rewrite <- sqrt_1; Apply sqrt_lt_1.
Left; Apply Rlt_R0_R1.
Apply H0.
Pattern 1 R1; Rewrite <- Rplus_Or; Apply Rlt_compatibility; Assumption.
Rewrite sqrt_Rsqr.
Replace ``(1+h)-1`` with h; [Right; Reflexivity | Ring].
Apply H0.
Case (total_order_T h R0); Intro.
Elim s; Intro.
Rewrite (Rabsolu_left h a) in H.
Apply Rle_anti_compatibility with ``-h``.
Rewrite Rplus_Or; Rewrite Rplus_sym; Rewrite Rplus_assoc; Rewrite Rplus_Ropp_r; Rewrite Rplus_Or; Exact H.
Left; Rewrite b; Rewrite Rplus_Or; Apply Rlt_R0_R1.
Left; Apply gt0_plus_gt0_is_gt0.
Apply Rlt_R0_R1.
Apply r.
Qed.

(* sqrt is continuous in 1 *)
Lemma sqrt_continuity_pt_R1 : (continuity_pt sqrt R1).
Unfold continuity_pt; Unfold continue_in; Unfold limit1_in; Unfold limit_in; Unfold dist; Simpl; Unfold R_dist; Intros.
Pose alpha := (Rmin eps R1).
Exists alpha; Intros.
Split.
Unfold alpha; Unfold Rmin; Case (total_order_Rle eps R1); Intro.
Assumption.
Apply Rlt_R0_R1.
Intros; Elim H0; Intros.
Rewrite sqrt_1; Replace x with ``1+(x-1)``; [Idtac | Ring]; Apply Rle_lt_trans with ``(Rabsolu (x-1))``.
Apply sqrt_var_maj.
Apply Rle_trans with alpha.
Left; Apply H2.
Unfold alpha; Apply Rmin_r.
Apply Rlt_le_trans with alpha; [Apply H2 | Unfold alpha; Apply Rmin_l].
Qed.

(* sqrt is continuous forall x>0 *)
Lemma sqrt_continuity_pt : (x:R) ``0<x`` -> (continuity_pt sqrt x).
Intros; Generalize sqrt_continuity_pt_R1.
Unfold continuity_pt; Unfold continue_in; Unfold limit1_in; Unfold limit_in; Unfold dist; Simpl; Unfold R_dist; Intros.
Cut ``0<eps/(sqrt x)``.
Intro; Elim (H0 ? H2); Intros alp_1 H3.
Elim H3; Intros.
Pose alpha := ``alp_1*x``.
Exists (Rmin alpha x); Intros.
Split.
Change ``0<(Rmin alpha x)``; Unfold Rmin; Case (total_order_Rle alpha x); Intro.
Unfold alpha; Apply Rmult_lt_pos; Assumption.
Apply H.
Intros; Replace x0 with ``x+(x0-x)``; [Idtac | Ring]; Replace ``(sqrt (x+(x0-x)))-(sqrt x)`` with ``(sqrt x)*((sqrt (1+(x0-x)/x))-(sqrt 1))``.
Rewrite Rabsolu_mult; Rewrite (Rabsolu_right (sqrt x)).
Apply Rlt_monotony_contra with ``/(sqrt x)``.
Apply Rlt_Rinv; Apply sqrt_lt_R0; Assumption.
Rewrite <- Rmult_assoc; Rewrite <- Rinv_l_sym.
Rewrite Rmult_1l; Rewrite Rmult_sym.
Unfold Rdiv in H5.
Case (Req_EM x x0); Intro.
Rewrite H7; Unfold Rminus Rdiv; Rewrite Rplus_Ropp_r; Rewrite Rmult_Ol; Rewrite Rplus_Or; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0.
Apply Rmult_lt_pos.
Assumption.
Apply Rlt_Rinv; Rewrite <- H7; Apply sqrt_lt_R0; Assumption.
Apply H5.
Split.
Unfold D_x no_cond.
Split.
Trivial.
Red; Intro.
Cut ``(x0-x)*/x==0``.
Intro.
Elim (without_div_Od ? ? H9); Intro.
Elim H7.
Apply (Rminus_eq_right ? ? H10).
Assert H11 := (without_div_Oi1 ? x H10).
Rewrite <- Rinv_l_sym in H11.
Elim R1_neq_R0; Exact H11.
Red; Intro; Rewrite H12 in H; Elim (Rlt_antirefl ? H).
Symmetry; Apply r_Rplus_plus with R1; Rewrite Rplus_Or; Unfold Rdiv in H8; Exact H8.
Unfold Rminus; Rewrite Rplus_sym; Rewrite <- Rplus_assoc; Rewrite Rplus_Ropp_l; Rewrite Rplus_Ol; Elim H6; Intros.
Unfold Rdiv; Rewrite Rabsolu_mult.
Rewrite Rabsolu_Rinv.
Rewrite (Rabsolu_right x).
Rewrite Rmult_sym; Apply Rlt_monotony_contra with x.
Apply H.
Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym.
Rewrite Rmult_1l; Rewrite Rmult_sym; Fold alpha.
Apply Rlt_le_trans with (Rmin alpha x).
Apply H9.
Apply Rmin_l.
Red; Intro; Rewrite H10 in H; Elim (Rlt_antirefl ? H).
Apply Rle_sym1; Left; Apply H.
Red; Intro; Rewrite H10 in H; Elim (Rlt_antirefl ? H).
Assert H7 := (sqrt_lt_R0 x H).
Red; Intro; Rewrite H8 in H7; Elim (Rlt_antirefl ? H7).
Apply Rle_sym1; Apply sqrt_positivity.
Left; Apply H.
Unfold Rminus; Rewrite Rmult_Rplus_distr; Rewrite Ropp_mul3; Repeat Rewrite <- sqrt_times.
Rewrite Rmult_1r; Rewrite Rmult_Rplus_distr; Rewrite Rmult_1r; Unfold Rdiv; Rewrite Rmult_sym; Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r; Reflexivity.
Red; Intro; Rewrite H7 in H; Elim (Rlt_antirefl ? H).
Left; Apply H.
Left; Apply Rlt_R0_R1.
Left; Apply H.
Elim H6; Intros.
Case (case_Rabsolu ``x0-x``); Intro.
Rewrite (Rabsolu_left ``x0-x`` r) in H8.
Rewrite Rplus_sym.
Apply Rle_anti_compatibility with ``-((x0-x)/x)``.
Rewrite Rplus_Or; Rewrite <- Rplus_assoc; Rewrite Rplus_Ropp_l; Rewrite Rplus_Ol; Unfold Rdiv; Rewrite <- Ropp_mul1.
Apply Rle_monotony_contra with x.
Apply H.
Rewrite Rmult_1r; Rewrite Rmult_sym; Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r; Left; Apply Rlt_le_trans with (Rmin alpha x).
Apply H8.
Apply Rmin_r.
Red; Intro; Rewrite H9 in H; Elim (Rlt_antirefl ? H).
Apply ge0_plus_ge0_is_ge0.
Left; Apply Rlt_R0_R1.
Unfold Rdiv; Apply Rmult_le_pos.
Apply Rle_sym2; Exact r.
Left; Apply Rlt_Rinv; Apply H.
Unfold Rdiv; Apply Rmult_lt_pos.
Apply H1.
Apply Rlt_Rinv; Apply sqrt_lt_R0; Apply H.
Qed.

(* sqrt is derivable for all x>0 *)
Lemma derivable_pt_lim_sqrt : (x:R) ``0<x`` -> (derivable_pt_lim sqrt x ``/(2*(sqrt x))``).
Intros; Pose g := [h:R]``(sqrt x)+(sqrt (x+h))``.
Cut (continuity_pt g R0).
Intro; Cut ``(g 0)<>0``.
Intro; Assert H2 := (continuity_pt_inv g R0 H0 H1).
Unfold derivable_pt_lim; Intros; Unfold continuity_pt in H2; Unfold continue_in in H2; Unfold limit1_in in H2; Unfold limit_in in H2; Simpl in H2; Unfold R_dist in H2.
Elim (H2 eps H3); Intros alpha H4.
Elim H4; Intros.
Pose alpha1 := (Rmin alpha x).
Cut ``0<alpha1``.
Intro; Exists (mkposreal alpha1 H7); Intros.
Replace ``((sqrt (x+h))-(sqrt x))/h`` with ``/((sqrt x)+(sqrt (x+h)))``.
Unfold inv_fct g in H6; Replace ``2*(sqrt x)`` with ``(sqrt x)+(sqrt (x+0))``.
Apply H6.
Split.
Unfold D_x no_cond.
Split.
Trivial.
Apply not_sym; Exact H8.
Unfold Rminus; Rewrite Ropp_O; Rewrite Rplus_Or; Apply Rlt_le_trans with alpha1.
Exact H9.
Unfold alpha1; Apply Rmin_l.
Rewrite Rplus_Or; Ring.
Cut ``0<=x+h``.
Intro; Cut ``0<(sqrt x)+(sqrt (x+h))``.
Intro; Apply r_Rmult_mult with ``((sqrt x)+(sqrt (x+h)))``.
Rewrite <- Rinv_r_sym.
Rewrite Rplus_sym; Unfold Rdiv; Rewrite <- Rmult_assoc; Rewrite Rsqr_plus_minus; Repeat Rewrite Rsqr_sqrt.
Rewrite Rplus_sym; Unfold Rminus; Rewrite Rplus_assoc; Rewrite Rplus_Ropp_r; Rewrite Rplus_Or; Rewrite <- Rinv_r_sym.
Reflexivity.
Apply H8.
Left; Apply H.
Assumption.
Red; Intro; Rewrite H12 in H11; Elim (Rlt_antirefl ? H11).
Red; Intro; Rewrite H12 in H11; Elim (Rlt_antirefl ? H11).
Apply gt0_plus_ge0_is_gt0.
Apply sqrt_lt_R0; Apply H.
Apply sqrt_positivity; Apply H10.
Case (case_Rabsolu h); Intro.
Rewrite (Rabsolu_left h r) in H9.
Apply Rle_anti_compatibility with ``-h``.
Rewrite Rplus_Or; Rewrite Rplus_sym; Rewrite Rplus_assoc; Rewrite Rplus_Ropp_r; Rewrite Rplus_Or; Left; Apply Rlt_le_trans with alpha1.
Apply H9.
Unfold alpha1; Apply Rmin_r.
Apply ge0_plus_ge0_is_ge0.
Left; Assumption.
Apply Rle_sym2; Apply r.
Unfold alpha1; Unfold Rmin; Case (total_order_Rle alpha x); Intro.
Apply H5.
Apply H.
Unfold g; Rewrite Rplus_Or.
Cut ``0<(sqrt x)+(sqrt x)``.
Intro; Red; Intro; Rewrite H2 in H1; Elim (Rlt_antirefl ? H1).
Apply gt0_plus_gt0_is_gt0; Apply sqrt_lt_R0; Apply H.
Replace g with (plus_fct (fct_cte (sqrt x)) (comp sqrt (plus_fct (fct_cte x) id))); [Idtac | Reflexivity].
Apply continuity_pt_plus.
Apply continuity_pt_const; Unfold constant fct_cte; Intro; Reflexivity.
Apply continuity_pt_comp.
Apply continuity_pt_plus.
Apply continuity_pt_const; Unfold constant fct_cte; Intro; Reflexivity.
Apply derivable_continuous_pt; Apply derivable_pt_id.
Apply sqrt_continuity_pt.
Unfold plus_fct fct_cte id; Rewrite Rplus_Or; Apply H.
Qed.

(**********)
Lemma derivable_pt_sqrt : (x:R) ``0<x`` -> (derivable_pt sqrt x).
Unfold derivable_pt; Intros.
Apply Specif.existT with ``/(2*(sqrt x))``.
Apply derivable_pt_lim_sqrt; Assumption.
Qed.

(**********)
Lemma derive_pt_sqrt : (x:R;pr:``0<x``) ``(derive_pt sqrt x (derivable_pt_sqrt ? pr)) == /(2*(sqrt x))``.
Intros.
Apply derive_pt_eq_0.
Apply derivable_pt_lim_sqrt; Assumption.
Qed.

(* We show that sqrt is continuous for all x>=0 *)
(* Remark : by definition of sqrt (as extension of Rsqrt on |R), *)
(*          we could also show that sqrt is continuous for all x *)
Lemma continuity_pt_sqrt : (x:R) ``0<=x`` -> (continuity_pt sqrt x).
Intros; Case (total_order R0 x); Intro.
Apply (sqrt_continuity_pt x H0).
Elim H0; Intro.
Unfold continuity_pt; Unfold continue_in; Unfold limit1_in; Unfold limit_in; Simpl; Unfold R_dist; Intros.
Exists (Rsqr eps); Intros.
Split.
Change ``0<(Rsqr eps)``; Apply Rsqr_pos_lt.
Red; Intro; Rewrite H3 in H2; Elim (Rlt_antirefl ? H2).
Intros; Elim H3; Intros.
Rewrite <- H1; Rewrite sqrt_0; Unfold Rminus; Rewrite Ropp_O; Rewrite Rplus_Or; Rewrite <- H1 in H5; Unfold Rminus in H5; Rewrite Ropp_O in H5; Rewrite Rplus_Or in H5.
Case (case_Rabsolu x0); Intro.
Unfold sqrt; Case (case_Rabsolu x0); Intro.
Rewrite Rabsolu_R0; Apply H2.
Assert H6 := (Rle_sym2 ? ? r0); Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H6 r)).
Rewrite Rabsolu_right.
Apply Rsqr_incrst_0.
Rewrite Rsqr_sqrt.
Rewrite (Rabsolu_right x0 r) in H5; Apply H5.
Apply Rle_sym2; Exact r.
Apply sqrt_positivity; Apply Rle_sym2; Exact r.
Left; Exact H2.
Apply Rle_sym1; Apply sqrt_positivity; Apply Rle_sym2; Exact r.
Elim (Rlt_antirefl ? (Rlt_le_trans ? ? ? H1 H)).
Qed.
