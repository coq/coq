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
Require Ranalysis2.
V7only [Import R_scope.]. Open Local Scope R_scope.

(* Division *)
Theorem derivable_pt_lim_div : (f1,f2:R->R;x,l1,l2:R) (derivable_pt_lim f1 x l1) -> (derivable_pt_lim f2 x l2) -> ~``(f2 x)==0``-> (derivable_pt_lim (div_fct f1 f2) x ``(l1*(f2 x)-l2*(f1 x))/(Rsqr (f2 x))``).
Intros.
Cut (derivable_pt f2 x); [Intro | Unfold derivable_pt; Apply Specif.existT with l2; Exact H0].
Assert H2 := ((continuous_neq_0 ? ? (derivable_continuous_pt ? ? X)) H1).
Elim H2; Clear H2; Intros eps_f2 H2.
Unfold div_fct.
Assert H3 := (derivable_continuous_pt ? ? X).
Unfold continuity_pt in H3; Unfold continue_in in H3; Unfold limit1_in in H3; Unfold limit_in in H3; Unfold dist in H3.
Simpl in H3; Unfold R_dist in H3.
Elim (H3 ``(Rabsolu (f2 x))/2``); [Idtac | Unfold Rdiv; Change ``0 < (Rabsolu (f2 x))*/2``; Apply Rmult_lt_pos; [Apply Rabsolu_pos_lt; Assumption | Apply Rlt_Rinv; Sup0]].
Clear H3; Intros alp_f2 H3.
Cut (x0:R) ``(Rabsolu (x0-x)) < alp_f2`` ->``(Rabsolu ((f2 x0)-(f2 x))) < (Rabsolu (f2 x))/2``.
Intro H4.
Cut (a:R) ``(Rabsolu (a-x)) < alp_f2``->``(Rabsolu (f2 x))/2 < (Rabsolu (f2 a))``.
Intro H5.
Cut (a:R) ``(Rabsolu (a)) < (Rmin eps_f2 alp_f2)`` -> ``/(Rabsolu (f2 (x+a))) < 2/(Rabsolu (f2 x))``.
Intro Maj.
Unfold derivable_pt_lim; Intros.
Elim (H ``(Rabsolu ((eps*(f2 x))/8))``); [Idtac | Unfold Rdiv; Change ``0 < (Rabsolu (eps*(f2 x)*/8))``; Apply Rabsolu_pos_lt; Repeat Apply prod_neq_R0; [Red; Intro H7; Rewrite H7 in H6; Elim (Rlt_antirefl ? H6) | Assumption | Apply Rinv_neq_R0; DiscrR]].
Intros alp_f1d H7.
Case (Req_EM (f1 x) R0); Intro.
Case (Req_EM l1 R0); Intro.
(***********************************)
(*              Cas n° 1           *)
(*           (f1 x)=0  l1 =0       *)
(***********************************)
Cut ``0 < (Rmin eps_f2 (Rmin alp_f2 alp_f1d))``; [Intro | Repeat Apply Rmin_pos; [Apply (cond_pos eps_f2) | Elim H3; Intros; Assumption | Apply (cond_pos alp_f1d)]].
Exists (mkposreal (Rmin eps_f2 (Rmin alp_f2 alp_f1d)) H10).
Simpl; Intros.
Assert H13 := (Rlt_le_trans ? ? ? H12 (Rmin_r ? ?)).
Assert H14 := (Rlt_le_trans ? ? ? H12 (Rmin_l ? ?)).
Assert H15 := (Rlt_le_trans ? ? ? H13 (Rmin_r ? ?)).
Assert H16 := (Rlt_le_trans ? ? ? H13 (Rmin_l ? ?)).
Assert H17 := (H7 ? H11 H15).
Rewrite formule; [Idtac | Assumption | Assumption | Apply H2; Apply H14].
Apply Rle_lt_trans with ``(Rabsolu (/(f2 (x+h))*(((f1 (x+h))-(f1 x))/h-l1))) + (Rabsolu (l1/((f2 x)*(f2 (x+h)))*((f2 x)-(f2 (x+h))))) + (Rabsolu ((f1 x)/((f2 x)*(f2 (x+h)))*(((f2 (x+h))-(f2 x))/h-l2))) + (Rabsolu ((l2*(f1 x))/((Rsqr (f2 x))*(f2 (x+h)))*((f2 (x+h))-(f2 x))))``.
Unfold Rminus.
Rewrite <- (Rabsolu_Ropp ``(f1 x)/((f2 x)*(f2 (x+h)))*(((f2 (x+h))+ -(f2 x))/h+ -l2)``).
Apply Rabsolu_4.
Repeat Rewrite Rabsolu_mult.
Apply Rlt_le_trans with ``eps/4+eps/4+eps/4+eps/4``.
Cut ``(Rabsolu (/(f2 (x+h))))*(Rabsolu (((f1 (x+h))-(f1 x))/h-l1)) < eps/4``.
Cut ``(Rabsolu (l1/((f2 x)*(f2 (x+h)))))*(Rabsolu ((f2 x)-(f2 (x+h)))) < eps/4``.
Cut ``(Rabsolu ((f1 x)/((f2 x)*(f2 (x+h)))))*(Rabsolu (((f2 (x+h))-(f2 x))/h-l2)) < eps/4``.
Cut ``(Rabsolu ((l2*(f1 x))/((Rsqr (f2 x))*(f2 (x+h)))))*(Rabsolu ((f2 (x+h))-(f2 x))) < eps/4``.
Intros.
Apply Rlt_4; Assumption.
Rewrite H8.
Unfold Rdiv; Repeat Rewrite Rmult_Or Orelse Rewrite Rmult_Ol.
Rewrite Rabsolu_R0; Rewrite Rmult_Ol.
Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Sup].
Rewrite H8.
Unfold Rdiv; Repeat Rewrite Rmult_Or Orelse Rewrite Rmult_Ol.
Rewrite Rabsolu_R0; Rewrite Rmult_Ol.
Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Sup].
Rewrite H9.
Unfold Rdiv; Repeat Rewrite Rmult_Or Orelse Rewrite Rmult_Ol.
Rewrite Rabsolu_R0; Rewrite Rmult_Ol.
Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Sup].
Rewrite <- Rabsolu_mult.
Apply (maj_term1 x h eps l1 alp_f2 eps_f2 alp_f1d f1 f2); Try Assumption Orelse Apply H2.
Apply H14.
Apply Rmin_2; Assumption.
Right; Symmetry; Apply quadruple_var.
(***********************************)
(*              Cas n° 2           *)
(*           (f1 x)=0  l1<>0       *)
(***********************************)
Assert H10 := (derivable_continuous_pt ? ? X).
Unfold continuity_pt in H10.
Unfold continue_in in H10.
Unfold limit1_in in H10.
Unfold limit_in in H10.
Unfold dist in H10.
Simpl in H10.
Unfold R_dist in H10.
Elim (H10 ``(Rabsolu (eps*(Rsqr (f2 x)))/(8*l1))``).
Clear H10; Intros alp_f2t2 H10.
Cut (a:R) ``(Rabsolu a) < alp_f2t2`` -> ``(Rabsolu ((f2 (x+a)) - (f2 x))) < (Rabsolu ((eps*(Rsqr (f2 x)))/(8*l1)))``.
Intro H11.
Cut ``0 < (Rmin (Rmin eps_f2 alp_f1d) (Rmin alp_f2 alp_f2t2))``.
Intro.
Exists (mkposreal (Rmin (Rmin eps_f2 alp_f1d) (Rmin alp_f2 alp_f2t2)) H12).
Simpl.
Intros.
Assert H15 := (Rlt_le_trans ? ? ? H14 (Rmin_r ? ?)).
Assert H16 := (Rlt_le_trans ? ? ? H14 (Rmin_l ? ?)).
Assert H17 := (Rlt_le_trans ? ? ? H15 (Rmin_l ? ?)).
Assert H18 := (Rlt_le_trans ? ? ? H15 (Rmin_r ? ?)).
Assert H19 := (Rlt_le_trans ? ? ? H16 (Rmin_l ? ?)).
Assert H20 := (Rlt_le_trans ? ? ? H16 (Rmin_r ? ?)).
Clear H14 H15 H16.
Rewrite formule; Try Assumption.
Apply Rle_lt_trans with ``(Rabsolu (/(f2 (x+h))*(((f1 (x+h))-(f1 x))/h-l1))) + (Rabsolu (l1/((f2 x)*(f2 (x+h)))*((f2 x)-(f2 (x+h))))) + (Rabsolu ((f1 x)/((f2 x)*(f2 (x+h)))*(((f2 (x+h))-(f2 x))/h-l2))) + (Rabsolu ((l2*(f1 x))/((Rsqr (f2 x))*(f2 (x+h)))*((f2 (x+h))-(f2 x))))``.
Unfold Rminus.
Rewrite <- (Rabsolu_Ropp ``(f1 x)/((f2 x)*(f2 (x+h)))*(((f2 (x+h))+ -(f2 x))/h+ -l2)``).
Apply Rabsolu_4.
Repeat Rewrite Rabsolu_mult.
Apply Rlt_le_trans with ``eps/4+eps/4+eps/4+eps/4``.
Cut ``(Rabsolu (/(f2 (x+h))))*(Rabsolu (((f1 (x+h))-(f1 x))/h-l1)) < eps/4``.
Cut ``(Rabsolu (l1/((f2 x)*(f2 (x+h)))))*(Rabsolu ((f2 x)-(f2 (x+h)))) < eps/4``.
Cut ``(Rabsolu ((f1 x)/((f2 x)*(f2 (x+h)))))*(Rabsolu (((f2 (x+h))-(f2 x))/h-l2)) < eps/4``.
Cut ``(Rabsolu ((l2*(f1 x))/((Rsqr (f2 x))*(f2 (x+h)))))*(Rabsolu ((f2 (x+h))-(f2 x))) < eps/4``.
Intros.
Apply Rlt_4; Assumption.
Rewrite H8.
Unfold Rdiv; Repeat Rewrite Rmult_Or Orelse Rewrite Rmult_Ol.
Rewrite Rabsolu_R0; Rewrite Rmult_Ol.
Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Sup].
Rewrite H8.
Unfold Rdiv; Repeat Rewrite Rmult_Or Orelse Rewrite Rmult_Ol.
Rewrite Rabsolu_R0; Rewrite Rmult_Ol.
Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Sup].
Rewrite <- Rabsolu_mult.
Apply (maj_term2 x h eps l1 alp_f2 alp_f2t2 eps_f2 f2); Try Assumption.
Apply H2; Assumption.
Apply Rmin_2; Assumption.
Rewrite <- Rabsolu_mult.
Apply (maj_term1 x h eps l1 alp_f2 eps_f2 alp_f1d f1 f2); Try Assumption.
Apply H2; Assumption.
Apply Rmin_2; Assumption.
Right; Symmetry; Apply quadruple_var.
Apply H2; Assumption.
Repeat Apply Rmin_pos.
Apply (cond_pos eps_f2).
Apply (cond_pos alp_f1d).
Elim H3; Intros; Assumption.
Elim H10; Intros; Assumption.
Intros.
Elim H10; Intros.
Case (Req_EM a R0); Intro.
Rewrite H14; Rewrite Rplus_Or.
Unfold Rminus; Rewrite Rplus_Ropp_r.
Rewrite Rabsolu_R0.
Apply Rabsolu_pos_lt.
Unfold Rdiv Rsqr; Repeat Rewrite Rmult_assoc.
Repeat Apply prod_neq_R0; Try Assumption.
Red; Intro; Rewrite H15 in H6; Elim (Rlt_antirefl ? H6).
Apply Rinv_neq_R0; Repeat Apply prod_neq_R0; DiscrR Orelse Assumption.
Apply H13.
Split.
Apply D_x_no_cond; Assumption.
Replace ``x+a-x`` with a; [Assumption | Ring].
Change ``0<(Rabsolu ((eps*(Rsqr (f2 x)))/(8*l1)))``.
Apply Rabsolu_pos_lt; Unfold Rdiv Rsqr; Repeat Rewrite Rmult_assoc; Repeat Apply prod_neq_R0.
Red; Intro; Rewrite H11 in H6; Elim (Rlt_antirefl ? H6).
Assumption. 
Assumption.
Apply Rinv_neq_R0; Repeat Apply prod_neq_R0; [DiscrR | DiscrR | DiscrR | Assumption].
(***********************************)
(*              Cas n° 3           *)
(*     (f1 x)<>0  l1=0  l2=0       *)
(***********************************)
Case (Req_EM l1 R0); Intro.
Case (Req_EM l2 R0); Intro.
Elim (H0 ``(Rabsolu ((Rsqr (f2 x))*eps)/(8*(f1 x)))``); [Idtac | Apply Rabsolu_pos_lt; Unfold Rdiv Rsqr; Repeat Rewrite Rmult_assoc; Repeat Apply prod_neq_R0; [Assumption | Assumption | Red; Intro; Rewrite H11 in H6; Elim (Rlt_antirefl ? H6) | Apply Rinv_neq_R0; Repeat Apply prod_neq_R0; DiscrR Orelse Assumption]].
Intros alp_f2d H12.
Cut ``0 < (Rmin (Rmin eps_f2 alp_f2) (Rmin alp_f1d alp_f2d))``.
Intro.
Exists (mkposreal (Rmin (Rmin eps_f2 alp_f2) (Rmin alp_f1d alp_f2d)) H11).
Simpl.
Intros.
Assert H15 := (Rlt_le_trans ? ? ? H14 (Rmin_l ? ?)).
Assert H16 := (Rlt_le_trans ? ? ? H14 (Rmin_r ? ?)).
Assert H17 := (Rlt_le_trans ? ? ? H15 (Rmin_l ? ?)).
Assert H18 := (Rlt_le_trans ? ? ? H15 (Rmin_r ? ?)).
Assert H19 := (Rlt_le_trans ? ? ? H16 (Rmin_l ? ?)).
Assert H20 := (Rlt_le_trans ? ? ? H16 (Rmin_r ? ?)).
Clear H15 H16.
Rewrite formule; Try Assumption.
Apply Rle_lt_trans with ``(Rabsolu (/(f2 (x+h))*(((f1 (x+h))-(f1 x))/h-l1))) + (Rabsolu (l1/((f2 x)*(f2 (x+h)))*((f2 x)-(f2 (x+h))))) + (Rabsolu ((f1 x)/((f2 x)*(f2 (x+h)))*(((f2 (x+h))-(f2 x))/h-l2))) + (Rabsolu ((l2*(f1 x))/((Rsqr (f2 x))*(f2 (x+h)))*((f2 (x+h))-(f2 x))))``.
Unfold Rminus.
Rewrite <- (Rabsolu_Ropp ``(f1 x)/((f2 x)*(f2 (x+h)))*(((f2 (x+h))+ -(f2 x))/h+ -l2)``).
Apply Rabsolu_4.
Repeat Rewrite Rabsolu_mult.
Apply Rlt_le_trans with ``eps/4+eps/4+eps/4+eps/4``.
Cut ``(Rabsolu (/(f2 (x+h))))*(Rabsolu (((f1 (x+h))-(f1 x))/h-l1)) < eps/4``.
Cut ``(Rabsolu (l1/((f2 x)*(f2 (x+h)))))*(Rabsolu ((f2 x)-(f2 (x+h)))) < eps/4``.
Cut ``(Rabsolu ((f1 x)/((f2 x)*(f2 (x+h)))))*(Rabsolu (((f2 (x+h))-(f2 x))/h-l2)) < eps/4``.
Cut ``(Rabsolu ((l2*(f1 x))/((Rsqr (f2 x))*(f2 (x+h)))))*(Rabsolu ((f2 (x+h))-(f2 x))) < eps/4``.
Intros.
Apply Rlt_4; Assumption.
Rewrite H10.
Unfold Rdiv; Repeat Rewrite Rmult_Or Orelse Rewrite Rmult_Ol.
Rewrite Rabsolu_R0; Rewrite Rmult_Ol.
Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Sup].
Rewrite <- Rabsolu_mult.
Apply (maj_term3 x h eps l2 alp_f2 eps_f2 alp_f2d f1 f2); Try Assumption.
Apply H2; Assumption.
Apply Rmin_2; Assumption.
Rewrite H9.
Unfold Rdiv; Repeat Rewrite Rmult_Or Orelse Rewrite Rmult_Ol.
Rewrite Rabsolu_R0; Rewrite Rmult_Ol.
Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Sup].
Rewrite <- Rabsolu_mult.
Apply (maj_term1 x h eps l1 alp_f2 eps_f2 alp_f1d f1 f2); Assumption Orelse Idtac.
Apply H2; Assumption.
Apply Rmin_2; Assumption.
Right; Symmetry; Apply quadruple_var.
Apply H2; Assumption.
Repeat Apply Rmin_pos.
Apply (cond_pos eps_f2).
Elim H3; Intros; Assumption.
Apply (cond_pos alp_f1d).
Apply (cond_pos alp_f2d).
(***********************************)
(*              Cas n° 4           *)
(*    (f1 x)<>0  l1=0  l2<>0       *)
(***********************************)
Elim (H0 ``(Rabsolu ((Rsqr (f2 x))*eps)/(8*(f1 x)))``); [Idtac | Apply Rabsolu_pos_lt; Unfold Rsqr Rdiv; Repeat Rewrite Rinv_Rmult; Repeat Apply prod_neq_R0; Try Assumption Orelse DiscrR].
Intros alp_f2d H11.
Assert H12 := (derivable_continuous_pt ? ? X).
Unfold continuity_pt in H12.
Unfold continue_in in H12.
Unfold limit1_in in H12.
Unfold limit_in in H12.
Unfold dist in H12.
Simpl in H12.
Unfold R_dist in H12.
Elim (H12 ``(Rabsolu (((Rsqr (f2 x))*(f2 x)*eps)/(8*(f1 x)*l2)))``).
Intros alp_f2c H13.
Cut ``0 < (Rmin (Rmin eps_f2 alp_f2) (Rmin alp_f1d (Rmin alp_f2d alp_f2c)))``.
Intro.
Exists (mkposreal (Rmin (Rmin eps_f2 alp_f2) (Rmin alp_f1d (Rmin alp_f2d alp_f2c))) H14).
Simpl; Intros.
Assert H17 := (Rlt_le_trans ? ? ? H16 (Rmin_l ? ?)).
Assert H18 := (Rlt_le_trans ? ? ? H16 (Rmin_r ? ?)).
Assert H19 := (Rlt_le_trans ? ? ? H18 (Rmin_r ? ?)).
Assert H20 := (Rlt_le_trans ? ? ? H19 (Rmin_l ? ?)).
Assert H21 := (Rlt_le_trans ? ? ? H19 (Rmin_r ? ?)).
Assert H22 := (Rlt_le_trans ? ? ? H18 (Rmin_l ? ?)).
Assert H23 := (Rlt_le_trans ? ? ? H17 (Rmin_l ? ?)).
Assert H24 := (Rlt_le_trans ? ? ? H17 (Rmin_r ? ?)).
Clear H16 H17 H18 H19.
Cut (a:R) ``(Rabsolu a) < alp_f2c`` -> ``(Rabsolu ((f2 (x+a))-(f2 x))) < (Rabsolu (((Rsqr (f2 x))*(f2 x)*eps)/(8*(f1 x)*l2)))``.
Intro.
Rewrite formule; Try Assumption.
Apply Rle_lt_trans with ``(Rabsolu (/(f2 (x+h))*(((f1 (x+h))-(f1 x))/h-l1))) + (Rabsolu (l1/((f2 x)*(f2 (x+h)))*((f2 x)-(f2 (x+h))))) + (Rabsolu ((f1 x)/((f2 x)*(f2 (x+h)))*(((f2 (x+h))-(f2 x))/h-l2))) + (Rabsolu ((l2*(f1 x))/((Rsqr (f2 x))*(f2 (x+h)))*((f2 (x+h))-(f2 x))))``.
Unfold Rminus.
Rewrite <- (Rabsolu_Ropp ``(f1 x)/((f2 x)*(f2 (x+h)))*(((f2 (x+h))+ -(f2 x))/h+ -l2)``).
Apply Rabsolu_4.
Repeat Rewrite Rabsolu_mult.
Apply Rlt_le_trans with ``eps/4+eps/4+eps/4+eps/4``.
Cut ``(Rabsolu (/(f2 (x+h))))*(Rabsolu (((f1 (x+h))-(f1 x))/h-l1)) < eps/4``.
Cut ``(Rabsolu (l1/((f2 x)*(f2 (x+h)))))*(Rabsolu ((f2 x)-(f2 (x+h)))) < eps/4``.
Cut ``(Rabsolu ((f1 x)/((f2 x)*(f2 (x+h)))))*(Rabsolu (((f2 (x+h))-(f2 x))/h-l2)) < eps/4``.
Cut ``(Rabsolu ((l2*(f1 x))/((Rsqr (f2 x))*(f2 (x+h)))))*(Rabsolu ((f2 (x+h))-(f2 x))) < eps/4``.
Intros.
Apply Rlt_4; Assumption.
Rewrite <- Rabsolu_mult.
Apply (maj_term4 x h eps l2 alp_f2 alp_f2c eps_f2 f1 f2); Try Assumption.
Apply H2; Assumption.
Apply Rmin_2; Assumption.
Rewrite <- Rabsolu_mult.
Apply (maj_term3 x h eps l2 alp_f2 eps_f2 alp_f2d f1 f2); Try Assumption.
Apply H2; Assumption.
Apply Rmin_2; Assumption.
Rewrite H9.
Unfold Rdiv; Repeat Rewrite Rmult_Or Orelse Rewrite Rmult_Ol.
Rewrite Rabsolu_R0; Rewrite Rmult_Ol.
Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Sup].
Rewrite <- Rabsolu_mult.
Apply (maj_term1 x h eps l1 alp_f2 eps_f2 alp_f1d f1 f2); Try Assumption.
Apply H2; Assumption.
Apply Rmin_2; Assumption.
Right; Symmetry; Apply quadruple_var.
Apply H2; Assumption.
Intros.
Case (Req_EM a R0); Intro.
Rewrite H17; Rewrite Rplus_Or.
Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0.
Apply Rabsolu_pos_lt.
Unfold Rdiv Rsqr.
Repeat Rewrite Rinv_Rmult; Try Assumption.
Repeat Apply prod_neq_R0; Try Assumption.
Red; Intro H18; Rewrite H18 in H6; Elim (Rlt_antirefl ? H6). 
Apply Rinv_neq_R0; DiscrR.
Apply Rinv_neq_R0; DiscrR.
Apply Rinv_neq_R0; DiscrR.
Apply Rinv_neq_R0; Assumption.
Apply Rinv_neq_R0; Assumption.
DiscrR.
DiscrR.
DiscrR.
DiscrR.
DiscrR.
Apply prod_neq_R0; [DiscrR | Assumption].
Elim H13; Intros.
Apply H19.
Split.
Apply D_x_no_cond; Assumption.
Replace ``x+a-x`` with a; [Assumption | Ring].
Repeat Apply Rmin_pos.
Apply (cond_pos eps_f2).
Elim H3; Intros; Assumption.
Apply (cond_pos alp_f1d).
Apply (cond_pos alp_f2d).
Elim H13; Intros; Assumption.
Change ``0 < (Rabsolu (((Rsqr (f2 x))*(f2 x)*eps)/(8*(f1 x)*l2)))``.
Apply Rabsolu_pos_lt.
Unfold Rsqr Rdiv.
Repeat Rewrite Rinv_Rmult; Try Assumption Orelse DiscrR.
Repeat Apply prod_neq_R0; Try Assumption.
Red; Intro H13; Rewrite H13 in H6; Elim (Rlt_antirefl ? H6). 
Apply Rinv_neq_R0; DiscrR.
Apply Rinv_neq_R0; DiscrR.
Apply Rinv_neq_R0; DiscrR.
Apply Rinv_neq_R0; Assumption.
Apply Rinv_neq_R0; Assumption.
Apply prod_neq_R0; [DiscrR | Assumption].
Red; Intro H11; Rewrite H11 in H6; Elim (Rlt_antirefl ? H6). 
Apply Rinv_neq_R0; DiscrR.
Apply Rinv_neq_R0; DiscrR.
Apply Rinv_neq_R0; DiscrR.
Apply Rinv_neq_R0; Assumption.
(***********************************)
(*              Cas n° 5           *)
(*    (f1 x)<>0  l1<>0  l2=0       *)
(***********************************)
Case (Req_EM l2 R0); Intro.
Assert H11 := (derivable_continuous_pt ? ? X).
Unfold continuity_pt in H11.
Unfold continue_in in H11.
Unfold limit1_in in H11.
Unfold limit_in in H11.
Unfold dist in H11.
Simpl in H11.
Unfold R_dist in H11.
Elim (H11 ``(Rabsolu (eps*(Rsqr (f2 x)))/(8*l1))``).
Clear H11; Intros alp_f2t2 H11.
Elim (H0 ``(Rabsolu ((Rsqr (f2 x))*eps)/(8*(f1 x)))``).
Intros alp_f2d H12.
Cut ``0 < (Rmin (Rmin eps_f2 alp_f2) (Rmin alp_f1d (Rmin alp_f2d alp_f2t2)))``.
Intro.
Exists (mkposreal (Rmin (Rmin eps_f2 alp_f2) (Rmin alp_f1d (Rmin alp_f2d alp_f2t2))) H13).
Simpl.
Intros.
Cut (a:R) ``(Rabsolu a)<alp_f2t2`` -> ``(Rabsolu ((f2 (x+a))-(f2 x)))<(Rabsolu ((eps*(Rsqr (f2 x)))/(8*l1)))``.
Intro.
Assert H17 := (Rlt_le_trans ? ? ? H15 (Rmin_l ? ?)).
Assert H18 := (Rlt_le_trans ? ? ? H15 (Rmin_r ? ?)).
Assert H19 := (Rlt_le_trans ? ? ? H17 (Rmin_r ? ?)).
Assert H20 := (Rlt_le_trans ? ? ? H17 (Rmin_l ? ?)).
Assert H21 := (Rlt_le_trans ? ? ? H18 (Rmin_r ? ?)).
Assert H22 := (Rlt_le_trans ? ? ? H18 (Rmin_l ? ?)).
Assert H23 := (Rlt_le_trans ? ? ? H21 (Rmin_l ? ?)).
Assert H24 := (Rlt_le_trans ? ? ? H21 (Rmin_r ? ?)).
Clear H15 H17 H18 H21.
Rewrite formule; Try Assumption.
Apply Rle_lt_trans with ``(Rabsolu (/(f2 (x+h))*(((f1 (x+h))-(f1 x))/h-l1))) + (Rabsolu (l1/((f2 x)*(f2 (x+h)))*((f2 x)-(f2 (x+h))))) + (Rabsolu ((f1 x)/((f2 x)*(f2 (x+h)))*(((f2 (x+h))-(f2 x))/h-l2))) + (Rabsolu ((l2*(f1 x))/((Rsqr (f2 x))*(f2 (x+h)))*((f2 (x+h))-(f2 x))))``.
Unfold Rminus.
Rewrite <- (Rabsolu_Ropp ``(f1 x)/((f2 x)*(f2 (x+h)))*(((f2 (x+h))+ -(f2 x))/h+ -l2)``).
Apply Rabsolu_4.
Repeat Rewrite Rabsolu_mult.
Apply Rlt_le_trans with ``eps/4+eps/4+eps/4+eps/4``.
Cut ``(Rabsolu (/(f2 (x+h))))*(Rabsolu (((f1 (x+h))-(f1 x))/h-l1)) < eps/4``.
Cut ``(Rabsolu (l1/((f2 x)*(f2 (x+h)))))*(Rabsolu ((f2 x)-(f2 (x+h)))) < eps/4``.
Cut ``(Rabsolu ((f1 x)/((f2 x)*(f2 (x+h)))))*(Rabsolu (((f2 (x+h))-(f2 x))/h-l2)) < eps/4``.
Cut ``(Rabsolu ((l2*(f1 x))/((Rsqr (f2 x))*(f2 (x+h)))))*(Rabsolu ((f2 (x+h))-(f2 x))) < eps/4``.
Intros.
Apply Rlt_4; Assumption.
Rewrite H10.
Unfold Rdiv; Repeat Rewrite Rmult_Or Orelse Rewrite Rmult_Ol.
Rewrite Rabsolu_R0; Rewrite Rmult_Ol.
Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Sup].
Rewrite <- Rabsolu_mult.
Apply (maj_term3 x h eps l2 alp_f2 eps_f2 alp_f2d f1 f2); Try Assumption.
Apply H2; Assumption.
Apply Rmin_2; Assumption.
Rewrite <- Rabsolu_mult.
Apply (maj_term2 x h eps l1 alp_f2 alp_f2t2 eps_f2 f2); Try Assumption.
Apply H2; Assumption.
Apply Rmin_2; Assumption.
Rewrite <- Rabsolu_mult.
Apply (maj_term1 x h eps l1 alp_f2 eps_f2 alp_f1d f1 f2); Try Assumption.
Apply H2; Assumption.
Apply Rmin_2; Assumption.
Right; Symmetry; Apply quadruple_var.
Apply H2; Assumption.
Intros.
Case (Req_EM a R0); Intro.
Rewrite H17; Rewrite Rplus_Or; Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0.
Apply Rabsolu_pos_lt.
Unfold Rdiv; Rewrite Rinv_Rmult; Try DiscrR Orelse Assumption.
Unfold Rsqr.
Repeat Apply prod_neq_R0; Assumption Orelse (Apply Rinv_neq_R0; Assumption) Orelse (Apply Rinv_neq_R0; DiscrR) Orelse (Red; Intro H18; Rewrite H18 in H6; Elim (Rlt_antirefl ? H6)).
Elim H11; Intros.
Apply H19.
Split.
Apply D_x_no_cond; Assumption.
Replace ``x+a-x`` with a; [Assumption | Ring].
Repeat Apply Rmin_pos.
Apply (cond_pos eps_f2).
Elim H3; Intros; Assumption.
Apply (cond_pos alp_f1d). 
Apply (cond_pos alp_f2d).
Elim H11; Intros; Assumption.
Apply Rabsolu_pos_lt.
Unfold Rdiv Rsqr; Rewrite Rinv_Rmult; Try DiscrR Orelse Assumption.
Repeat Apply prod_neq_R0; Assumption Orelse (Apply Rinv_neq_R0; Assumption) Orelse (Apply Rinv_neq_R0; DiscrR) Orelse (Red; Intro H12; Rewrite H12 in H6; Elim (Rlt_antirefl ? H6)).
Change ``0 < (Rabsolu ((eps*(Rsqr (f2 x)))/(8*l1)))``.
Apply Rabsolu_pos_lt.
Unfold Rdiv Rsqr; Rewrite Rinv_Rmult; Try DiscrR Orelse Assumption.
Repeat Apply prod_neq_R0; Assumption Orelse (Apply Rinv_neq_R0; Assumption) Orelse (Apply Rinv_neq_R0; DiscrR) Orelse (Red; Intro H12; Rewrite H12 in H6; Elim (Rlt_antirefl ? H6)).
(***********************************)
(*              Cas n° 6           *)
(*    (f1 x)<>0  l1<>0  l2<>0      *)
(***********************************)
Elim (H0 ``(Rabsolu ((Rsqr (f2 x))*eps)/(8*(f1 x)))``).
Intros alp_f2d H11.
Assert H12 := (derivable_continuous_pt ? ? X).
Unfold continuity_pt in H12.
Unfold continue_in in H12.
Unfold limit1_in in H12.
Unfold limit_in in H12.
Unfold dist in H12.
Simpl in H12.
Unfold R_dist in H12.
Elim (H12 ``(Rabsolu (((Rsqr (f2 x))*(f2 x)*eps)/(8*(f1 x)*l2)))``).
Intros alp_f2c H13.
Elim (H12 ``(Rabsolu (eps*(Rsqr (f2 x)))/(8*l1))``).
Intros alp_f2t2 H14.
Cut ``0 < (Rmin (Rmin (Rmin eps_f2 alp_f2) (Rmin alp_f1d alp_f2d)) (Rmin alp_f2c alp_f2t2))``.
Intro.
Exists (mkposreal (Rmin (Rmin (Rmin eps_f2 alp_f2) (Rmin alp_f1d alp_f2d)) (Rmin alp_f2c alp_f2t2)) H15).
Simpl.
Intros.
Assert H18 := (Rlt_le_trans ? ? ? H17 (Rmin_l ? ?)).
Assert H19 := (Rlt_le_trans ? ? ? H17 (Rmin_r ? ?)).
Assert H20 := (Rlt_le_trans ? ? ? H18 (Rmin_l ? ?)).
Assert H21 := (Rlt_le_trans ? ? ? H18 (Rmin_r ? ?)).
Assert H22 := (Rlt_le_trans ? ? ? H19 (Rmin_l ? ?)).
Assert H23 := (Rlt_le_trans ? ? ? H19 (Rmin_r ? ?)).
Assert H24 := (Rlt_le_trans ? ? ? H20 (Rmin_l ? ?)).
Assert H25 := (Rlt_le_trans ? ? ? H20 (Rmin_r ? ?)).
Assert H26 := (Rlt_le_trans ? ? ? H21 (Rmin_l ? ?)).
Assert H27 := (Rlt_le_trans ? ? ? H21 (Rmin_r ? ?)).
Clear H17 H18 H19 H20 H21.
Cut (a:R) ``(Rabsolu a) < alp_f2t2`` -> ``(Rabsolu ((f2 (x+a))-(f2 x))) < (Rabsolu ((eps*(Rsqr (f2 x)))/(8*l1)))``.
Cut (a:R) ``(Rabsolu a) < alp_f2c`` -> ``(Rabsolu ((f2 (x+a))-(f2 x))) < (Rabsolu (((Rsqr (f2 x))*(f2 x)*eps)/(8*(f1 x)*l2)))``.
Intros.
Rewrite formule; Try Assumption.
Apply Rle_lt_trans with ``(Rabsolu (/(f2 (x+h))*(((f1 (x+h))-(f1 x))/h-l1))) + (Rabsolu (l1/((f2 x)*(f2 (x+h)))*((f2 x)-(f2 (x+h))))) + (Rabsolu ((f1 x)/((f2 x)*(f2 (x+h)))*(((f2 (x+h))-(f2 x))/h-l2))) + (Rabsolu ((l2*(f1 x))/((Rsqr (f2 x))*(f2 (x+h)))*((f2 (x+h))-(f2 x))))``.
Unfold Rminus.
Rewrite <- (Rabsolu_Ropp ``(f1 x)/((f2 x)*(f2 (x+h)))*(((f2 (x+h))+ -(f2 x))/h+ -l2)``).
Apply Rabsolu_4.
Repeat Rewrite Rabsolu_mult.
Apply Rlt_le_trans with ``eps/4+eps/4+eps/4+eps/4``.
Cut ``(Rabsolu (/(f2 (x+h))))*(Rabsolu (((f1 (x+h))-(f1 x))/h-l1)) < eps/4``.
Cut ``(Rabsolu (l1/((f2 x)*(f2 (x+h)))))*(Rabsolu ((f2 x)-(f2 (x+h)))) < eps/4``.
Cut ``(Rabsolu ((f1 x)/((f2 x)*(f2 (x+h)))))*(Rabsolu (((f2 (x+h))-(f2 x))/h-l2)) < eps/4``.
Cut ``(Rabsolu ((l2*(f1 x))/((Rsqr (f2 x))*(f2 (x+h)))))*(Rabsolu ((f2 (x+h))-(f2 x))) < eps/4``.
Intros.
Apply Rlt_4; Assumption.
Rewrite <- Rabsolu_mult.
Apply (maj_term4 x h eps l2 alp_f2 alp_f2c eps_f2 f1 f2); Try Assumption.
Apply H2; Assumption.
Apply Rmin_2; Assumption.
Rewrite <- Rabsolu_mult.
Apply (maj_term3 x h eps l2 alp_f2 eps_f2 alp_f2d f1 f2); Try Assumption.
Apply H2; Assumption.
Apply Rmin_2; Assumption.
Rewrite <- Rabsolu_mult.
Apply (maj_term2 x h eps l1 alp_f2 alp_f2t2 eps_f2 f2); Try Assumption.
Apply H2; Assumption.
Apply Rmin_2; Assumption.
Rewrite <- Rabsolu_mult.
Apply (maj_term1 x h eps l1 alp_f2 eps_f2 alp_f1d f1 f2); Try Assumption.
Apply H2; Assumption.
Apply Rmin_2; Assumption.
Right; Symmetry; Apply quadruple_var.
Apply H2; Assumption.
Intros.
Case (Req_EM a R0); Intro.
Rewrite H18; Rewrite Rplus_Or; Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Apply Rabsolu_pos_lt.
Unfold Rdiv Rsqr; Rewrite Rinv_Rmult.
Repeat Apply prod_neq_R0; Assumption Orelse (Apply Rinv_neq_R0; Assumption) Orelse (Apply Rinv_neq_R0; DiscrR) Orelse (Red; Intro H28; Rewrite H28 in H6; Elim (Rlt_antirefl ? H6)).
Apply prod_neq_R0; [DiscrR | Assumption].
Apply prod_neq_R0; [DiscrR | Assumption].
Assumption.
Elim H13; Intros.
Apply H20.
Split.
Apply D_x_no_cond; Assumption.
Replace ``x+a-x`` with a; [Assumption | Ring].
Intros.
Case (Req_EM a R0); Intro.
Rewrite H18; Rewrite Rplus_Or; Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Apply Rabsolu_pos_lt.
Unfold Rdiv Rsqr; Rewrite Rinv_Rmult.
Repeat Apply prod_neq_R0; Assumption Orelse (Apply Rinv_neq_R0; Assumption) Orelse (Apply Rinv_neq_R0; DiscrR) Orelse (Red; Intro H28; Rewrite H28 in H6; Elim (Rlt_antirefl ? H6)).
DiscrR.
Assumption.
Elim H14; Intros.
Apply H20.
Split.
Unfold D_x no_cond; Split.
Trivial.
Apply Rminus_not_eq_right.
Replace ``x+a-x`` with a; [Assumption | Ring].
Replace ``x+a-x`` with a; [Assumption | Ring].
Repeat Apply Rmin_pos.
Apply (cond_pos eps_f2).
Elim H3; Intros; Assumption.
Apply (cond_pos alp_f1d).
Apply (cond_pos alp_f2d).
Elim H13; Intros; Assumption.
Elim H14; Intros; Assumption.
Change ``0 < (Rabsolu ((eps*(Rsqr (f2 x)))/(8*l1)))``; Apply Rabsolu_pos_lt.
Unfold Rdiv Rsqr; Rewrite Rinv_Rmult; Try DiscrR Orelse Assumption.
Repeat Apply prod_neq_R0; Assumption Orelse (Apply Rinv_neq_R0; Assumption) Orelse (Apply Rinv_neq_R0; DiscrR) Orelse (Red; Intro H14; Rewrite H14 in H6; Elim (Rlt_antirefl ? H6)).
Change ``0 < (Rabsolu (((Rsqr (f2 x))*(f2 x)*eps)/(8*(f1 x)*l2)))``; Apply Rabsolu_pos_lt.
Unfold Rdiv Rsqr; Rewrite Rinv_Rmult.
Repeat Apply prod_neq_R0; Assumption Orelse (Apply Rinv_neq_R0; Assumption) Orelse (Apply Rinv_neq_R0; DiscrR) Orelse (Red; Intro H13; Rewrite H13 in H6; Elim (Rlt_antirefl ? H6)).
Apply prod_neq_R0; [DiscrR | Assumption].
Apply prod_neq_R0; [DiscrR | Assumption].
Assumption.
Apply Rabsolu_pos_lt.
Unfold Rdiv Rsqr; Rewrite Rinv_Rmult; [Idtac | DiscrR | Assumption].
Repeat Apply prod_neq_R0; Assumption Orelse (Apply Rinv_neq_R0; Assumption) Orelse (Apply Rinv_neq_R0; DiscrR) Orelse (Red; Intro H11; Rewrite H11 in H6; Elim (Rlt_antirefl ? H6)).
Intros.
Unfold Rdiv.
Apply Rlt_monotony_contra with ``(Rabsolu (f2 (x+a)))``.
Apply Rabsolu_pos_lt; Apply H2.
Apply Rlt_le_trans with (Rmin eps_f2 alp_f2).
Assumption.
Apply Rmin_l.
Rewrite <- Rinv_r_sym.
Apply Rlt_monotony_contra with (Rabsolu (f2 x)).
Apply Rabsolu_pos_lt; Assumption.
Rewrite Rmult_1r.
Rewrite (Rmult_sym (Rabsolu (f2 x))).
Repeat Rewrite Rmult_assoc.
Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r.
Apply Rlt_monotony_contra with ``/2``.
Apply Rlt_Rinv; Sup0.
Repeat Rewrite (Rmult_sym ``/2``).
Repeat Rewrite Rmult_assoc.
Rewrite <- Rinv_r_sym.
Rewrite Rmult_1r.
Unfold Rdiv in H5; Apply H5.
Replace ``x+a-x`` with a.
Assert H7 := (Rlt_le_trans ? ? ? H6 (Rmin_r ? ?)); Assumption.
Ring.
DiscrR.
Apply Rabsolu_no_R0; Assumption.
Apply Rabsolu_no_R0; Apply H2.
Assert H7 := (Rlt_le_trans ? ? ? H6 (Rmin_l ? ?)); Assumption.
Intros.
Assert H6 := (H4 a H5).
Rewrite <- (Rabsolu_Ropp ``(f2 a)-(f2 x)``) in H6.
Rewrite Ropp_distr2 in H6.
Assert H7 := (Rle_lt_trans ? ? ? (Rabsolu_triang_inv ? ?) H6).
Apply Rlt_anti_compatibility with ``-(Rabsolu (f2 a)) + (Rabsolu (f2 x))/2``.
Rewrite Rplus_assoc.
Rewrite <- double_var.
Do 2 Rewrite (Rplus_sym ``-(Rabsolu (f2 a))``).
Rewrite Rplus_assoc; Rewrite Rplus_Ropp_l; Rewrite Rplus_Or.
Unfold Rminus in H7; Assumption.
Intros.
Case (Req_EM x x0); Intro.
Rewrite <- H5; Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Unfold Rdiv; Apply Rmult_lt_pos; [Apply Rabsolu_pos_lt; Assumption | Apply Rlt_Rinv; Sup0].
Elim H3; Intros.
Apply H7.
Split.
Unfold D_x no_cond; Split.
Trivial.
Assumption.
Assumption.
Qed.

Lemma derivable_pt_div : (f1,f2:R->R;x:R) (derivable_pt f1 x) -> (derivable_pt f2 x) -> ``(f2 x)<>0`` -> (derivable_pt (div_fct f1 f2) x).
Unfold derivable_pt.
Intros.
Elim X; Intros.
Elim X0; Intros.
Apply Specif.existT with ``(x0*(f2 x)-x1*(f1 x))/(Rsqr (f2 x))``.
Apply derivable_pt_lim_div; Assumption.
Qed.

Lemma derivable_div : (f1,f2:R->R) (derivable f1) -> (derivable f2) -> ((x:R)``(f2 x)<>0``) -> (derivable (div_fct f1 f2)).
Unfold derivable; Intros.
Apply (derivable_pt_div ? ? ? (X x) (X0 x) (H x)).
Qed.

Lemma derive_pt_div : (f1,f2:R->R;x:R;pr1:(derivable_pt f1 x);pr2:(derivable_pt f2 x);na:``(f2 x)<>0``) ``(derive_pt (div_fct f1 f2) x (derivable_pt_div ? ? ? pr1 pr2 na)) == ((derive_pt f1 x pr1)*(f2 x)-(derive_pt f2 x pr2)*(f1 x))/(Rsqr (f2 x))``.
Intros.
Assert H := (derivable_derive f1 x pr1).
Assert H0 := (derivable_derive f2 x pr2).
Assert H1 := (derivable_derive (div_fct f1 f2) x (derivable_pt_div ? ? ? pr1 pr2 na)).
Elim H; Clear H; Intros l1 H.
Elim H0; Clear H0; Intros l2 H0.
Elim H1; Clear H1; Intros l H1.
Rewrite H; Rewrite H0; Apply derive_pt_eq_0.
Assert H3 := (projT2 ? ? pr1).
Unfold derive_pt in H; Rewrite H in H3.
Assert H4 := (projT2 ? ? pr2).
Unfold derive_pt in H0; Rewrite H0 in H4.
Apply derivable_pt_lim_div; Assumption.
Qed.
