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
V7only [Import R_scope.]. Open Local Scope R_scope.

(**********)
Lemma formule : (x,h,l1,l2:R;f1,f2:R->R) ``h<>0`` -> ``(f2 x)<>0`` -> ``(f2 (x+h))<>0`` -> ``((f1 (x+h))/(f2 (x+h))-(f1 x)/(f2 x))/h-(l1*(f2 x)-l2*(f1 x))/(Rsqr (f2 x))`` == ``/(f2 (x+h))*(((f1 (x+h))-(f1 x))/h-l1) + l1/((f2 x)*(f2 (x+h)))*((f2 x)-(f2 (x+h))) - (f1 x)/((f2 x)*(f2 (x+h)))*(((f2 (x+h))-(f2 x))/h-l2) + (l2*(f1 x))/((Rsqr (f2 x))*(f2 (x+h)))*((f2 (x+h))-(f2 x))``.
Intros; Unfold Rdiv Rminus Rsqr.
Repeat Rewrite Rmult_Rplus_distrl; Repeat Rewrite Rmult_Rplus_distr; Repeat Rewrite Rinv_Rmult; Try Assumption.
Replace ``l1*(f2 x)*(/(f2 x)*/(f2 x))`` with ``l1*/(f2 x)*((f2 x)*/(f2 x))``; [Idtac | Ring].
Replace ``l1*(/(f2 x)*/(f2 (x+h)))*(f2 x)`` with ``l1*/(f2 (x+h))*((f2 x)*/(f2 x))``; [Idtac | Ring].
Replace ``l1*(/(f2 x)*/(f2 (x+h)))* -(f2 (x+h))`` with ``-(l1*/(f2 x)*((f2 (x+h))*/(f2 (x+h))))``; [Idtac | Ring].
Replace ``(f1 x)*(/(f2 x)*/(f2 (x+h)))*((f2 (x+h))*/h)`` with ``(f1 x)*/(f2 x)*/h*((f2 (x+h))*/(f2 (x+h)))``; [Idtac | Ring].
Replace ``(f1 x)*(/(f2 x)*/(f2 (x+h)))*( -(f2 x)*/h)`` with ``-((f1 x)*/(f2 (x+h))*/h*((f2 x)*/(f2 x)))``; [Idtac | Ring].
Replace ``(l2*(f1 x)*(/(f2 x)*/(f2 x)*/(f2 (x+h)))*(f2 (x+h)))`` with ``l2*(f1 x)*/(f2 x)*/(f2 x)*((f2 (x+h))*/(f2 (x+h)))``; [Idtac | Ring].
Replace ``l2*(f1 x)*(/(f2 x)*/(f2 x)*/(f2 (x+h)))* -(f2 x)`` with ``-(l2*(f1 x)*/(f2 x)*/(f2 (x+h))*((f2 x)*/(f2 x)))``; [Idtac | Ring].
Repeat Rewrite <- Rinv_r_sym; Try Assumption Orelse Ring.
Apply prod_neq_R0; Assumption.
Qed.

Lemma Rmin_pos : (x,y:R) ``0<x`` -> ``0<y`` -> ``0 < (Rmin x y)``.
Intros; Unfold Rmin.
Case (total_order_Rle x y); Intro; Assumption.
Qed.

Lemma maj_term1 : (x,h,eps,l1,alp_f2:R;eps_f2,alp_f1d:posreal;f1,f2:R->R) ``0 < eps`` -> ``(f2 x)<>0`` -> ``(f2 (x+h))<>0`` -> ((h:R)``h <> 0``->``(Rabsolu h) < alp_f1d``->``(Rabsolu (((f1 (x+h))-(f1 x))/h-l1)) < (Rabsolu ((eps*(f2 x))/8))``) -> ((a:R)``(Rabsolu a) < (Rmin eps_f2 alp_f2)``->``/(Rabsolu (f2 (x+a))) < 2/(Rabsolu (f2 x))``) -> ``h<>0`` -> ``(Rabsolu h)<alp_f1d`` -> ``(Rabsolu h) < (Rmin eps_f2 alp_f2)`` -> ``(Rabsolu (/(f2 (x+h))*(((f1 (x+h))-(f1 x))/h-l1))) < eps/4``.
Intros.
Assert H7 := (H3 h H6).
Assert H8 := (H2 h H4 H5).
Apply Rle_lt_trans with ``2/(Rabsolu (f2 x))*(Rabsolu (((f1 (x+h))-(f1 x))/h-l1))``.
Rewrite Rabsolu_mult.
Apply Rle_monotony_r.
Apply Rabsolu_pos.
Rewrite Rabsolu_Rinv; [Left; Exact H7 | Assumption].
Apply Rlt_le_trans with ``2/(Rabsolu (f2 x))*(Rabsolu ((eps*(f2 x))/8))``.
Apply Rlt_monotony.
Unfold Rdiv; Apply Rmult_lt_pos; [Sup0 | Apply Rlt_Rinv; Apply Rabsolu_pos_lt; Assumption].
Exact H8.
Right; Unfold Rdiv.
Repeat Rewrite Rabsolu_mult.
Rewrite Rabsolu_Rinv; DiscrR.
Replace ``(Rabsolu 8)`` with ``8``.
Replace ``8`` with ``2*4``; [Idtac | Ring].
Rewrite Rinv_Rmult; [Idtac | DiscrR | DiscrR].
Replace ``2*/(Rabsolu (f2 x))*((Rabsolu eps)*(Rabsolu (f2 x))*(/2*/4))`` with ``(Rabsolu eps)*/4*(2*/2)*((Rabsolu (f2 x))*/(Rabsolu (f2 x)))``; [Idtac | Ring].
Replace (Rabsolu eps) with eps.
Repeat Rewrite <- Rinv_r_sym; Try DiscrR Orelse (Apply Rabsolu_no_R0; Assumption).
Ring.
Symmetry; Apply Rabsolu_right; Left; Assumption.
Symmetry; Apply Rabsolu_right; Left; Sup.
Qed.

Lemma maj_term2 : (x,h,eps,l1,alp_f2,alp_f2t2:R;eps_f2:posreal;f2:R->R) ``0 < eps`` -> ``(f2 x)<>0`` -> ``(f2 (x+h))<>0`` -> ((a:R)``(Rabsolu a) < alp_f2t2``->``(Rabsolu ((f2 (x+a))-(f2 x))) < (Rabsolu ((eps*(Rsqr (f2 x)))/(8*l1)))``)-> ((a:R)``(Rabsolu a) < (Rmin eps_f2 alp_f2)``->``/(Rabsolu (f2 (x+a))) < 2/(Rabsolu (f2 x))``) -> ``h<>0`` -> ``(Rabsolu h)<alp_f2t2`` -> ``(Rabsolu h) < (Rmin eps_f2 alp_f2)`` -> ``l1<>0`` -> ``(Rabsolu (l1/((f2 x)*(f2 (x+h)))*((f2 x)-(f2 (x+h))))) < eps/4``.
Intros.
Assert H8 := (H3 h H6).
Assert H9 := (H2 h H5).
Apply Rle_lt_trans with ``(Rabsolu (l1/((f2 x)*(f2 (x+h)))))*(Rabsolu ((eps*(Rsqr (f2 x)))/(8*l1)))``.
Rewrite Rabsolu_mult; Apply Rle_monotony.
Apply Rabsolu_pos.
Rewrite <- (Rabsolu_Ropp ``(f2 x)-(f2 (x+h))``); Rewrite Ropp_distr2.
Left; Apply H9.
Apply Rlt_le_trans with ``(Rabsolu (2*l1/((f2 x)*(f2 x))))*(Rabsolu ((eps*(Rsqr (f2 x)))/(8*l1)))``.
Apply Rlt_monotony_r.
Apply Rabsolu_pos_lt.
Unfold Rdiv; Unfold Rsqr; Repeat Apply prod_neq_R0; Try Assumption Orelse DiscrR.
Red; Intro H10; Rewrite H10 in H; Elim (Rlt_antirefl ? H).
Apply Rinv_neq_R0; Apply prod_neq_R0; Try Assumption Orelse DiscrR.
Unfold Rdiv.
Repeat Rewrite Rinv_Rmult; Try Assumption.
Repeat Rewrite Rabsolu_mult.
Replace ``(Rabsolu 2)`` with ``2``.
Rewrite (Rmult_sym ``2``).
Replace ``(Rabsolu l1)*((Rabsolu (/(f2 x)))*(Rabsolu (/(f2 x))))*2`` with ``(Rabsolu l1)*((Rabsolu (/(f2 x)))*((Rabsolu (/(f2 x)))*2))``; [Idtac | Ring].
Repeat Apply Rlt_monotony.
Apply Rabsolu_pos_lt; Assumption.
Apply Rabsolu_pos_lt; Apply Rinv_neq_R0; Assumption.
Repeat Rewrite Rabsolu_Rinv; Try Assumption.
Rewrite <- (Rmult_sym ``2``).
Unfold Rdiv in H8; Exact H8.
Symmetry; Apply Rabsolu_right; Left; Sup0.
Right.
Unfold Rsqr Rdiv.
Do 1 Rewrite Rinv_Rmult; Try Assumption Orelse DiscrR.
Do 1 Rewrite Rinv_Rmult; Try Assumption Orelse DiscrR.
Repeat Rewrite Rabsolu_mult.
Repeat Rewrite Rabsolu_Rinv; Try Assumption Orelse DiscrR.
Replace (Rabsolu eps) with eps.
Replace ``(Rabsolu (8))`` with ``8``.
Replace ``(Rabsolu 2)`` with ``2``.
Replace ``8`` with ``4*2``; [Idtac | Ring].
Rewrite Rinv_Rmult; DiscrR.
Replace ``2*((Rabsolu l1)*(/(Rabsolu (f2 x))*/(Rabsolu (f2 x))))*(eps*((Rabsolu (f2 x))*(Rabsolu (f2 x)))*(/4*/2*/(Rabsolu l1)))`` with ``eps*/4*((Rabsolu l1)*/(Rabsolu l1))*((Rabsolu (f2 x))*/(Rabsolu (f2 x)))*((Rabsolu (f2 x))*/(Rabsolu (f2 x)))*(2*/2)``; [Idtac | Ring].
Repeat Rewrite <- Rinv_r_sym; Try (Apply Rabsolu_no_R0; Assumption) Orelse DiscrR.
Ring.
Symmetry; Apply Rabsolu_right; Left; Sup0.
Symmetry; Apply Rabsolu_right; Left; Sup.
Symmetry; Apply Rabsolu_right; Left; Assumption.
Qed.

Lemma maj_term3 : (x,h,eps,l2,alp_f2:R;eps_f2,alp_f2d:posreal;f1,f2:R->R) ``0 < eps`` -> ``(f2 x)<>0`` -> ``(f2 (x+h))<>0`` -> ((h:R)``h <> 0``->``(Rabsolu h) < alp_f2d``->``(Rabsolu (((f2 (x+h))-(f2 x))/h-l2)) < (Rabsolu (((Rsqr (f2 x))*eps)/(8*(f1 x))))``) -> ((a:R)``(Rabsolu a) < (Rmin eps_f2 alp_f2)``->``/(Rabsolu (f2 (x+a))) < 2/(Rabsolu (f2 x))``) -> ``h<>0`` -> ``(Rabsolu h)<alp_f2d`` -> ``(Rabsolu h) < (Rmin eps_f2 alp_f2)`` -> ``(f1 x)<>0`` -> ``(Rabsolu ((f1 x)/((f2 x)*(f2 (x+h)))*(((f2 (x+h))-(f2 x))/h-l2))) < eps/4``.
Intros.
Assert H8 := (H2 h H4 H5).
Assert H9 := (H3 h H6).
Apply Rle_lt_trans with ``(Rabsolu ((f1 x)/((f2 x)*(f2 (x+h)))))*(Rabsolu (((Rsqr (f2 x))*eps)/(8*(f1 x))))``.
Rewrite Rabsolu_mult.
Apply Rle_monotony.
Apply Rabsolu_pos.
Left; Apply H8.
Apply Rlt_le_trans with ``(Rabsolu (2*(f1 x)/((f2 x)*(f2 x))))*(Rabsolu (((Rsqr (f2 x))*eps)/(8*(f1 x))))``.
Apply Rlt_monotony_r.
Apply Rabsolu_pos_lt.
Unfold Rdiv; Unfold Rsqr; Repeat Apply prod_neq_R0; Try Assumption.
Red; Intro H10; Rewrite H10 in H; Elim (Rlt_antirefl ? H).
Apply Rinv_neq_R0; Apply prod_neq_R0; DiscrR Orelse Assumption.
Unfold Rdiv.
Repeat Rewrite Rinv_Rmult; Try Assumption.
Repeat Rewrite Rabsolu_mult.
Replace ``(Rabsolu 2)`` with ``2``.
Rewrite (Rmult_sym ``2``).
Replace ``(Rabsolu (f1 x))*((Rabsolu (/(f2 x)))*(Rabsolu (/(f2 x))))*2`` with ``(Rabsolu (f1 x))*((Rabsolu (/(f2 x)))*((Rabsolu (/(f2 x)))*2))``; [Idtac | Ring].
Repeat Apply Rlt_monotony.
Apply Rabsolu_pos_lt; Assumption.
Apply Rabsolu_pos_lt; Apply Rinv_neq_R0; Assumption.
Repeat Rewrite Rabsolu_Rinv; Assumption Orelse Idtac.
Rewrite <- (Rmult_sym ``2``).
Unfold Rdiv in H9; Exact H9.
Symmetry; Apply Rabsolu_right; Left; Sup0.
Right.
Unfold Rsqr Rdiv.
Rewrite Rinv_Rmult; Try Assumption Orelse DiscrR.
Rewrite Rinv_Rmult; Try Assumption Orelse DiscrR.
Repeat Rewrite Rabsolu_mult.
Repeat Rewrite Rabsolu_Rinv; Try Assumption Orelse DiscrR.
Replace (Rabsolu eps) with eps.
Replace ``(Rabsolu (8))`` with ``8``.
Replace ``(Rabsolu 2)`` with ``2``.
Replace ``8`` with ``4*2``; [Idtac | Ring].
Rewrite Rinv_Rmult; DiscrR.
Replace ``2*((Rabsolu (f1 x))*(/(Rabsolu (f2 x))*/(Rabsolu (f2 x))))*((Rabsolu (f2 x))*(Rabsolu (f2 x))*eps*(/4*/2*/(Rabsolu (f1 x))))`` with ``eps*/4*((Rabsolu (f2 x))*/(Rabsolu (f2 x)))*((Rabsolu (f2 x))*/(Rabsolu (f2 x)))*((Rabsolu (f1 x))*/(Rabsolu (f1 x)))*(2*/2)``; [Idtac | Ring].
Repeat Rewrite <- Rinv_r_sym; Try DiscrR Orelse (Apply Rabsolu_no_R0; Assumption).
Ring.
Symmetry; Apply Rabsolu_right; Left; Sup0.
Symmetry; Apply Rabsolu_right; Left; Sup.
Symmetry; Apply Rabsolu_right; Left; Assumption.
Qed.

Lemma maj_term4 : (x,h,eps,l2,alp_f2,alp_f2c:R;eps_f2:posreal;f1,f2:R->R) ``0 < eps`` -> ``(f2 x)<>0`` -> ``(f2 (x+h))<>0`` -> ((a:R)``(Rabsolu a) < alp_f2c`` -> ``(Rabsolu ((f2 (x+a))-(f2 x))) < (Rabsolu (((Rsqr (f2 x))*(f2 x)*eps)/(8*(f1 x)*l2)))``)  -> ((a:R)``(Rabsolu a) < (Rmin eps_f2 alp_f2)``->``/(Rabsolu (f2 (x+a))) < 2/(Rabsolu (f2 x))``) -> ``h<>0`` -> ``(Rabsolu h)<alp_f2c`` -> ``(Rabsolu h) < (Rmin eps_f2 alp_f2)`` -> ``(f1 x)<>0`` -> ``l2<>0`` -> ``(Rabsolu ((l2*(f1 x))/((Rsqr (f2 x))*(f2 (x+h)))*((f2 (x+h))-(f2 x)))) < eps/4``.
Intros.
Assert H9 := (H2 h H5).
Assert H10 := (H3 h H6).
Apply Rle_lt_trans with ``(Rabsolu ((l2*(f1 x))/((Rsqr (f2 x))*(f2 (x+h)))))*(Rabsolu (((Rsqr (f2 x))*(f2 x)*eps)/(8*(f1 x)*l2)))``.
Rewrite Rabsolu_mult.
Apply Rle_monotony.
Apply Rabsolu_pos.
Left; Apply H9.
Apply Rlt_le_trans with ``(Rabsolu (2*l2*(f1 x)/((Rsqr (f2 x))*(f2 x))))*(Rabsolu (((Rsqr (f2 x))*(f2 x)*eps)/(8*(f1 x)*l2)))``.
Apply Rlt_monotony_r.
Apply Rabsolu_pos_lt.
Unfold Rdiv; Unfold Rsqr; Repeat Apply prod_neq_R0; Assumption Orelse Idtac.
Red; Intro H11; Rewrite H11 in H; Elim (Rlt_antirefl ? H).
Apply Rinv_neq_R0; Apply prod_neq_R0.
Apply prod_neq_R0.
DiscrR.
Assumption.
Assumption.
Unfold Rdiv.
Repeat Rewrite Rinv_Rmult; Try Assumption Orelse (Unfold Rsqr; Apply prod_neq_R0; Assumption).
Repeat Rewrite Rabsolu_mult.
Replace ``(Rabsolu 2)`` with ``2``.
Replace ``2*(Rabsolu l2)*((Rabsolu (f1 x))*((Rabsolu (/(Rsqr (f2 x))))*(Rabsolu (/(f2 x)))))`` with ``(Rabsolu l2)*((Rabsolu (f1 x))*((Rabsolu (/(Rsqr (f2 x))))*((Rabsolu (/(f2 x)))*2)))``; [Idtac | Ring].
Replace ``(Rabsolu l2)*(Rabsolu (f1 x))*((Rabsolu (/(Rsqr (f2 x))))*(Rabsolu (/(f2 (x+h)))))`` with ``(Rabsolu l2)*((Rabsolu (f1 x))*(((Rabsolu (/(Rsqr (f2 x))))*(Rabsolu (/(f2 (x+h)))))))``; [Idtac | Ring].
Repeat Apply Rlt_monotony.
Apply Rabsolu_pos_lt; Assumption.
Apply Rabsolu_pos_lt; Assumption.
Apply Rabsolu_pos_lt; Apply Rinv_neq_R0; Unfold Rsqr; Apply prod_neq_R0;  Assumption.
Repeat Rewrite Rabsolu_Rinv; [Idtac | Assumption | Assumption].
Rewrite <- (Rmult_sym ``2``).
Unfold Rdiv in H10; Exact H10.
Symmetry; Apply Rabsolu_right; Left; Sup0.
Right; Unfold Rsqr Rdiv.
Rewrite Rinv_Rmult; Try Assumption Orelse DiscrR.
Rewrite Rinv_Rmult; Try Assumption Orelse DiscrR.
Rewrite Rinv_Rmult; Try Assumption Orelse DiscrR.
Rewrite Rinv_Rmult; Try Assumption Orelse DiscrR.
Repeat Rewrite Rabsolu_mult.
Repeat Rewrite Rabsolu_Rinv; Try Assumption Orelse DiscrR.
Replace (Rabsolu eps) with eps.
Replace ``(Rabsolu (8))`` with ``8``.
Replace ``(Rabsolu 2)`` with ``2``.
Replace ``8`` with ``4*2``; [Idtac | Ring].
Rewrite Rinv_Rmult; DiscrR.
Replace ``2*(Rabsolu l2)*((Rabsolu (f1 x))*(/(Rabsolu (f2 x))*/(Rabsolu (f2 x))*/(Rabsolu (f2 x))))*((Rabsolu (f2 x))*(Rabsolu (f2 x))*(Rabsolu (f2 x))*eps*(/4*/2*/(Rabsolu (f1 x))*/(Rabsolu l2)))`` with ``eps*/4*((Rabsolu l2)*/(Rabsolu l2))*((Rabsolu (f1 x))*/(Rabsolu (f1 x)))*((Rabsolu (f2 x))*/(Rabsolu (f2 x)))*((Rabsolu (f2 x))*/(Rabsolu (f2 x)))*((Rabsolu (f2 x))*/(Rabsolu (f2 x)))*(2*/2)``; [Idtac | Ring].
Repeat Rewrite <- Rinv_r_sym; Try DiscrR Orelse (Apply Rabsolu_no_R0; Assumption).
Ring.
Symmetry; Apply Rabsolu_right; Left; Sup0.
Symmetry; Apply Rabsolu_right; Left; Sup.
Symmetry; Apply Rabsolu_right; Left; Assumption.
Apply prod_neq_R0; Assumption Orelse DiscrR.
Apply prod_neq_R0; Assumption.
Qed.

Lemma D_x_no_cond : (x,a:R) ``a<>0`` -> (D_x no_cond x ``x+a``).
Intros.
Unfold D_x no_cond.
Split.
Trivial.
Apply Rminus_not_eq.
Unfold Rminus.
Rewrite Ropp_distr1.
Rewrite <- Rplus_assoc.
Rewrite Rplus_Ropp_r.
Rewrite Rplus_Ol.
Apply Ropp_neq; Assumption.
Qed.

Lemma Rabsolu_4 : (a,b,c,d:R) ``(Rabsolu (a+b+c+d)) <= (Rabsolu a) + (Rabsolu b) + (Rabsolu c) + (Rabsolu d)``.
Intros.
Apply Rle_trans with ``(Rabsolu (a+b)) + (Rabsolu (c+d))``.
Replace ``a+b+c+d`` with ``(a+b)+(c+d)``; [Apply Rabsolu_triang | Ring].
Apply Rle_trans with ``(Rabsolu a) + (Rabsolu b) + (Rabsolu (c+d))``.
Apply Rle_compatibility_r.
Apply Rabsolu_triang.
Repeat Rewrite Rplus_assoc; Repeat Apply Rle_compatibility.
Apply Rabsolu_triang.
Qed.

Lemma Rlt_4 : (a,b,c,d,e,f,g,h:R) ``a < b`` -> ``c < d`` -> ``e < f `` -> ``g < h`` -> ``a+c+e+g < b+d+f+h``.
Intros; Apply Rlt_trans with ``b+c+e+g``.
Repeat Apply Rlt_compatibility_r; Assumption.
Repeat Rewrite Rplus_assoc; Apply Rlt_compatibility.
Apply Rlt_trans with ``d+e+g``.
Rewrite Rplus_assoc; Apply Rlt_compatibility_r; Assumption.
Rewrite Rplus_assoc; Apply Rlt_compatibility; Apply Rlt_trans with ``f+g``.
Apply Rlt_compatibility_r; Assumption.
Apply Rlt_compatibility; Assumption.
Qed.

Lemma Rmin_2 : (a,b,c:R) ``a < b`` -> ``a < c`` -> ``a < (Rmin b c)``.
Intros; Unfold Rmin; Case (total_order_Rle b c); Intro; Assumption.
Qed.

Lemma quadruple : (x:R) ``4*x == x + x + x + x``.
Intro; Ring.
Qed.

Lemma quadruple_var : (x:R) `` x == x/4 + x/4 + x/4 + x/4``.
Intro; Rewrite <- quadruple.
Unfold Rdiv; Rewrite <- Rmult_assoc; Rewrite Rinv_r_simpl_m; DiscrR.
Reflexivity.
Qed.

(**********)
Lemma continuous_neq_0 : (f:R->R; x0:R) (continuity_pt f x0) -> ~``(f x0)==0`` -> (EXT eps : posreal | (h:R) ``(Rabsolu h) < eps`` -> ~``(f (x0+h))==0``).
Intros; Unfold continuity_pt in H; Unfold continue_in in H; Unfold limit1_in in H; Unfold limit_in in H; Elim (H ``(Rabsolu ((f x0)/2))``).
Intros; Elim H1; Intros.
Exists (mkposreal x H2).
Intros; Assert H5 := (H3 ``x0+h``).
Cut ``(dist R_met (x0+h) x0) < x`` -> ``(dist R_met (f (x0+h)) (f x0)) < (Rabsolu ((f x0)/2))``.
Unfold dist; Simpl; Unfold R_dist; Replace ``x0+h-x0`` with h.
Intros; Assert H7 := (H6 H4).
Red; Intro.
Rewrite H8 in H7; Unfold Rminus in H7; Rewrite Rplus_Ol in H7; Rewrite Rabsolu_Ropp in H7; Unfold Rdiv in H7; Rewrite Rabsolu_mult in H7; Pattern 1 ``(Rabsolu (f x0)) `` in H7; Rewrite <- Rmult_1r in H7.
Cut ``0<(Rabsolu (f x0))``.
Intro; Assert H10 := (Rlt_monotony_contra ? ? ? H9 H7).
Cut ``(Rabsolu (/2))==/2``.
Assert Hyp:``0<2``.
Sup0.
Intro; Rewrite H11 in H10; Assert H12 := (Rlt_monotony ``2`` ? ? Hyp H10); Rewrite Rmult_1r in H12; Rewrite <- Rinv_r_sym in H12; [Idtac | DiscrR].
Cut (Rlt (IZR `1`) (IZR `2`)).
Unfold IZR; Unfold INR convert; Simpl; Intro; Elim (Rlt_antirefl ``1`` (Rlt_trans ? ? ? H13 H12)).
Apply IZR_lt; Omega.
Unfold Rabsolu; Case (case_Rabsolu ``/2``); Intro.
Assert Hyp:``0<2``.
Sup0.
Assert H11 := (Rlt_monotony ``2`` ? ? Hyp r); Rewrite Rmult_Or in H11; Rewrite <- Rinv_r_sym in H11; [Idtac | DiscrR].
Elim (Rlt_antirefl ``0`` (Rlt_trans ? ? ? Rlt_R0_R1 H11)).
Reflexivity.
Apply (Rabsolu_pos_lt ? H0).
Ring.
Assert H6 := (Req_EM ``x0`` ``x0+h``); Elim H6; Intro.
Intro; Rewrite <- H7; Unfold dist R_met; Unfold R_dist; Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Apply Rabsolu_pos_lt.
Unfold Rdiv; Apply prod_neq_R0; [Assumption | Apply Rinv_neq_R0; DiscrR].
Intro; Apply H5.
Split.
Unfold D_x no_cond.
Split; Trivial Orelse Assumption.
Assumption.
Change ``0 < (Rabsolu ((f x0)/2))``.
Apply Rabsolu_pos_lt; Unfold Rdiv; Apply prod_neq_R0.
Assumption.
Apply Rinv_neq_R0; DiscrR.
Qed.
