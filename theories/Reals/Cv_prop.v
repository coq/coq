(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)
 
(*i $Id$ i*)

Require Max. 
Require Rbase.
Require DiscrR.
Require Rseries.
Require Rcomplet.
Require AltSeries.

(* Unicité de la limite pour les suites convergentes *) 
Lemma UL_suite : (Un:nat->R;l1,l2:R) (Un_cv Un l1) -> (Un_cv Un l2) -> l1==l2. 
Intros Un l1 l2; Unfold Un_cv; Unfold R_dist; Intros. 
Apply cond_eq. 
Intros; Cut ``0<eps/2``; [Intro | Unfold Rdiv; Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Sup0]]. 
Elim (H ``eps/2`` H2); Intros. 
Elim (H0 ``eps/2`` H2); Intros. 
Pose N := (max x x0). 
Apply Rle_lt_trans with ``(Rabsolu (l1 -(Un N)))+(Rabsolu ((Un N)-l2))``. 
Replace ``l1-l2`` with ``(l1-(Un N))+((Un N)-l2)``; [Apply Rabsolu_triang | Ring]. 
Rewrite (double_var eps); Apply Rplus_lt. 
Rewrite <- Rabsolu_Ropp; Rewrite Ropp_distr2; Apply H3; Unfold ge N; Apply le_max_l. 
Apply H4; Unfold ge N; Apply le_max_r. 
Qed.

(* La limite de la somme de deux suites convergentes est la somme des limites *) 
Lemma CV_plus : (An,Bn:nat->R;l1,l2:R) (Un_cv An l1) -> (Un_cv Bn l2) -> (Un_cv [i:nat]``(An i)+(Bn i)`` ``l1+l2``). 
Unfold Un_cv; Unfold R_dist; Intros. 
Cut ``0<eps/2``; [Intro | Unfold Rdiv; Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Sup0]]. 
Elim (H ``eps/2`` H2); Intros. 
Elim (H0 ``eps/2`` H2); Intros. 
Pose N := (max x x0). 
Exists N; Intros. 
Replace ``(An n)+(Bn n)-(l1+l2)`` with ``((An n)-l1)+((Bn n)-l2)``; [Idtac | Ring]. 
Apply Rle_lt_trans with ``(Rabsolu ((An n)-l1))+(Rabsolu ((Bn n)-l2))``. 
Apply Rabsolu_triang. 
Rewrite (double_var eps); Apply Rplus_lt. 
Apply H3; Unfold ge; Apply le_trans with N; [Unfold N; Apply le_max_l | Assumption]. 
Apply H4; Unfold ge; Apply le_trans with N; [Unfold N; Apply le_max_r | Assumption]. 
Qed. 

(* ||a|-|b||<=|a-b| *)
Lemma Rabsolu_triang_inv2 : (a,b:R) ``(Rabsolu ((Rabsolu a)-(Rabsolu b)))<=(Rabsolu (a-b))``. 
Cut (a,b:R) ``(Rabsolu b)<=(Rabsolu a)``->``(Rabsolu ((Rabsolu a)-(Rabsolu b))) <= (Rabsolu (a-b))``. 
Intros; Case (total_order_T (Rabsolu a) (Rabsolu b)); Intro. 
Elim s; Intro. 
Rewrite <- (Rabsolu_Ropp ``(Rabsolu a)-(Rabsolu b)``); Rewrite <- (Rabsolu_Ropp ``a-b``); Do 2 Rewrite Ropp_distr2. 
Apply H; Left; Assumption. 
Rewrite b0; Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Apply Rabsolu_pos. 
Apply H; Left; Assumption. 
Intros; Replace ``(Rabsolu ((Rabsolu a)-(Rabsolu b)))`` with ``(Rabsolu a)-(Rabsolu b)``. 
Apply Rabsolu_triang_inv. 
Rewrite (Rabsolu_right ``(Rabsolu a)-(Rabsolu b)``); [Reflexivity | Apply Rle_sym1; Apply Rle_anti_compatibility with (Rabsolu b); Rewrite Rplus_Or; Replace ``(Rabsolu b)+((Rabsolu a)-(Rabsolu b))`` with (Rabsolu a); [Assumption | Ring]]. 
Qed. 
 
(* Lien convergence / convergence absolue *) 
Lemma cv_cvabs : (Un:nat->R;l:R) (Un_cv Un l) -> (Un_cv [i:nat](Rabsolu (Un i)) (Rabsolu l)). 
Unfold Un_cv; Unfold R_dist; Intros. 
Elim (H eps H0); Intros. 
Exists x; Intros. 
Apply Rle_lt_trans with ``(Rabsolu ((Un n)-l))``. 
Apply Rabsolu_triang_inv2. 
Apply H1; Assumption. 
Qed. 

(* Toute suite convergente est de Cauchy *) 
Lemma CV_Cauchy : (Un:nat->R) (sigTT R [l:R](Un_cv Un l)) -> (Cauchy_crit Un). 
Intros; Elim X; Intros. 
Unfold Cauchy_crit; Intros. 
Unfold Un_cv in p; Unfold R_dist in p. 
Cut ``0<eps/2``; [Intro | Unfold Rdiv; Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Sup0]]. 
Elim (p ``eps/2`` H0); Intros. 
Exists x0; Intros. 
Unfold R_dist; Apply Rle_lt_trans with ``(Rabsolu ((Un n)-x))+(Rabsolu (x-(Un m)))``. 
Replace ``(Un n)-(Un m)`` with ``((Un n)-x)+(x-(Un m))``; [Apply Rabsolu_triang | Ring]. 
Rewrite (double_var eps); Apply Rplus_lt. 
Apply H1; Assumption. 
Rewrite <- Rabsolu_Ropp; Rewrite Ropp_distr2; Apply H1; Assumption. 
Qed. 

(**********)
Lemma maj_by_pos : (Un:nat->R) (sigTT R [l:R](Un_cv Un l)) -> (EXT l:R | ``0<l``/\((n:nat)``(Rabsolu (Un n))<=l``)). 
Intros; Elim X; Intros. 
Cut (sigTT R [l:R](Un_cv [k:nat](Rabsolu (Un k)) l)). 
Intro. 
Assert H := (CV_Cauchy [k:nat](Rabsolu (Un k)) X0). 
Assert H0 := (cauchy_bound [k:nat](Rabsolu (Un k)) H). 
Elim H0; Intros. 
Exists ``x0+1``. 
Cut ``0<=x0``. 
Intro. 
Split. 
Apply ge0_plus_gt0_is_gt0; [Assumption | Apply Rlt_R0_R1]. 
Intros. 
Apply Rle_trans with x0. 
Unfold is_upper_bound in H1. 
Apply H1. 
Exists n; Reflexivity. 
Pattern 1 x0; Rewrite <- Rplus_Or; Apply Rle_compatibility; Left; Apply Rlt_R0_R1. 
Apply Rle_trans with (Rabsolu (Un O)). 
Apply Rabsolu_pos. 
Unfold is_upper_bound in H1. 
Apply H1. 
Exists O; Reflexivity. 
Apply existTT with (Rabsolu x). 
Apply cv_cvabs; Assumption. 
Qed. 
 
(* La limite du produit de deux suites convergentes est le produit des limites *) 
Lemma CV_mult : (An,Bn:nat->R;l1,l2:R) (Un_cv An l1) -> (Un_cv Bn l2) -> (Un_cv [i:nat]``(An i)*(Bn i)`` ``l1*l2``). 
Intros. 
Cut (sigTT R [l:R](Un_cv An l)). 
Intro. 
Assert H1 := (maj_by_pos An X). 
Elim H1; Intros M H2. 
Elim H2; Intros. 
Unfold Un_cv; Unfold R_dist; Intros. 
Cut ``0<eps/(2*M)``. 
Intro. 
Case (Req_EM l2 R0); Intro. 
Unfold Un_cv in H0; Unfold R_dist in H0. 
Elim (H0 ``eps/(2*M)`` H6); Intros. 
Exists x; Intros. 
Apply Rle_lt_trans with ``(Rabsolu ((An n)*(Bn n)-(An n)*l2))+(Rabsolu ((An n)*l2-l1*l2))``. 
Replace ``(An n)*(Bn n)-l1*l2`` with ``((An n)*(Bn n)-(An n)*l2)+((An n)*l2-l1*l2)``; [Apply Rabsolu_triang | Ring]. 
Replace ``(Rabsolu ((An n)*(Bn n)-(An n)*l2))`` with ``(Rabsolu (An n))*(Rabsolu ((Bn n)-l2))``. 
Replace ``(Rabsolu ((An n)*l2-l1*l2))`` with R0. 
Rewrite Rplus_Or. 
Apply Rle_lt_trans with ``M*(Rabsolu ((Bn n)-l2))``. 
Do 2 Rewrite <- (Rmult_sym ``(Rabsolu ((Bn n)-l2))``). 
Apply Rle_monotony. 
Apply Rabsolu_pos. 
Apply H4. 
Apply Rlt_monotony_contra with ``/M``. 
Apply Rlt_Rinv; Apply H3. 
Rewrite <- Rmult_assoc; Rewrite <- Rinv_l_sym. 
Rewrite Rmult_1l; Rewrite (Rmult_sym ``/M``). 
Apply Rlt_trans with  ``eps/(2*M)``. 
Apply H8; Assumption. 
Unfold Rdiv; Rewrite Rinv_Rmult. 
Apply Rlt_monotony_contra with ``2``. 
Sup0.
Replace ``2*(eps*(/2*/M))`` with ``(2*/2)*(eps*/M)``; [Idtac | Ring]. 
Rewrite <- Rinv_r_sym. 
Rewrite Rmult_1l; Rewrite double. 
Pattern 1 ``eps*/M``; Rewrite <- Rplus_Or. 
Apply Rlt_compatibility; Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Assumption]. 
DiscrR. 
DiscrR. 
Red; Intro; Rewrite H10 in H3; Elim (Rlt_antirefl ? H3). 
Red; Intro; Rewrite H10 in H3; Elim (Rlt_antirefl ? H3). 
Rewrite H7; Do 2 Rewrite Rmult_Or; Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Reflexivity. 
Replace ``(An n)*(Bn n)-(An n)*l2`` with ``(An n)*((Bn n)-l2)``; [Idtac | Ring]. 
Symmetry; Apply Rabsolu_mult. 
Cut ``0<eps/(2*(Rabsolu l2))``. 
Intro. 
Unfold Un_cv in H; Unfold R_dist in H; Unfold Un_cv in H0; Unfold R_dist in H0. 
Elim (H ``eps/(2*(Rabsolu l2))`` H8); Intros N1 H9. 
Elim (H0 ``eps/(2*M)`` H6); Intros N2 H10. 
Pose N := (max N1 N2). 
Exists N; Intros. 
Apply Rle_lt_trans with ``(Rabsolu ((An n)*(Bn n)-(An n)*l2))+(Rabsolu ((An n)*l2-l1*l2))``. 
Replace ``(An n)*(Bn n)-l1*l2`` with ``((An n)*(Bn n)-(An n)*l2)+((An n)*l2-l1*l2)``; [Apply Rabsolu_triang | Ring]. 
Replace ``(Rabsolu ((An n)*(Bn n)-(An n)*l2))`` with ``(Rabsolu (An n))*(Rabsolu ((Bn n)-l2))``. 
Replace ``(Rabsolu ((An n)*l2-l1*l2))`` with ``(Rabsolu l2)*(Rabsolu ((An n)-l1))``. 
Rewrite (double_var eps); Apply Rplus_lt. 
Apply Rle_lt_trans with ``M*(Rabsolu ((Bn n)-l2))``. 
Do 2 Rewrite <- (Rmult_sym ``(Rabsolu ((Bn n)-l2))``). 
Apply Rle_monotony. 
Apply Rabsolu_pos. 
Apply H4. 
Apply Rlt_monotony_contra with ``/M``. 
Apply Rlt_Rinv; Apply H3. 
Rewrite <- Rmult_assoc; Rewrite <- Rinv_l_sym. 
Rewrite Rmult_1l; Rewrite (Rmult_sym ``/M``). 
Apply Rlt_le_trans with  ``eps/(2*M)``. 
Apply H10. 
Unfold ge; Apply le_trans with N. 
Unfold N; Apply le_max_r. 
Assumption. 
Unfold Rdiv; Rewrite Rinv_Rmult. 
Right; Ring. 
DiscrR. 
Red; Intro; Rewrite H12 in H3; Elim (Rlt_antirefl ? H3). 
Red; Intro; Rewrite H12 in H3; Elim (Rlt_antirefl ? H3). 
Apply Rlt_monotony_contra with ``/(Rabsolu l2)``. 
Apply Rlt_Rinv; Apply Rabsolu_pos_lt; Assumption. 
Rewrite <- Rmult_assoc; Rewrite <- Rinv_l_sym. 
Rewrite Rmult_1l; Apply Rlt_le_trans with ``eps/(2*(Rabsolu l2))``. 
Apply H9. 
Unfold ge; Apply le_trans with N. 
Unfold N; Apply le_max_l. 
Assumption. 
Unfold Rdiv; Right; Rewrite Rinv_Rmult. 
Ring. 
DiscrR. 
Apply Rabsolu_no_R0; Assumption. 
Apply Rabsolu_no_R0; Assumption. 
Replace ``(An n)*l2-l1*l2`` with ``l2*((An n)-l1)``; [Symmetry; Apply Rabsolu_mult | Ring]. 
Replace ``(An n)*(Bn n)-(An n)*l2`` with ``(An n)*((Bn n)-l2)``; [Symmetry; Apply Rabsolu_mult | Ring]. 
Unfold Rdiv; Apply Rmult_lt_pos. 
Assumption. 
Apply Rlt_Rinv; Apply Rmult_lt_pos; [Sup0 | Apply Rabsolu_pos_lt; Assumption]. 
Unfold Rdiv; Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Apply Rmult_lt_pos; [Sup0 | Assumption]]. 
Apply existTT with l1; Assumption. 
Qed. 

(**********)
Lemma CV_minus : (An,Bn:nat->R;l1,l2:R) (Un_cv An l1) -> (Un_cv Bn l2) -> (Un_cv [i:nat]``(An i)-(Bn i)`` ``l1-l2``). 
Intros. 
Replace [i:nat]``(An i)-(Bn i)`` with [i:nat]``(An i)+((opp_sui Bn) i)``. 
Unfold Rminus; Apply CV_plus. 
Assumption. 
Apply CV_opp; Assumption. 
Unfold Rminus opp_sui; Reflexivity. 
Qed. 

