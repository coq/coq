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
Require SeqSeries.
Require Export Rtrigo_fun.
Require Export Rtrigo_def.
Require Export Rtrigo_alt.
Require Export Cos_rel.
Require Export Cos_plus.
Require ZArith_base.
Require Zcomplements.
Require Classical_Prop.
V7only [Import nat_scope. Import Z_scope. Import R_scope.].
Open Local Scope nat_scope.
Open Local Scope R_scope.

(** sin_PI2 is the only remaining axiom **)
Axiom sin_PI2 : ``(sin (PI/2))==1``.

(**********)
Lemma PI_neq0 : ~``PI==0``.
Red; Intro; Assert H0 := PI_RGT_0; Rewrite H in H0; Elim (Rlt_antirefl ? H0).
Qed.

(**********) 
Lemma cos_minus : (x,y:R) ``(cos (x-y))==(cos x)*(cos y)+(sin x)*(sin y)``.
Intros; Unfold Rminus; Rewrite cos_plus.
Rewrite <- cos_sym; Rewrite sin_antisym; Ring.
Qed.

(**********)
Lemma sin2_cos2 : (x:R) ``(Rsqr (sin x)) + (Rsqr (cos x))==1``.
Intro; Unfold Rsqr; Rewrite Rplus_sym; Rewrite <- (cos_minus x x); Unfold Rminus; Rewrite Rplus_Ropp_r; Apply cos_0.
Qed.

Lemma cos2 : (x:R) ``(Rsqr (cos x))==1-(Rsqr (sin x))``.
Intro x; Generalize (sin2_cos2 x); Intro H1; Rewrite <- H1; Unfold Rminus; Rewrite <- (Rplus_sym (Rsqr (cos x))); Rewrite Rplus_assoc; Rewrite Rplus_Ropp_r; Symmetry; Apply Rplus_Or.
Qed.

(**********)
Lemma cos_PI2 : ``(cos (PI/2))==0``.
Apply Rsqr_eq_0; Rewrite cos2; Rewrite sin_PI2; Rewrite Rsqr_1; Unfold Rminus; Apply Rplus_Ropp_r.
Qed.

(**********)
Lemma cos_PI : ``(cos PI)==-1``.
Replace ``PI`` with ``PI/2+PI/2``.
Rewrite cos_plus.
Rewrite sin_PI2; Rewrite cos_PI2.
Ring.
Symmetry; Apply double_var.
Qed.

Lemma sin_PI : ``(sin PI)==0``.
Assert H := (sin2_cos2 PI).
Rewrite cos_PI in H.
Rewrite <- Rsqr_neg in H.
Rewrite Rsqr_1 in H.
Cut (Rsqr (sin PI))==R0.
Intro; Apply (Rsqr_eq_0 ? H0).
Apply r_Rplus_plus with R1.
Rewrite Rplus_Or; Rewrite Rplus_sym; Exact H.
Qed.

(**********)
Lemma neg_cos : (x:R) ``(cos (x+PI))==-(cos x)``.
Intro x; Rewrite -> cos_plus; Rewrite -> sin_PI; Rewrite -> cos_PI; Ring.
Qed.

(**********)
Lemma sin_cos : (x:R) ``(sin x)==-(cos (PI/2+x))``.
Intro x; Rewrite -> cos_plus; Rewrite -> sin_PI2; Rewrite -> cos_PI2; Ring.
Qed.

(**********)
Lemma sin_plus : (x,y:R) ``(sin (x+y))==(sin x)*(cos y)+(cos x)*(sin y)``.
Intros.
Rewrite (sin_cos ``x+y``).
Replace ``PI/2+(x+y)`` with ``(PI/2+x)+y``; [Rewrite cos_plus | Ring].
Rewrite (sin_cos ``PI/2+x``).
Replace ``PI/2+(PI/2+x)`` with ``x+PI``.
Rewrite neg_cos.
Replace (cos ``PI/2+x``) with ``-(sin x)``.
Ring.
Rewrite sin_cos; Rewrite Ropp_Ropp; Reflexivity.
Pattern 1 PI; Rewrite (double_var PI); Ring.
Qed.

Lemma sin_minus : (x,y:R) ``(sin (x-y))==(sin x)*(cos y)-(cos x)*(sin y)``.
Intros; Unfold Rminus; Rewrite sin_plus.
Rewrite <- cos_sym; Rewrite sin_antisym; Ring.
Qed.

(**********)
Definition tan [x:R] : R := ``(sin x)/(cos x)``.

Lemma tan_plus : (x,y:R) ~``(cos x)==0`` -> ~``(cos y)==0`` -> ~``(cos (x+y))==0`` -> ~``1-(tan x)*(tan y)==0`` -> ``(tan (x+y))==((tan x)+(tan y))/(1-(tan x)*(tan y))``.
Intros; Unfold tan; Rewrite sin_plus; Rewrite cos_plus; Unfold Rdiv; Replace ``((cos x)*(cos y)-(sin x)*(sin y))`` with ``((cos x)*(cos y))*(1-(sin x)*/(cos x)*((sin y)*/(cos y)))``.
Rewrite Rinv_Rmult.
Repeat Rewrite <- Rmult_assoc; Replace ``((sin x)*(cos y)+(cos x)*(sin y))*/((cos x)*(cos y))`` with ``((sin x)*/(cos x)+(sin y)*/(cos y))``.
Reflexivity.
Rewrite Rmult_Rplus_distrl; Rewrite Rinv_Rmult.
Repeat Rewrite Rmult_assoc; Repeat Rewrite (Rmult_sym ``(sin x)``); Repeat Rewrite <- Rmult_assoc.
Repeat Rewrite Rinv_r_simpl_m; [Reflexivity | Assumption | Assumption].
Assumption.
Assumption.
Apply prod_neq_R0; Assumption.
Assumption.
Unfold Rminus; Rewrite Rmult_Rplus_distr; Rewrite Rmult_1r; Apply Rplus_plus_r; Repeat Rewrite Rmult_assoc; Rewrite (Rmult_sym ``(sin x)``); Rewrite (Rmult_sym ``(cos y)``); Rewrite <- Ropp_mul3; Repeat Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym.
Rewrite Rmult_1l; Rewrite (Rmult_sym (sin x)); Rewrite <- Ropp_mul3; Repeat Rewrite Rmult_assoc; Apply Rmult_mult_r; Rewrite (Rmult_sym ``/(cos y)``); Rewrite Rmult_assoc; Rewrite <- Rinv_r_sym.
Apply Rmult_1r.
Assumption.
Assumption.
Qed.

(*******************************************************)
(* Some properties of cos, sin and tan                 *)
(*******************************************************)

Lemma sin2 : (x:R) ``(Rsqr (sin x))==1-(Rsqr (cos x))``.
Intro x; Generalize (cos2 x); Intro H1; Rewrite -> H1.
Unfold Rminus; Rewrite Ropp_distr1; Rewrite <- Rplus_assoc; Rewrite Rplus_Ropp_r; Rewrite Rplus_Ol; Symmetry; Apply Ropp_Ropp.
Qed.

Lemma sin_2a : (x:R) ``(sin (2*x))==2*(sin x)*(cos x)``.
Intro x; Rewrite double; Rewrite sin_plus.
Rewrite <- (Rmult_sym (sin x)); Symmetry; Rewrite Rmult_assoc; Apply double.
Qed.

Lemma cos_2a : (x:R) ``(cos (2*x))==(cos x)*(cos x)-(sin x)*(sin x)``.
Intro x; Rewrite double; Apply cos_plus.
Qed.

Lemma cos_2a_cos : (x:R) ``(cos (2*x))==2*(cos x)*(cos x)-1``.
Intro x; Rewrite double; Unfold Rminus; Rewrite Rmult_assoc; Rewrite cos_plus; Generalize (sin2_cos2 x); Rewrite double; Intro H1; Rewrite <- H1; SqRing.
Qed.

Lemma cos_2a_sin : (x:R) ``(cos (2*x))==1-2*(sin x)*(sin x)``.
Intro x; Rewrite Rmult_assoc; Unfold Rminus; Repeat Rewrite double.
Generalize (sin2_cos2 x); Intro H1; Rewrite <- H1; Rewrite cos_plus; SqRing.
Qed.

Lemma tan_2a : (x:R) ~``(cos x)==0`` -> ~``(cos (2*x))==0`` -> ~``1-(tan x)*(tan x)==0`` ->``(tan (2*x))==(2*(tan x))/(1-(tan x)*(tan x))``.
Repeat Rewrite double; Intros; Repeat Rewrite double; Rewrite double in H0; Apply tan_plus; Assumption.
Qed.

Lemma sin_neg : (x:R) ``(sin (-x))==-(sin x)``.
Apply sin_antisym.
Qed.

Lemma cos_neg : (x:R) ``(cos (-x))==(cos x)``.
Intro; Symmetry; Apply cos_sym.
Qed.

Lemma tan_0 : ``(tan 0)==0``.
Unfold tan; Rewrite -> sin_0; Rewrite -> cos_0.
Unfold Rdiv; Apply Rmult_Ol. 
Qed.

Lemma tan_neg : (x:R) ``(tan (-x))==-(tan x)``.
Intros x; Unfold tan; Rewrite sin_neg; Rewrite cos_neg; Unfold Rdiv.
Apply Ropp_mul1.
Qed.

Lemma tan_minus : (x,y:R) ~``(cos x)==0`` -> ~``(cos y)==0`` -> ~``(cos (x-y))==0`` -> ~``1+(tan x)*(tan y)==0`` -> ``(tan (x-y))==((tan x)-(tan y))/(1+(tan x)*(tan y))``.
Intros; Unfold Rminus; Rewrite tan_plus.
Rewrite tan_neg; Unfold Rminus; Rewrite <- Ropp_mul1; Rewrite Ropp_mul2; Reflexivity.
Assumption.
Rewrite cos_neg; Assumption.
Assumption.
Rewrite tan_neg; Unfold Rminus; Rewrite <- Ropp_mul1; Rewrite Ropp_mul2; Assumption.
Qed.

Lemma cos_3PI2 : ``(cos (3*(PI/2)))==0``.
Replace ``3*(PI/2)`` with ``PI+(PI/2)``.
Rewrite -> cos_plus; Rewrite -> sin_PI; Rewrite -> cos_PI2; Ring.
Pattern 1 PI; Rewrite (double_var PI).
Ring.
Qed.

Lemma sin_2PI : ``(sin (2*PI))==0``.
Rewrite -> sin_2a; Rewrite -> sin_PI; Ring.
Qed.

Lemma cos_2PI : ``(cos (2*PI))==1``.
Rewrite -> cos_2a; Rewrite -> sin_PI; Rewrite -> cos_PI; Ring.
Qed.

Lemma neg_sin : (x:R) ``(sin (x+PI))==-(sin x)``.
Intro x; Rewrite -> sin_plus; Rewrite -> sin_PI; Rewrite -> cos_PI; Ring.
Qed.

Lemma sin_PI_x : (x:R) ``(sin (PI-x))==(sin x)``.
Intro x; Rewrite -> sin_minus; Rewrite -> sin_PI; Rewrite -> cos_PI; Rewrite Rmult_Ol; Unfold Rminus; Rewrite Rplus_Ol; Rewrite Ropp_mul1; Rewrite Ropp_Ropp; Apply Rmult_1l.
Qed.

Lemma sin_period : (x:R)(k:nat) ``(sin (x+2*(INR k)*PI))==(sin x)``.
Intros x k; Induction k.
Cut ``x+2*(INR O)*PI==x``; [Intro; Rewrite H; Reflexivity | Ring].
Replace ``x+2*(INR (S k))*PI`` with ``(x+2*(INR k)*PI)+(2*PI)``; [Rewrite -> sin_plus; Rewrite -> sin_2PI; Rewrite -> cos_2PI; Ring; Apply Hreck | Rewrite -> S_INR; Ring].
Qed.

Lemma cos_period : (x:R)(k:nat) ``(cos (x+2*(INR k)*PI))==(cos x)``.
Intros x k; Induction k.
Cut ``x+2*(INR O)*PI==x``; [Intro; Rewrite H; Reflexivity | Ring].
Replace ``x+2*(INR (S k))*PI`` with ``(x+2*(INR k)*PI)+(2*PI)``; [Rewrite -> cos_plus; Rewrite -> sin_2PI; Rewrite -> cos_2PI; Ring; Apply Hreck | Rewrite -> S_INR; Ring].
Qed.

Lemma sin_shift : (x:R) ``(sin (PI/2-x))==(cos x)``.
Intro x; Rewrite -> sin_minus; Rewrite -> sin_PI2; Rewrite -> cos_PI2; Ring.
Qed.

Lemma cos_shift : (x:R) ``(cos (PI/2-x))==(sin x)``.
Intro x; Rewrite -> cos_minus; Rewrite -> sin_PI2; Rewrite -> cos_PI2; Ring.
Qed.

Lemma cos_sin : (x:R) ``(cos x)==(sin (PI/2+x))``.
Intro x; Rewrite -> sin_plus; Rewrite -> sin_PI2; Rewrite -> cos_PI2; Ring.
Qed.

Lemma PI2_RGT_0 : ``0<PI/2``.
Unfold Rdiv; Apply Rmult_lt_pos; [Apply PI_RGT_0 | Apply Rlt_Rinv; Sup].
Qed. 

Lemma SIN_bound : (x:R) ``-1<=(sin x)<=1``.
Intro; Case (total_order_Rle ``-1`` (sin x)); Intro.
Case (total_order_Rle (sin x) ``1``); Intro.
Split; Assumption.
Cut ``1<(sin x)``.
Intro; Generalize (Rsqr_incrst_1 ``1`` (sin x) H (Rlt_le ``0`` ``1`` Rlt_R0_R1) (Rlt_le ``0`` (sin x) (Rlt_trans ``0`` ``1`` (sin x) Rlt_R0_R1 H))); Rewrite Rsqr_1; Intro; Rewrite sin2 in H0; Unfold Rminus in H0; Generalize (Rlt_compatibility ``-1`` ``1`` ``1+ -(Rsqr (cos x))`` H0); Repeat Rewrite <- Rplus_assoc; Repeat Rewrite Rplus_Ropp_l; Rewrite Rplus_Ol; Intro; Rewrite <- Ropp_O in H1; Generalize (Rlt_Ropp ``-0`` ``-(Rsqr (cos x))`` H1); Repeat Rewrite Ropp_Ropp; Intro; Generalize (pos_Rsqr (cos x)); Intro; Elim (Rlt_antirefl ``0`` (Rle_lt_trans ``0`` (Rsqr (cos x)) ``0`` H3 H2)).
Auto with real.
Cut ``(sin x)< -1``.
Intro; Generalize (Rlt_Ropp (sin x) ``-1`` H); Rewrite Ropp_Ropp; Clear H; Intro; Generalize (Rsqr_incrst_1 ``1`` ``-(sin x)`` H (Rlt_le ``0`` ``1`` Rlt_R0_R1) (Rlt_le ``0`` ``-(sin x)`` (Rlt_trans ``0`` ``1`` ``-(sin x)`` Rlt_R0_R1 H))); Rewrite Rsqr_1; Intro; Rewrite <- Rsqr_neg in H0; Rewrite sin2 in H0; Unfold Rminus in H0; Generalize (Rlt_compatibility ``-1`` ``1`` ``1+ -(Rsqr (cos x))`` H0); Repeat Rewrite <- Rplus_assoc; Repeat Rewrite Rplus_Ropp_l; Rewrite Rplus_Ol; Intro; Rewrite <- Ropp_O in H1; Generalize (Rlt_Ropp ``-0`` ``-(Rsqr (cos x))`` H1); Repeat Rewrite Ropp_Ropp; Intro; Generalize (pos_Rsqr (cos x)); Intro; Elim (Rlt_antirefl ``0`` (Rle_lt_trans ``0`` (Rsqr (cos x)) ``0`` H3 H2)).
Auto with real.
Qed.

Lemma COS_bound : (x:R) ``-1<=(cos x)<=1``.
Intro; Rewrite <- sin_shift; Apply SIN_bound.
Qed.

Lemma cos_sin_0 : (x:R) ~(``(cos x)==0``/\``(sin x)==0``).
Intro; Red; Intro; Elim H; Intros; Generalize (sin2_cos2 x); Intro; Rewrite H0 in H2; Rewrite H1 in H2; Repeat Rewrite Rsqr_O in H2; Rewrite Rplus_Or in H2; Generalize Rlt_R0_R1; Intro; Rewrite <- H2 in H3; Elim (Rlt_antirefl ``0`` H3).
Qed.
  
Lemma cos_sin_0_var : (x:R) ~``(cos x)==0``\/~``(sin x)==0``.
Intro; Apply not_and_or; Apply cos_sin_0.
Qed.

(*****************************************************************)
(* Using series definitions of cos and sin                       *)
(*****************************************************************)

Definition sin_lb [a:R] : R := (sin_approx a (3)).
Definition sin_ub [a:R] : R := (sin_approx a (4)).
Definition cos_lb [a:R] : R := (cos_approx a (3)).
Definition cos_ub [a:R] : R := (cos_approx a (4)).

Lemma sin_lb_gt_0 : (a:R) ``0<a``->``a<=PI/2``->``0<(sin_lb a)``.
Intros.
Unfold sin_lb; Unfold sin_approx; Unfold sin_term.
Pose Un := [i:nat]``(pow a (plus (mult (S (S O)) i) (S O)))/(INR (fact (plus (mult (S (S O)) i) (S O))))``.
Replace (sum_f_R0 [i:nat] ``(pow ( -1) i)*(pow a (plus (mult (S (S O)) i) (S O)))/(INR (fact (plus (mult (S (S O)) i) (S O))))`` (S (S (S O)))) with (sum_f_R0 [i:nat]``(pow (-1) i)*(Un i)`` (3)); [Idtac | Apply sum_eq; Intros; Unfold Un; Reflexivity].
Cut (n:nat)``(Un (S n))<(Un n)``.
Intro; Simpl.
Repeat Rewrite Rmult_1l; Repeat Rewrite Rmult_1r; Replace ``-1*(Un (S O))`` with ``-(Un (S O))``; [Idtac | Ring]; Replace ``-1* -1*(Un (S (S O)))`` with ``(Un (S (S O)))``; [Idtac | Ring]; Replace ``-1*( -1* -1)*(Un (S (S (S O))))`` with ``-(Un (S (S (S O))))``; [Idtac | Ring]; Replace ``(Un O)+ -(Un (S O))+(Un (S (S O)))+ -(Un (S (S (S O))))`` with ``((Un O)-(Un (S O)))+((Un (S (S O)))-(Un (S (S (S O)))))``; [Idtac | Ring].
Apply gt0_plus_gt0_is_gt0.
Unfold Rminus; Apply Rlt_anti_compatibility with (Un (S O)); Rewrite Rplus_Or; Rewrite (Rplus_sym (Un (S O))); Rewrite Rplus_assoc; Rewrite Rplus_Ropp_l; Rewrite Rplus_Or; Apply H1.
Unfold Rminus; Apply Rlt_anti_compatibility with (Un (S (S (S O)))); Rewrite Rplus_Or; Rewrite (Rplus_sym (Un (S (S (S O))))); Rewrite Rplus_assoc; Rewrite Rplus_Ropp_l; Rewrite Rplus_Or; Apply H1.
Intro; Unfold Un.
Cut (plus (mult (2) (S n)) (S O)) = (plus (plus (mult (2) n) (S O)) (2)).
Intro; Rewrite H1.
Rewrite pow_add; Unfold Rdiv; Rewrite Rmult_assoc; Apply Rlt_monotony.
Apply pow_lt; Assumption.
Rewrite <- H1; Apply Rlt_monotony_contra with (INR (fact (plus (mult (S (S O)) n) (S O)))).
Apply lt_INR_0; Apply neq_O_lt.
Assert H2 := (fact_neq_0 (plus (mult (2) n) (1))).
Red; Intro; Elim H2; Symmetry; Assumption.
Rewrite <- Rinv_r_sym.
Apply Rlt_monotony_contra with (INR (fact (plus (mult (S (S O)) (S n)) (S O)))).
Apply lt_INR_0; Apply neq_O_lt.
Assert H2 := (fact_neq_0 (plus (mult (2) (S n)) (1))).
Red; Intro; Elim H2; Symmetry; Assumption.
Rewrite (Rmult_sym (INR (fact (plus (mult (S (S O)) (S n)) (S O))))); Repeat Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym.
Do 2 Rewrite Rmult_1r; Apply Rle_lt_trans with ``(INR (fact (plus (mult (S (S O)) n) (S O))))*4``.
Apply Rle_monotony.
Replace R0 with (INR O); [Idtac | Reflexivity]; Apply le_INR; Apply le_O_n.
Simpl; Rewrite Rmult_1r; Replace ``4`` with ``(Rsqr 2)``; [Idtac | SqRing]; Replace ``a*a`` with (Rsqr a); [Idtac | Reflexivity]; Apply Rsqr_incr_1.
Apply Rle_trans with ``PI/2``; [Assumption | Unfold Rdiv; Apply Rle_monotony_contra with ``2``; [ Sup0 | Rewrite <- Rmult_assoc;  Rewrite Rinv_r_simpl_m; [Replace ``2*2`` with ``4``; [Apply PI_4 | Ring] | DiscrR]]].
Left; Assumption.
Left; Sup0.
Rewrite H1; Replace (plus (plus (mult (S (S O)) n) (S O)) (S (S O))) with (S (S (plus (mult (S (S O)) n) (S O)))).
Do 2 Rewrite fact_simpl; Do 2 Rewrite mult_INR.
Repeat Rewrite <- Rmult_assoc.
Rewrite <- (Rmult_sym (INR (fact (plus (mult (S (S O)) n) (S O))))).
Rewrite Rmult_assoc.
Apply Rlt_monotony.
Apply lt_INR_0; Apply neq_O_lt.
Assert H2 := (fact_neq_0 (plus (mult (2) n) (1))).
Red; Intro; Elim H2; Symmetry; Assumption.
Do 2 Rewrite S_INR; Rewrite plus_INR; Rewrite mult_INR; Pose x := (INR n); Unfold INR.
Replace ``(2*x+1+1+1)*(2*x+1+1)`` with ``4*x*x+10*x+6``; [Idtac | Ring].
Apply Rlt_anti_compatibility with ``-4``; Rewrite Rplus_Ropp_l; Replace ``-4+(4*x*x+10*x+6)`` with ``(4*x*x+10*x)+2``; [Idtac | Ring].
Apply ge0_plus_gt0_is_gt0.
Cut ``0<=x``.
Intro; Apply ge0_plus_ge0_is_ge0; Repeat Apply Rmult_le_pos; Assumption Orelse Left; Sup.
Unfold x; Replace R0 with (INR O); [Apply le_INR; Apply le_O_n | Reflexivity].
Sup0.
Apply INR_eq; Do 2 Rewrite S_INR; Do 3 Rewrite plus_INR; Rewrite mult_INR; Repeat Rewrite S_INR; Ring.
Apply INR_fact_neq_0.
Apply INR_fact_neq_0.
Apply INR_eq; Do 3 Rewrite plus_INR; Do 2 Rewrite mult_INR; Repeat Rewrite S_INR; Ring.
Qed.

Lemma SIN : (a:R) ``0<=a`` -> ``a<=PI`` -> ``(sin_lb a)<=(sin a)<=(sin_ub a)``.
Intros; Unfold sin_lb sin_ub; Apply (sin_bound a (S O) H H0).
Qed.

Lemma COS : (a:R) ``-PI/2<=a`` -> ``a<=PI/2`` -> ``(cos_lb a)<=(cos a)<=(cos_ub a)``.
Intros; Unfold cos_lb cos_ub; Apply (cos_bound a (S O) H H0).
Qed.

(**********)
Lemma _PI2_RLT_0 : ``-(PI/2)<0``.
Rewrite <- Ropp_O; Apply Rlt_Ropp1; Apply PI2_RGT_0.
Qed.

Lemma PI4_RLT_PI2 : ``PI/4<PI/2``.
Unfold Rdiv; Apply Rlt_monotony.
Apply PI_RGT_0.
Apply Rinv_lt.
Apply Rmult_lt_pos; Sup0.
Pattern 1 ``2``; Rewrite <- Rplus_Or.
Replace ``4`` with ``2+2``; [Apply Rlt_compatibility; Sup0 | Ring].
Qed.

Lemma PI2_Rlt_PI : ``PI/2<PI``.
Unfold Rdiv; Pattern 2 PI; Rewrite <- Rmult_1r.
Apply Rlt_monotony.
Apply PI_RGT_0.
Pattern 3 R1; Rewrite <- Rinv_R1; Apply Rinv_lt.
Rewrite Rmult_1l; Sup0.
Pattern 1 R1; Rewrite <- Rplus_Or; Apply Rlt_compatibility; Apply Rlt_R0_R1.
Qed.

(********************************************)
(* Increasing and decreasing of COS and SIN *)
(********************************************)
Theorem sin_gt_0 : (x:R) ``0<x`` -> ``x<PI`` -> ``0<(sin x)``.
Intros; Elim (SIN x (Rlt_le R0 x H) (Rlt_le x PI H0)); Intros H1 _; Case (total_order x ``PI/2``); Intro H2.
Apply Rlt_le_trans with (sin_lb x).
Apply sin_lb_gt_0; [Assumption | Left; Assumption].
Assumption.
Elim H2; Intro H3.
Rewrite H3; Rewrite sin_PI2; Apply Rlt_R0_R1.
Rewrite <- sin_PI_x; Generalize (Rgt_Ropp x ``PI/2`` H3); Intro H4; Generalize (Rlt_compatibility PI (Ropp x) (Ropp ``PI/2``) H4).
Replace ``PI+(-x)`` with ``PI-x``.
Replace ``PI+ -(PI/2)`` with ``PI/2``.
Intro H5; Generalize (Rlt_Ropp x PI H0); Intro H6; Change ``-PI < -x`` in H6; Generalize (Rlt_compatibility PI (Ropp PI) (Ropp x) H6).
Rewrite Rplus_Ropp_r.
Replace ``PI+ -x`` with ``PI-x``.
Intro H7; Elim (SIN ``PI-x`` (Rlt_le R0 ``PI-x`` H7) (Rlt_le ``PI-x`` PI (Rlt_trans ``PI-x`` ``PI/2`` ``PI`` H5 PI2_Rlt_PI))); Intros H8 _; Generalize (sin_lb_gt_0 ``PI-x`` H7 (Rlt_le ``PI-x`` ``PI/2`` H5)); Intro H9; Apply (Rlt_le_trans ``0`` ``(sin_lb (PI-x))`` ``(sin (PI-x))`` H9 H8).
Reflexivity.
Pattern 2 PI; Rewrite double_var; Ring.
Reflexivity.
Qed.

Theorem cos_gt_0 : (x:R) ``-(PI/2)<x`` -> ``x<PI/2`` -> ``0<(cos x)``.
Intros; Rewrite cos_sin; Generalize (Rlt_compatibility ``PI/2`` ``-(PI/2)`` x H).
Rewrite Rplus_Ropp_r; Intro H1; Generalize (Rlt_compatibility ``PI/2`` x ``PI/2`` H0); Rewrite <- double_var; Intro H2; Apply (sin_gt_0 ``PI/2+x`` H1 H2).
Qed.

Lemma sin_ge_0 : (x:R) ``0<=x`` -> ``x<=PI`` -> ``0<=(sin x)``.
Intros x H1 H2; Elim H1; Intro H3; [ Elim H2; Intro H4; [ Left ; Apply (sin_gt_0 x H3 H4) | Rewrite H4; Right; Symmetry; Apply sin_PI ] | Rewrite <- H3; Right; Symmetry; Apply sin_0].
Qed.

Lemma cos_ge_0 : (x:R) ``-(PI/2)<=x`` -> ``x<=PI/2`` -> ``0<=(cos x)``.
Intros x H1 H2; Elim H1; Intro H3; [ Elim H2; Intro H4; [ Left ; Apply (cos_gt_0 x H3 H4) | Rewrite H4; Right; Symmetry; Apply cos_PI2 ] | Rewrite <- H3; Rewrite cos_neg; Right; Symmetry; Apply cos_PI2 ].
Qed.

Lemma sin_le_0 : (x:R) ``PI<=x`` -> ``x<=2*PI`` -> ``(sin x)<=0``.
Intros x H1 H2; Apply Rle_sym2; Rewrite <- Ropp_O; Rewrite <- (Ropp_Ropp (sin x)); Apply Rle_Ropp; Rewrite <- neg_sin; Replace ``x+PI`` with ``(x-PI)+2*(INR (S O))*PI``; [Rewrite -> (sin_period (Rminus x PI) (S O)); Apply sin_ge_0; [Replace ``x-PI`` with ``x+(-PI)``; [Rewrite Rplus_sym; Replace ``0`` with ``(-PI)+PI``; [Apply Rle_compatibility; Assumption | Ring] | Ring] | Replace ``x-PI`` with ``x+(-PI)``; Rewrite Rplus_sym; [Pattern 2 PI; Replace ``PI`` with ``(-PI)+2*PI``; [Apply Rle_compatibility; Assumption | Ring] | Ring]] |Unfold INR; Ring].
Qed.

Lemma cos_le_0 : (x:R) ``PI/2<=x``->``x<=3*(PI/2)``->``(cos x)<=0``.
Intros x H1 H2; Apply Rle_sym2; Rewrite <- Ropp_O; Rewrite <- (Ropp_Ropp (cos x)); Apply Rle_Ropp; Rewrite <- neg_cos; Replace ``x+PI`` with ``(x-PI)+2*(INR (S O))*PI``.
Rewrite cos_period; Apply cos_ge_0.
Replace ``-(PI/2)`` with ``-PI+(PI/2)``.
Unfold Rminus; Rewrite (Rplus_sym x); Apply Rle_compatibility; Assumption.
Pattern 1 PI; Rewrite (double_var PI); Rewrite Ropp_distr1; Ring.
Unfold Rminus; Rewrite Rplus_sym; Replace ``PI/2`` with ``(-PI)+3*(PI/2)``.
Apply Rle_compatibility; Assumption.
Pattern 1 PI; Rewrite (double_var PI); Rewrite Ropp_distr1; Ring. 
Unfold INR; Ring.
Qed.

Lemma sin_lt_0 : (x:R) ``PI<x`` -> ``x<2*PI`` -> ``(sin x)<0``.
Intros x H1 H2; Rewrite <- Ropp_O; Rewrite <- (Ropp_Ropp (sin x)); Apply Rlt_Ropp; Rewrite <- neg_sin; Replace ``x+PI`` with ``(x-PI)+2*(INR (S O))*PI``; [Rewrite -> (sin_period (Rminus x PI) (S O)); Apply sin_gt_0; [Replace ``x-PI`` with ``x+(-PI)``; [Rewrite Rplus_sym; Replace ``0`` with ``(-PI)+PI``; [Apply Rlt_compatibility; Assumption | Ring] | Ring] | Replace ``x-PI`` with ``x+(-PI)``; Rewrite Rplus_sym; [Pattern 2 PI; Replace ``PI`` with ``(-PI)+2*PI``; [Apply Rlt_compatibility; Assumption | Ring] | Ring]] |Unfold INR; Ring].
Qed.

Lemma sin_lt_0_var : (x:R) ``-PI<x`` -> ``x<0`` -> ``(sin x)<0``.
Intros; Generalize (Rlt_compatibility ``2*PI`` ``-PI`` x H); Replace ``2*PI+(-PI)`` with ``PI``; [Intro H1; Rewrite Rplus_sym in H1; Generalize (Rlt_compatibility ``2*PI`` x ``0`` H0); Intro H2; Rewrite (Rplus_sym ``2*PI``) in H2; Rewrite <- (Rplus_sym R0) in H2; Rewrite Rplus_Ol in H2; Rewrite <- (sin_period x (1)); Unfold INR; Replace ``2*1*PI`` with ``2*PI``; [Apply (sin_lt_0 ``x+2*PI`` H1 H2) | Ring] | Ring].
Qed.

Lemma cos_lt_0 : (x:R) ``PI/2<x`` -> ``x<3*(PI/2)``-> ``(cos x)<0``.
Intros x H1 H2; Rewrite <- Ropp_O; Rewrite <- (Ropp_Ropp (cos x)); Apply Rlt_Ropp; Rewrite <- neg_cos; Replace ``x+PI`` with ``(x-PI)+2*(INR (S O))*PI``.
Rewrite cos_period; Apply cos_gt_0.
Replace ``-(PI/2)`` with ``-PI+(PI/2)``.
Unfold Rminus; Rewrite (Rplus_sym x); Apply Rlt_compatibility; Assumption.
Pattern 1 PI; Rewrite (double_var PI); Rewrite Ropp_distr1; Ring. 
Unfold Rminus; Rewrite Rplus_sym; Replace ``PI/2`` with ``(-PI)+3*(PI/2)``.
Apply Rlt_compatibility; Assumption.
Pattern 1 PI; Rewrite (double_var PI); Rewrite Ropp_distr1; Ring. 
Unfold INR; Ring.
Qed.

Lemma tan_gt_0 : (x:R) ``0<x`` -> ``x<PI/2`` -> ``0<(tan x)``.
Intros x H1 H2; Unfold tan; Generalize _PI2_RLT_0; Generalize (Rlt_trans R0 x ``PI/2`` H1 H2); Intros; Generalize (Rlt_trans ``-(PI/2)`` R0 x H0 H1); Intro H5; Generalize (Rlt_trans x ``PI/2`` PI H2 PI2_Rlt_PI); Intro H7; Unfold Rdiv;  Apply Rmult_lt_pos.
Apply sin_gt_0; Assumption.
Apply Rlt_Rinv; Apply cos_gt_0; Assumption.
Qed.

Lemma tan_lt_0 : (x:R) ``-(PI/2)<x``->``x<0``->``(tan x)<0``.
Intros x H1 H2; Unfold tan; Generalize (cos_gt_0 x H1 (Rlt_trans x ``0`` ``PI/2`` H2 PI2_RGT_0)); Intro H3; Rewrite <- Ropp_O; Replace ``(sin x)/(cos x)`` with ``- ((-(sin x))/(cos x))``.
Rewrite <- sin_neg; Apply Rgt_Ropp; Change ``0<(sin (-x))/(cos x)``; Unfold Rdiv; Apply Rmult_lt_pos.
Apply sin_gt_0.
Rewrite <- Ropp_O; Apply Rgt_Ropp; Assumption.
Apply Rlt_trans with ``PI/2``.
Rewrite <- (Ropp_Ropp ``PI/2``); Apply Rgt_Ropp; Assumption.
Apply PI2_Rlt_PI.
Apply Rlt_Rinv; Assumption.
Unfold Rdiv; Ring.
Qed.

Lemma cos_ge_0_3PI2 : (x:R) ``3*(PI/2)<=x``->``x<=2*PI``->``0<=(cos x)``.
Intros; Rewrite <- cos_neg; Rewrite <- (cos_period ``-x`` (1)); Unfold INR; Replace ``-x+2*1*PI`` with ``2*PI-x``.
Generalize (Rle_Ropp x ``2*PI`` H0); Intro H1; Generalize (Rle_sym2 ``-(2*PI)`` ``-x`` H1); Clear H1; Intro H1; Generalize (Rle_compatibility ``2*PI`` ``-(2*PI)`` ``-x`` H1).
Rewrite Rplus_Ropp_r. 
Intro H2; Generalize (Rle_Ropp ``3*(PI/2)`` x H); Intro H3; Generalize (Rle_sym2 ``-x`` ``-(3*(PI/2))`` H3); Clear H3; Intro H3;  Generalize (Rle_compatibility ``2*PI`` ``-x`` ``-(3*(PI/2))`` H3).
Replace ``2*PI+ -(3*PI/2)`` with ``PI/2``.
Intro H4; Apply (cos_ge_0 ``2*PI-x`` (Rlt_le ``-(PI/2)`` ``2*PI-x`` (Rlt_le_trans ``-(PI/2)`` ``0`` ``2*PI-x`` _PI2_RLT_0 H2)) H4).
Rewrite double; Pattern 2 3 PI; Rewrite double_var; Ring.
Ring.
Qed.

Lemma form1 : (p,q:R) ``(cos p)+(cos q)==2*(cos ((p-q)/2))*(cos ((p+q)/2))``.
Intros p q; Pattern 1 p; Replace ``p`` with ``(p-q)/2+(p+q)/2``.
Rewrite <- (cos_neg q); Replace``-q`` with ``(p-q)/2-(p+q)/2``.
Rewrite cos_plus; Rewrite cos_minus; Ring.
Pattern 3 q; Rewrite double_var; Unfold Rdiv; Ring.
Pattern 3 p; Rewrite double_var; Unfold Rdiv; Ring.
Qed.

Lemma form2 : (p,q:R) ``(cos p)-(cos q)==-2*(sin ((p-q)/2))*(sin ((p+q)/2))``.
Intros p q; Pattern 1 p; Replace ``p`` with ``(p-q)/2+(p+q)/2``.
Rewrite <- (cos_neg q); Replace``-q`` with ``(p-q)/2-(p+q)/2``.
Rewrite cos_plus; Rewrite cos_minus; Ring.
Pattern 3 q; Rewrite double_var; Unfold Rdiv; Ring.
Pattern 3 p; Rewrite double_var; Unfold Rdiv; Ring.
Qed.

Lemma form3 : (p,q:R) ``(sin p)+(sin q)==2*(cos ((p-q)/2))*(sin ((p+q)/2))``.
Intros p q; Pattern 1 p; Replace ``p`` with ``(p-q)/2+(p+q)/2``.
Pattern 3 q; Replace ``q`` with ``(p+q)/2-(p-q)/2``.
Rewrite sin_plus; Rewrite sin_minus; Ring.
Pattern 3 q; Rewrite double_var; Unfold Rdiv; Ring.
Pattern 3 p; Rewrite double_var; Unfold Rdiv; Ring.
Qed.

Lemma form4 : (p,q:R) ``(sin p)-(sin q)==2*(cos ((p+q)/2))*(sin ((p-q)/2))``.
Intros p q; Pattern 1 p; Replace ``p`` with ``(p-q)/2+(p+q)/2``.
Pattern 3 q; Replace ``q`` with ``(p+q)/2-(p-q)/2``.
Rewrite sin_plus; Rewrite sin_minus; Ring.
Pattern 3 q; Rewrite double_var; Unfold Rdiv; Ring.
Pattern 3 p; Rewrite double_var; Unfold Rdiv; Ring.

Qed.

Lemma sin_increasing_0 : (x,y:R) ``-(PI/2)<=x``->``x<=PI/2``->``-(PI/2)<=y``->``y<=PI/2``->``(sin x)<(sin y)``->``x<y``.
Intros; Cut ``(sin ((x-y)/2))<0``.
Intro H4; Case (total_order ``(x-y)/2`` ``0``); Intro H5.
Assert Hyp : ``0<2``.
Sup0.
Generalize (Rlt_monotony ``2`` ``(x-y)/2`` ``0`` Hyp H5).
Unfold Rdiv.
Rewrite <- Rmult_assoc.
Rewrite Rinv_r_simpl_m.
Rewrite Rmult_Or.
Clear H5; Intro H5; Apply Rminus_lt; Assumption.
DiscrR.
Elim H5; Intro H6.
Rewrite H6 in H4; Rewrite sin_0 in H4; Elim (Rlt_antirefl ``0`` H4).
Change ``0<(x-y)/2`` in H6; Generalize (Rle_Ropp ``-(PI/2)`` y H1).
Rewrite Ropp_Ropp.
Intro H7; Generalize (Rle_sym2 ``-y`` ``PI/2`` H7); Clear H7; Intro H7; Generalize (Rplus_le x ``PI/2`` ``-y`` ``PI/2`` H0 H7).
Rewrite <- double_var.
Intro H8.
Assert Hyp : ``0<2``.
Sup0.
Generalize (Rle_monotony ``(Rinv 2)`` ``x-y`` PI (Rlt_le ``0`` ``/2`` (Rlt_Rinv ``2`` Hyp)) H8).
Repeat Rewrite (Rmult_sym ``/2``). 
Intro H9; Generalize (sin_gt_0 ``(x-y)/2`` H6 (Rle_lt_trans ``(x-y)/2`` ``PI/2`` PI H9 PI2_Rlt_PI)); Intro H10; Elim (Rlt_antirefl ``(sin ((x-y)/2))`` (Rlt_trans ``(sin ((x-y)/2))`` ``0`` ``(sin ((x-y)/2))`` H4 H10)).
Generalize (Rlt_minus (sin x) (sin y) H3); Clear H3; Intro H3; Rewrite form4 in H3; Generalize (Rplus_le x ``PI/2`` y ``PI/2`` H0 H2).
Rewrite <- double_var.
Assert Hyp : ``0<2``.
Sup0.
Intro H4; Generalize (Rle_monotony ``(Rinv 2)`` ``x+y`` PI (Rlt_le ``0`` ``/2`` (Rlt_Rinv ``2`` Hyp)) H4).
Repeat Rewrite (Rmult_sym ``/2``). 
Clear H4; Intro H4; Generalize (Rplus_le ``-(PI/2)`` x ``-(PI/2)`` y H H1); Replace ``-(PI/2)+(-(PI/2))`` with ``-PI``.
Intro H5; Generalize (Rle_monotony ``(Rinv 2)`` ``-PI`` ``x+y`` (Rlt_le ``0`` ``/2`` (Rlt_Rinv ``2`` Hyp)) H5).
Replace ``/2*(x+y)`` with ``(x+y)/2``.
Replace ``/2*(-PI)`` with ``-(PI/2)``.
Clear H5; Intro H5; Elim H4; Intro H40.
Elim H5; Intro H50.
Generalize (cos_gt_0 ``(x+y)/2`` H50 H40); Intro H6; Generalize (Rlt_monotony ``2`` ``0`` ``(cos ((x+y)/2))`` Hyp H6).
Rewrite Rmult_Or. 
Clear H6; Intro H6; Case (case_Rabsolu ``(sin ((x-y)/2))``); Intro H7.
Assumption.
Generalize (Rle_sym2 ``0`` ``(sin ((x-y)/2))`` H7); Clear H7; Intro H7; Generalize (Rmult_le_pos ``2*(cos ((x+y)/2))`` ``(sin ((x-y)/2))`` (Rlt_le ``0`` ``2*(cos ((x+y)/2))`` H6) H7); Intro H8; Generalize (Rle_lt_trans ``0`` ``2*(cos ((x+y)/2))*(sin ((x-y)/2))`` ``0`` H8 H3); Intro H9; Elim (Rlt_antirefl ``0`` H9).
Rewrite <- H50 in H3; Rewrite cos_neg in H3; Rewrite cos_PI2 in H3; Rewrite Rmult_Or in H3; Rewrite Rmult_Ol in H3; Elim (Rlt_antirefl ``0`` H3).
Unfold Rdiv in H3.
Rewrite H40 in H3; Assert H50 := cos_PI2; Unfold Rdiv in H50; Rewrite H50 in H3; Rewrite Rmult_Or in H3; Rewrite Rmult_Ol in H3; Elim (Rlt_antirefl ``0`` H3).
Unfold Rdiv.
Rewrite <- Ropp_mul1.
Apply Rmult_sym.
Unfold Rdiv; Apply Rmult_sym.
Pattern 1 PI; Rewrite double_var.
Rewrite Ropp_distr1.
Reflexivity.
Qed.

Lemma sin_increasing_1 : (x,y:R) ``-(PI/2)<=x``->``x<=PI/2``->``-(PI/2)<=y``->``y<=PI/2``->``x<y``->``(sin x)<(sin y)``.
Intros; Generalize (Rlt_compatibility ``x`` ``x`` ``y`` H3); Intro H4; Generalize (Rplus_le ``-(PI/2)`` x ``-(PI/2)`` x H H); Replace ``-(PI/2)+ (-(PI/2))`` with ``-PI``.
Assert Hyp : ``0<2``.
Sup0.
Intro H5; Generalize (Rle_lt_trans ``-PI`` ``x+x`` ``x+y`` H5 H4); Intro H6; Generalize (Rlt_monotony ``(Rinv 2)`` ``-PI`` ``x+y`` (Rlt_Rinv ``2`` Hyp) H6); Replace ``/2*(-PI)`` with ``-(PI/2)``.
Replace ``/2*(x+y)`` with ``(x+y)/2``.
Clear H4 H5 H6; Intro H4; Generalize (Rlt_compatibility ``y`` ``x`` ``y`` H3); Intro H5; Rewrite Rplus_sym in H5; Generalize (Rplus_le y ``PI/2`` y ``PI/2`` H2 H2).
Rewrite <- double_var.
Intro H6; Generalize (Rlt_le_trans ``x+y`` ``y+y`` PI H5 H6); Intro H7; Generalize (Rlt_monotony ``(Rinv 2)``  ``x+y`` PI (Rlt_Rinv ``2`` Hyp) H7); Replace ``/2*PI`` with ``PI/2``.
Replace ``/2*(x+y)`` with ``(x+y)/2``.
Clear H5 H6 H7; Intro H5; Generalize (Rle_Ropp ``-(PI/2)`` y H1); Rewrite Ropp_Ropp; Clear H1; Intro H1; Generalize (Rle_sym2 ``-y`` ``PI/2`` H1); Clear H1; Intro H1; Generalize (Rle_Ropp y ``PI/2`` H2); Clear H2; Intro H2; Generalize (Rle_sym2 ``-(PI/2)`` ``-y`` H2); Clear H2; Intro H2; Generalize (Rlt_compatibility ``-y`` x y H3); Replace ``-y+x`` with ``x-y``.
Rewrite Rplus_Ropp_l.
Intro H6; Generalize (Rlt_monotony ``(Rinv 2)``  ``x-y`` ``0`` (Rlt_Rinv ``2`` Hyp) H6); Rewrite Rmult_Or; Replace ``/2*(x-y)`` with ``(x-y)/2``.
Clear H6; Intro H6; Generalize (Rplus_le  ``-(PI/2)`` x ``-(PI/2)`` ``-y`` H H2); Replace ``-(PI/2)+ (-(PI/2))`` with ``-PI``.
Replace `` x+ -y`` with ``x-y``.
Intro H7; Generalize (Rle_monotony ``(Rinv 2)`` ``-PI`` ``x-y`` (Rlt_le ``0`` ``/2`` (Rlt_Rinv ``2`` Hyp)) H7); Replace ``/2*(-PI)`` with ``-(PI/2)``.
Replace ``/2*(x-y)`` with ``(x-y)/2``.
Clear H7; Intro H7; Clear H H0 H1 H2; Apply Rminus_lt; Rewrite form4; Generalize (cos_gt_0 ``(x+y)/2`` H4 H5); Intro H8; Generalize (Rmult_lt_pos ``2`` ``(cos ((x+y)/2))`` Hyp H8); Clear H8; Intro H8; Cut ``-PI< -(PI/2)``.
Intro H9; Generalize (sin_lt_0_var ``(x-y)/2`` (Rlt_le_trans ``-PI`` ``-(PI/2)`` ``(x-y)/2`` H9 H7) H6); Intro H10; Generalize (Rlt_anti_monotony ``(sin ((x-y)/2))`` ``0`` ``2*(cos ((x+y)/2))`` H10 H8); Intro H11; Rewrite Rmult_Or in H11; Rewrite Rmult_sym; Assumption.
Apply Rlt_Ropp; Apply PI2_Rlt_PI.
Unfold Rdiv; Apply Rmult_sym.
Unfold Rdiv; Rewrite <- Ropp_mul1; Apply Rmult_sym.
Reflexivity.
Pattern 1 PI; Rewrite double_var.
Rewrite Ropp_distr1.
Reflexivity.
Unfold Rdiv; Apply Rmult_sym.
Unfold Rminus; Apply Rplus_sym.
Unfold Rdiv; Apply Rmult_sym.
Unfold Rdiv; Apply Rmult_sym.
Unfold Rdiv; Apply Rmult_sym.
Unfold Rdiv.
Rewrite <- Ropp_mul1.
Apply Rmult_sym.
Pattern 1 PI; Rewrite double_var.
Rewrite Ropp_distr1.
Reflexivity.
Qed.

Lemma sin_decreasing_0 : (x,y:R) ``x<=3*(PI/2)``-> ``PI/2<=x`` -> ``y<=3*(PI/2)``-> ``PI/2<=y`` -> ``(sin x)<(sin y)`` -> ``y<x``.
Intros; Rewrite <- (sin_PI_x x) in H3; Rewrite <- (sin_PI_x y) in H3; Generalize (Rlt_Ropp ``(sin (PI-x))`` ``(sin (PI-y))`` H3); Repeat Rewrite <- sin_neg; Generalize (Rle_compatibility ``-PI`` x ``3*(PI/2)`` H); Generalize (Rle_compatibility ``-PI`` ``PI/2`` x H0); Generalize (Rle_compatibility ``-PI`` y ``3*(PI/2)`` H1); Generalize (Rle_compatibility ``-PI`` ``PI/2`` y H2); Replace ``-PI+x`` with ``x-PI``.
Replace ``-PI+PI/2`` with ``-(PI/2)``.
Replace ``-PI+y`` with ``y-PI``.
Replace ``-PI+3*(PI/2)`` with ``PI/2``.
Replace ``-(PI-x)`` with ``x-PI``.
Replace ``-(PI-y)`` with ``y-PI``.
Intros; Change ``(sin (y-PI))<(sin (x-PI))`` in H8; Apply Rlt_anti_compatibility with ``-PI``; Rewrite Rplus_sym; Replace ``y+ (-PI)`` with ``y-PI``.
Rewrite Rplus_sym; Replace ``x+ (-PI)`` with ``x-PI``.
Apply (sin_increasing_0 ``y-PI`` ``x-PI`` H4 H5 H6 H7 H8).
Reflexivity.
Reflexivity.
Unfold Rminus; Rewrite Ropp_distr1.
Rewrite Ropp_Ropp.
Apply Rplus_sym.
Unfold Rminus; Rewrite Ropp_distr1.
Rewrite Ropp_Ropp.
Apply Rplus_sym.
Pattern 2 PI; Rewrite double_var.
Rewrite Ropp_distr1.
Ring.
Unfold Rminus; Apply Rplus_sym.
Pattern 2 PI; Rewrite double_var.
Rewrite Ropp_distr1.
Ring.
Unfold Rminus; Apply Rplus_sym.
Qed.

Lemma sin_decreasing_1 : (x,y:R) ``x<=3*(PI/2)``-> ``PI/2<=x`` -> ``y<=3*(PI/2)``-> ``PI/2<=y`` -> ``x<y``  -> ``(sin y)<(sin x)``.
Intros; Rewrite <- (sin_PI_x x); Rewrite <- (sin_PI_x y); Generalize (Rle_compatibility ``-PI`` x ``3*(PI/2)`` H); Generalize (Rle_compatibility ``-PI`` ``PI/2`` x H0); Generalize (Rle_compatibility ``-PI`` y ``3*(PI/2)`` H1); Generalize (Rle_compatibility ``-PI`` ``PI/2`` y H2); Generalize (Rlt_compatibility ``-PI`` x y H3); Replace ``-PI+PI/2`` with ``-(PI/2)``.
Replace ``-PI+y`` with ``y-PI``.
Replace ``-PI+3*(PI/2)`` with ``PI/2``.
Replace ``-PI+x`` with ``x-PI``.
Intros; Apply Ropp_Rlt; Repeat Rewrite <- sin_neg; Replace ``-(PI-x)`` with ``x-PI``.
Replace ``-(PI-y)`` with ``y-PI``.
Apply (sin_increasing_1 ``x-PI`` ``y-PI`` H7 H8 H5 H6 H4).
Unfold Rminus; Rewrite Ropp_distr1.
Rewrite Ropp_Ropp.
Apply Rplus_sym.
Unfold Rminus; Rewrite Ropp_distr1.
Rewrite Ropp_Ropp.
Apply Rplus_sym.
Unfold Rminus; Apply Rplus_sym.
Pattern 2 PI; Rewrite double_var; Ring.
Unfold Rminus; Apply Rplus_sym.
Pattern 2 PI; Rewrite double_var; Ring.
Qed.

Lemma cos_increasing_0 : (x,y:R) ``PI<=x`` -> ``x<=2*PI`` ->``PI<=y`` -> ``y<=2*PI`` -> ``(cos x)<(cos y)`` -> ``x<y``.
Intros x y H1 H2 H3 H4; Rewrite <- (cos_neg x); Rewrite <- (cos_neg y); Rewrite <- (cos_period ``-x`` (1)); Rewrite <- (cos_period ``-y`` (1)); Unfold INR; Replace ``-x+2*1*PI`` with ``PI/2-(x-3*(PI/2))``.
Replace ``-y+2*1*PI`` with ``PI/2-(y-3*(PI/2))``.
Repeat Rewrite cos_shift; Intro H5; Generalize (Rle_compatibility ``-3*(PI/2)`` PI x H1); Generalize (Rle_compatibility ``-3*(PI/2)`` x ``2*PI`` H2); Generalize (Rle_compatibility ``-3*(PI/2)`` PI y H3); Generalize (Rle_compatibility ``-3*(PI/2)`` y ``2*PI`` H4).
Replace ``-3*(PI/2)+y`` with ``y-3*(PI/2)``.
Replace ``-3*(PI/2)+x`` with ``x-3*(PI/2)``.
Replace ``-3*(PI/2)+2*PI`` with ``PI/2``.
Replace ``-3*PI/2+PI`` with ``-(PI/2)``.
Clear H1 H2 H3 H4; Intros H1 H2 H3 H4; Apply Rlt_anti_compatibility with ``-3*(PI/2)``; Replace ``-3*PI/2+x`` with ``x-3*(PI/2)``.
Replace ``-3*PI/2+y`` with ``y-3*(PI/2)``.
Apply (sin_increasing_0 ``x-3*(PI/2)`` ``y-3*(PI/2)`` H4 H3 H2 H1 H5).
Unfold Rminus.
Rewrite Ropp_mul1. 
Apply Rplus_sym. 
Unfold Rminus.
Rewrite Ropp_mul1. 
Apply Rplus_sym. 
Pattern 3 PI; Rewrite double_var.
Ring.
Rewrite double; Pattern 3 4 PI; Rewrite double_var.
Ring.
Unfold Rminus.
Rewrite Ropp_mul1. 
Apply Rplus_sym. 
Unfold Rminus.
Rewrite Ropp_mul1. 
Apply Rplus_sym. 
Rewrite Rmult_1r.
Rewrite (double PI); Pattern 3 4 PI; Rewrite double_var.
Ring.
Rewrite Rmult_1r.
Rewrite (double PI); Pattern 3 4 PI; Rewrite double_var.
Ring.
Qed.

Lemma cos_increasing_1 : (x,y:R) ``PI<=x`` -> ``x<=2*PI`` ->``PI<=y`` -> ``y<=2*PI`` -> ``x<y`` -> ``(cos x)<(cos y)``.
Intros x y H1 H2 H3 H4 H5; Generalize (Rle_compatibility ``-3*(PI/2)`` PI x H1); Generalize (Rle_compatibility ``-3*(PI/2)`` x ``2*PI`` H2); Generalize (Rle_compatibility ``-3*(PI/2)`` PI y H3); Generalize (Rle_compatibility ``-3*(PI/2)`` y ``2*PI`` H4); Generalize (Rlt_compatibility ``-3*(PI/2)`` x y H5); Rewrite <- (cos_neg x); Rewrite <- (cos_neg y); Rewrite <- (cos_period ``-x`` (1)); Rewrite <- (cos_period ``-y`` (1)); Unfold INR; Replace ``-3*(PI/2)+x`` with ``x-3*(PI/2)``.
Replace ``-3*(PI/2)+y`` with ``y-3*(PI/2)``.
Replace ``-3*(PI/2)+PI`` with ``-(PI/2)``.
Replace ``-3*(PI/2)+2*PI`` with ``PI/2``.
Clear H1 H2 H3 H4 H5; Intros H1 H2 H3 H4 H5; Replace ``-x+2*1*PI`` with ``(PI/2)-(x-3*(PI/2))``.
Replace ``-y+2*1*PI`` with ``(PI/2)-(y-3*(PI/2))``.
Repeat Rewrite cos_shift; Apply (sin_increasing_1 ``x-3*(PI/2)`` ``y-3*(PI/2)`` H5 H4 H3 H2 H1).
Rewrite Rmult_1r.
Rewrite (double PI); Pattern 3 4 PI; Rewrite double_var.
Ring.
Rewrite Rmult_1r.
Rewrite (double PI); Pattern 3 4 PI; Rewrite double_var.
Ring.
Rewrite (double PI); Pattern 3 4 PI; Rewrite double_var.
Ring.
Pattern 3 PI; Rewrite double_var; Ring.
Unfold Rminus.
Rewrite <- Ropp_mul1.
Apply Rplus_sym.
Unfold Rminus.
Rewrite <- Ropp_mul1.
Apply Rplus_sym.
Qed.

Lemma cos_decreasing_0 : (x,y:R) ``0<=x``->``x<=PI``->``0<=y``->``y<=PI``->``(cos x)<(cos y)``->``y<x``.
Intros; Generalize (Rlt_Ropp (cos x) (cos y) H3); Repeat Rewrite <- neg_cos; Intro H4; Change ``(cos (y+PI))<(cos (x+PI))`` in H4; Rewrite (Rplus_sym x) in H4; Rewrite (Rplus_sym y) in H4; Generalize (Rle_compatibility PI ``0`` x H); Generalize (Rle_compatibility PI x PI H0); Generalize (Rle_compatibility PI ``0`` y H1); Generalize (Rle_compatibility PI y PI H2); Rewrite Rplus_Or.
Rewrite <- double.
Clear H H0 H1 H2 H3; Intros; Apply Rlt_anti_compatibility with ``PI``; Apply (cos_increasing_0 ``PI+y`` ``PI+x`` H0 H H2 H1 H4).
Qed.

Lemma cos_decreasing_1 : (x,y:R) ``0<=x``->``x<=PI``->``0<=y``->``y<=PI``->``x<y``->``(cos y)<(cos x)``.
Intros; Apply Ropp_Rlt; Repeat Rewrite <- neg_cos; Rewrite (Rplus_sym x); Rewrite (Rplus_sym y); Generalize (Rle_compatibility PI ``0`` x H); Generalize (Rle_compatibility PI x PI H0); Generalize (Rle_compatibility PI ``0`` y H1); Generalize (Rle_compatibility PI y PI H2); Rewrite Rplus_Or.
Rewrite <- double.
Generalize (Rlt_compatibility PI x y H3); Clear H H0 H1 H2 H3; Intros; Apply (cos_increasing_1 ``PI+x`` ``PI+y`` H3 H2 H1 H0 H).
Qed.

Lemma tan_diff : (x,y:R) ~``(cos x)==0``->~``(cos y)==0``->``(tan x)-(tan y)==(sin (x-y))/((cos x)*(cos y))``.
Intros; Unfold tan;Rewrite sin_minus.
Unfold Rdiv. 
Unfold Rminus.
Rewrite Rmult_Rplus_distrl.
Rewrite Rinv_Rmult.
Repeat Rewrite (Rmult_sym (sin x)).
Repeat Rewrite Rmult_assoc.
Rewrite (Rmult_sym (cos y)).
Repeat Rewrite Rmult_assoc.
Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r.
Rewrite (Rmult_sym (sin x)).
Apply Rplus_plus_r.
Rewrite <- Ropp_mul1.
Rewrite <- Ropp_mul3.
Rewrite (Rmult_sym ``/(cos x)``).
Repeat Rewrite Rmult_assoc.
Rewrite (Rmult_sym (cos x)).
Repeat Rewrite Rmult_assoc.
Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r.
Reflexivity.
Assumption.
Assumption.
Assumption.
Assumption.
Qed.

Lemma tan_increasing_0 : (x,y:R) ``-(PI/4)<=x``->``x<=PI/4`` ->``-(PI/4)<=y``->``y<=PI/4``->``(tan x)<(tan y)``->``x<y``.
Intros; Generalize PI4_RLT_PI2; Intro H4; Generalize (Rlt_Ropp ``PI/4`` ``PI/2`` H4); Intro H5; Change ``-(PI/2)< -(PI/4)`` in H5; Generalize (cos_gt_0 x (Rlt_le_trans ``-(PI/2)`` ``-(PI/4)`` x H5 H) (Rle_lt_trans x ``PI/4`` ``PI/2`` H0 H4)); Intro HP1; Generalize (cos_gt_0 y (Rlt_le_trans ``-(PI/2)`` ``-(PI/4)`` y H5 H1) (Rle_lt_trans y ``PI/4`` ``PI/2`` H2 H4)); Intro HP2; Generalize (not_sym ``0`` (cos x) (Rlt_not_eq ``0`` (cos x) (cos_gt_0 x (Rlt_le_trans ``-(PI/2)`` ``-(PI/4)`` x H5 H) (Rle_lt_trans x ``PI/4`` ``PI/2`` H0 H4)))); Intro H6; Generalize (not_sym ``0`` (cos y) (Rlt_not_eq ``0`` (cos y) (cos_gt_0 y (Rlt_le_trans ``-(PI/2)`` ``-(PI/4)`` y H5 H1) (Rle_lt_trans y ``PI/4`` ``PI/2`` H2 H4)))); Intro H7; Generalize (tan_diff x y H6 H7); Intro H8; Generalize (Rlt_minus (tan x) (tan y) H3); Clear H3; Intro H3; Rewrite H8 in H3; Cut ``(sin (x-y))<0``.
Intro H9; Generalize (Rle_Ropp ``-(PI/4)`` y H1); Rewrite Ropp_Ropp; Intro H10; Generalize (Rle_sym2 ``-y`` ``PI/4`` H10); Clear H10; Intro H10; Generalize (Rle_Ropp y ``PI/4`` H2); Intro H11; Generalize (Rle_sym2 ``-(PI/4)`` ``-y`` H11); Clear H11; Intro H11; Generalize (Rplus_le ``-(PI/4)`` x ``-(PI/4)`` ``-y`` H H11); Generalize (Rplus_le x ``PI/4`` ``-y`` ``PI/4`` H0 H10); Replace ``x+ -y`` with ``x-y``.
Replace ``PI/4+PI/4`` with ``PI/2``.
Replace ``-(PI/4)+ -(PI/4)`` with ``-(PI/2)``.
Intros; Case (total_order ``0`` ``x-y``); Intro H14.
Generalize (sin_gt_0 ``x-y`` H14 (Rle_lt_trans ``x-y`` ``PI/2`` PI H12 PI2_Rlt_PI)); Intro H15; Elim (Rlt_antirefl ``0`` (Rlt_trans ``0`` ``(sin (x-y))`` ``0`` H15 H9)).
Elim H14; Intro H15.
Rewrite <- H15 in H9; Rewrite -> sin_0 in H9;  Elim (Rlt_antirefl ``0`` H9). 
Apply Rminus_lt; Assumption.
Pattern 1 PI; Rewrite double_var.
Unfold Rdiv.
Rewrite Rmult_Rplus_distrl.
Repeat Rewrite Rmult_assoc.
Rewrite <- Rinv_Rmult.
Rewrite Ropp_distr1.
Replace ``2*2`` with ``4``.
Reflexivity.
Ring.
DiscrR.
DiscrR.
Pattern 1 PI; Rewrite double_var.
Unfold Rdiv.
Rewrite Rmult_Rplus_distrl.
Repeat Rewrite Rmult_assoc.
Rewrite <- Rinv_Rmult.
Replace ``2*2`` with ``4``.
Reflexivity.
Ring.
DiscrR.
DiscrR.
Reflexivity.
Case (case_Rabsolu ``(sin (x-y))``); Intro H9.
Assumption.
Generalize (Rle_sym2 ``0`` ``(sin (x-y))`` H9); Clear H9; Intro H9; Generalize (Rlt_Rinv (cos x) HP1); Intro H10; Generalize (Rlt_Rinv (cos y) HP2); Intro H11; Generalize (Rmult_lt_pos (Rinv (cos x)) (Rinv (cos y)) H10 H11); Replace ``/(cos x)*/(cos y)`` with ``/((cos x)*(cos y))``.
Intro H12; Generalize (Rmult_le_pos ``(sin (x-y))`` ``/((cos x)*(cos y))`` H9 (Rlt_le ``0`` ``/((cos x)*(cos y))`` H12)); Intro H13; Elim (Rlt_antirefl ``0`` (Rle_lt_trans ``0`` ``(sin (x-y))*/((cos x)*(cos y))`` ``0`` H13 H3)).
Rewrite Rinv_Rmult.
Reflexivity. 
Assumption.
Assumption.
Qed.

Lemma tan_increasing_1 : (x,y:R) ``-(PI/4)<=x``->``x<=PI/4`` ->``-(PI/4)<=y``->``y<=PI/4``->``x<y``->``(tan x)<(tan y)``.
Intros; Apply Rminus_lt; Generalize PI4_RLT_PI2; Intro H4; Generalize (Rlt_Ropp ``PI/4`` ``PI/2`` H4); Intro H5; Change ``-(PI/2)< -(PI/4)`` in H5; Generalize (cos_gt_0 x (Rlt_le_trans ``-(PI/2)`` ``-(PI/4)`` x H5 H) (Rle_lt_trans x ``PI/4`` ``PI/2`` H0 H4)); Intro HP1; Generalize (cos_gt_0 y (Rlt_le_trans ``-(PI/2)`` ``-(PI/4)`` y H5 H1) (Rle_lt_trans y ``PI/4`` ``PI/2`` H2 H4)); Intro HP2; Generalize (not_sym ``0`` (cos x) (Rlt_not_eq ``0`` (cos x) (cos_gt_0 x (Rlt_le_trans ``-(PI/2)`` ``-(PI/4)`` x H5 H) (Rle_lt_trans x ``PI/4`` ``PI/2`` H0 H4)))); Intro H6; Generalize (not_sym ``0`` (cos y) (Rlt_not_eq ``0`` (cos y) (cos_gt_0 y (Rlt_le_trans ``-(PI/2)`` ``-(PI/4)`` y H5 H1) (Rle_lt_trans y ``PI/4`` ``PI/2`` H2 H4)))); Intro H7; Rewrite (tan_diff x y H6 H7); Generalize (Rlt_Rinv (cos x) HP1); Intro H10; Generalize (Rlt_Rinv (cos y) HP2); Intro H11; Generalize (Rmult_lt_pos (Rinv (cos x)) (Rinv (cos y)) H10 H11); Replace ``/(cos x)*/(cos y)`` with ``/((cos x)*(cos y))``.
Clear H10 H11; Intro H8; Generalize (Rle_Ropp y ``PI/4`` H2); Intro H11; Generalize (Rle_sym2 ``-(PI/4)`` ``-y`` H11); Clear H11; Intro H11; Generalize (Rplus_le ``-(PI/4)`` x ``-(PI/4)`` ``-y`` H H11); Replace ``x+ -y`` with ``x-y``.
Replace ``-(PI/4)+ -(PI/4)`` with ``-(PI/2)``.
Clear H11; Intro H9; Generalize (Rlt_minus x y H3); Clear H3; Intro H3; Clear H H0 H1 H2 H4 H5 HP1 HP2; Generalize PI2_Rlt_PI; Intro H1; Generalize (Rlt_Ropp ``PI/2`` PI H1); Clear H1; Intro H1; Generalize (sin_lt_0_var ``x-y`` (Rlt_le_trans ``-PI`` ``-(PI/2)`` ``x-y`` H1 H9) H3); Intro H2; Generalize (Rlt_anti_monotony ``(sin (x-y))`` ``0`` ``/((cos x)*(cos y))`` H2 H8); Rewrite Rmult_Or; Intro H4; Assumption.
Pattern 1 PI; Rewrite double_var.
Unfold Rdiv.
Rewrite Rmult_Rplus_distrl.
Repeat Rewrite Rmult_assoc.
Rewrite <- Rinv_Rmult.
Replace ``2*2`` with ``4``.
Rewrite Ropp_distr1.
Reflexivity.
Ring.
DiscrR.
DiscrR.
Reflexivity.
Apply Rinv_Rmult; Assumption.
Qed.

Lemma sin_incr_0 : (x,y:R) ``-(PI/2)<=x``->``x<=PI/2``->``-(PI/2)<=y``->``y<=PI/2``->``(sin x)<=(sin y)``->``x<=y``.
Intros; Case (total_order (sin x) (sin y)); Intro H4; [Left; Apply (sin_increasing_0 x y H H0 H1 H2 H4) | Elim H4; Intro H5; [Case (total_order x y); Intro H6; [Left; Assumption | Elim H6; Intro H7; [Right; Assumption | Generalize (sin_increasing_1 y x H1 H2 H H0 H7); Intro H8; Rewrite H5 in H8; Elim (Rlt_antirefl (sin y) H8)]] | Elim (Rlt_antirefl (sin x) (Rle_lt_trans (sin x) (sin y) (sin x) H3 H5))]].
Qed.

Lemma sin_incr_1 : (x,y:R) ``-(PI/2)<=x``->``x<=PI/2``->``-(PI/2)<=y``->``y<=PI/2``->``x<=y``->``(sin x)<=(sin y)``.
Intros; Case (total_order x y); Intro H4; [Left; Apply (sin_increasing_1 x y H H0 H1 H2 H4) | Elim H4; Intro H5; [Case (total_order (sin x) (sin y)); Intro H6; [Left; Assumption | Elim H6; Intro H7; [Right; Assumption | Generalize (sin_increasing_0 y x H1 H2 H H0 H7); Intro H8; Rewrite H5 in H8; Elim (Rlt_antirefl y H8)]] | Elim (Rlt_antirefl x (Rle_lt_trans x y x H3 H5))]].
Qed.

Lemma sin_decr_0 : (x,y:R) ``x<=3*(PI/2)``->``PI/2<=x``->``y<=3*(PI/2)``->``PI/2<=y``-> ``(sin x)<=(sin y)`` -> ``y<=x``.
Intros; Case (total_order (sin x) (sin y)); Intro H4; [Left; Apply (sin_decreasing_0 x y H H0 H1 H2 H4) | Elim H4; Intro H5; [Case (total_order x y); Intro H6; [Generalize (sin_decreasing_1 x y H H0 H1 H2 H6); Intro H8; Rewrite H5 in H8; Elim (Rlt_antirefl (sin y) H8) | Elim H6; Intro H7; [Right; Symmetry; Assumption | Left; Assumption]] | Elim (Rlt_antirefl (sin x) (Rle_lt_trans (sin x) (sin y) (sin x) H3 H5))]].
Qed.

Lemma sin_decr_1 : (x,y:R) ``x<=3*(PI/2)``-> ``PI/2<=x`` -> ``y<=3*(PI/2)``-> ``PI/2<=y`` -> ``x<=y``  -> ``(sin y)<=(sin x)``.
Intros; Case (total_order x y); Intro H4; [Left; Apply (sin_decreasing_1 x y H H0 H1 H2 H4) | Elim H4; Intro H5; [Case (total_order (sin x) (sin y)); Intro H6; [Generalize (sin_decreasing_0 x y H H0 H1 H2 H6); Intro H8; Rewrite H5 in H8; Elim (Rlt_antirefl y H8) | Elim H6; Intro H7; [Right; Symmetry; Assumption | Left; Assumption]] | Elim (Rlt_antirefl x (Rle_lt_trans x y x H3 H5))]].
Qed.

Lemma cos_incr_0 : (x,y:R) ``PI<=x`` -> ``x<=2*PI`` ->``PI<=y`` -> ``y<=2*PI`` -> ``(cos x)<=(cos y)`` -> ``x<=y``.
Intros; Case (total_order (cos x) (cos y)); Intro H4; [Left; Apply (cos_increasing_0 x y H H0 H1 H2 H4) | Elim H4; Intro H5; [Case (total_order x y); Intro H6; [Left; Assumption | Elim H6; Intro H7; [Right; Assumption | Generalize (cos_increasing_1 y x H1 H2 H H0 H7); Intro H8; Rewrite H5 in H8; Elim (Rlt_antirefl (cos y) H8)]] | Elim (Rlt_antirefl (cos x) (Rle_lt_trans (cos x) (cos y) (cos x) H3 H5))]].
Qed.

Lemma cos_incr_1 : (x,y:R) ``PI<=x`` -> ``x<=2*PI`` ->``PI<=y`` -> ``y<=2*PI`` -> ``x<=y`` -> ``(cos x)<=(cos y)``.
Intros; Case (total_order x y); Intro H4; [Left; Apply (cos_increasing_1 x y H H0 H1 H2 H4) | Elim H4; Intro H5; [Case (total_order (cos x) (cos y)); Intro H6; [Left; Assumption | Elim H6; Intro H7; [Right; Assumption | Generalize (cos_increasing_0 y x H1 H2 H H0 H7); Intro H8; Rewrite H5 in H8; Elim (Rlt_antirefl y H8)]] | Elim (Rlt_antirefl x (Rle_lt_trans x y x H3 H5))]].
Qed.

Lemma cos_decr_0 : (x,y:R) ``0<=x``->``x<=PI``->``0<=y``->``y<=PI``->``(cos x)<=(cos y)`` -> ``y<=x``.
Intros; Case (total_order (cos x) (cos y)); Intro H4; [Left; Apply (cos_decreasing_0 x y H H0 H1 H2 H4) | Elim H4; Intro H5; [Case (total_order x y); Intro H6; [Generalize (cos_decreasing_1 x y H H0 H1 H2 H6); Intro H8; Rewrite H5 in H8; Elim (Rlt_antirefl (cos y) H8) | Elim H6; Intro H7; [Right; Symmetry; Assumption | Left; Assumption]] | Elim (Rlt_antirefl (cos x) (Rle_lt_trans (cos x) (cos y) (cos x) H3 H5))]].
Qed.

Lemma cos_decr_1 : (x,y:R) ``0<=x``->``x<=PI``->``0<=y``->``y<=PI``->``x<=y``->``(cos y)<=(cos x)``.
Intros; Case (total_order x y); Intro H4; [Left; Apply (cos_decreasing_1 x y H H0 H1 H2 H4) | Elim H4; Intro H5; [Case (total_order (cos x) (cos y)); Intro H6; [Generalize (cos_decreasing_0 x y H H0 H1 H2 H6); Intro H8; Rewrite H5 in H8; Elim (Rlt_antirefl y H8) | Elim H6; Intro H7; [Right; Symmetry; Assumption | Left; Assumption]] | Elim (Rlt_antirefl x (Rle_lt_trans x y x H3 H5))]].
Qed.

Lemma tan_incr_0 : (x,y:R) ``-(PI/4)<=x``->``x<=PI/4`` ->``-(PI/4)<=y``->``y<=PI/4``->``(tan x)<=(tan y)``->``x<=y``.
Intros; Case (total_order (tan x) (tan y)); Intro H4; [Left; Apply (tan_increasing_0 x y H H0 H1 H2 H4) | Elim H4; Intro H5; [Case (total_order x y); Intro H6; [Left; Assumption | Elim H6; Intro H7; [Right; Assumption | Generalize (tan_increasing_1 y x H1 H2 H H0 H7); Intro H8; Rewrite H5 in H8; Elim (Rlt_antirefl (tan y) H8)]] | Elim (Rlt_antirefl (tan x) (Rle_lt_trans (tan x) (tan y) (tan x) H3 H5))]].
Qed.

Lemma tan_incr_1 : (x,y:R) ``-(PI/4)<=x``->``x<=PI/4`` ->``-(PI/4)<=y``->``y<=PI/4``->``x<=y``->``(tan x)<=(tan y)``.
Intros; Case (total_order x y); Intro H4; [Left; Apply (tan_increasing_1 x y H H0 H1 H2 H4) | Elim H4; Intro H5; [Case (total_order (tan x) (tan y)); Intro H6; [Left; Assumption | Elim H6; Intro H7; [Right; Assumption | Generalize (tan_increasing_0 y x H1 H2 H H0 H7); Intro H8; Rewrite H5 in H8; Elim (Rlt_antirefl y H8)]] | Elim (Rlt_antirefl x (Rle_lt_trans x y x H3 H5))]].
Qed.

(**********)
Lemma sin_eq_0_1 : (x:R) (EXT k:Z | x==(Rmult (IZR k) PI)) -> (sin x)==R0.
Intros.
Elim H; Intros.
Apply (Zcase_sign x0).
Intro.
Rewrite H1 in H0.
Simpl in H0.
Rewrite H0; Rewrite Rmult_Ol; Apply sin_0.
Intro.
Cut `0<=x0`.
Intro.
Elim (IZN x0 H2); Intros.
Rewrite H3 in H0.
Rewrite <- INR_IZR_INZ in H0.
Rewrite H0.
Elim (even_odd_cor x1); Intros.
Elim H4; Intro.
Rewrite H5.
Rewrite mult_INR.
Simpl.
Rewrite <- (Rplus_Ol ``2*(INR x2)*PI``).
Rewrite sin_period.
Apply sin_0.
Rewrite H5.
Rewrite S_INR; Rewrite mult_INR.
Simpl.
Rewrite Rmult_Rplus_distrl.
Rewrite Rmult_1l; Rewrite sin_plus.
Rewrite sin_PI.
Rewrite Rmult_Or.
Rewrite <- (Rplus_Ol ``2*(INR x2)*PI``).
Rewrite sin_period.
Rewrite sin_0; Ring.
Apply le_IZR.
Left; Apply IZR_lt.
Assert H2 := Zgt_iff_lt.
Elim (H2 x0 `0`); Intros.
Apply H3; Assumption.
Intro.
Rewrite H0.
Replace ``(sin ((IZR x0)*PI))`` with ``-(sin (-(IZR x0)*PI))``.
Cut `0<=-x0`.
Intro.
Rewrite <- Ropp_Ropp_IZR.
Elim (IZN `-x0` H2); Intros.
Rewrite H3.
Rewrite <- INR_IZR_INZ.
Elim (even_odd_cor x1); Intros.
Elim H4; Intro.
Rewrite H5.
Rewrite mult_INR.
Simpl.
Rewrite <- (Rplus_Ol ``2*(INR x2)*PI``).
Rewrite sin_period.
Rewrite sin_0; Ring.
Rewrite H5.
Rewrite S_INR; Rewrite mult_INR.
Simpl.
Rewrite Rmult_Rplus_distrl.
Rewrite Rmult_1l; Rewrite sin_plus.
Rewrite sin_PI.
Rewrite Rmult_Or.
Rewrite <- (Rplus_Ol ``2*(INR x2)*PI``).
Rewrite sin_period.
Rewrite sin_0; Ring.
Apply le_IZR.
Apply Rle_anti_compatibility with ``(IZR x0)``.
Rewrite Rplus_Or.
Rewrite Ropp_Ropp_IZR.
Rewrite Rplus_Ropp_r.
Left; Replace R0 with (IZR `0`); [Apply IZR_lt | Reflexivity].
Assumption.
Rewrite <- sin_neg.
Rewrite Ropp_mul1.
Rewrite Ropp_Ropp.
Reflexivity.
Qed.

Lemma sin_eq_0_0 : (x:R) (sin x)==R0 -> (EXT k:Z | x==(Rmult (IZR k) PI)).
Intros.
Assert H0 := (euclidian_division x PI PI_neq0).
Elim H0; Intros q H1.
Elim H1; Intros r H2.
Exists q.
Cut r==R0.
Intro.
Elim H2; Intros H4 _; Rewrite H4; Rewrite H3.
Apply Rplus_Or.
Elim H2; Intros.
Rewrite H3 in H.
Rewrite sin_plus in H.
Cut ``(sin ((IZR q)*PI))==0``.
Intro.
Rewrite H5 in H.
Rewrite Rmult_Ol in H.
Rewrite Rplus_Ol in H.
Assert H6 := (without_div_Od ? ? H).
Elim H6; Intro.
Assert H8 := (sin2_cos2 ``(IZR q)*PI``).
Rewrite H5 in H8; Rewrite H7 in H8.
Rewrite Rsqr_O in H8.
Rewrite Rplus_Or in H8.
Elim R1_neq_R0; Symmetry; Assumption.
Cut r==R0\/``0<r<PI``.
Intro; Elim H8; Intro.
Assumption.
Elim H9; Intros.
Assert H12 := (sin_gt_0 ? H10 H11).
Rewrite H7 in H12; Elim (Rlt_antirefl ? H12).
Rewrite Rabsolu_right in H4.
Elim H4; Intros.
Case (total_order R0 r); Intro.
Right; Split; Assumption.
Elim H10; Intro.
Left; Symmetry; Assumption.
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H8 H11)).
Apply Rle_sym1.
Left; Apply PI_RGT_0.
Apply sin_eq_0_1.
Exists q; Reflexivity.
Qed.

Lemma cos_eq_0_0 : (x:R) (cos x)==R0 -> (EXT k : Z | ``x==(IZR k)*PI+PI/2``). 
Intros x H; Rewrite -> cos_sin in H; Generalize (sin_eq_0_0 (Rplus (Rdiv PI (INR (2))) x) H); Intro H2; Elim H2; Intros x0 H3; Exists (Zminus x0 (inject_nat (S O))); Rewrite <- Z_R_minus; Ring; Rewrite Rmult_sym; Rewrite <- H3; Unfold INR.
Rewrite (double_var ``-PI``); Unfold Rdiv; Ring.
Qed.

Lemma  cos_eq_0_1 : (x:R) (EXT k : Z | ``x==(IZR k)*PI+PI/2``) -> ``(cos x)==0``.
Intros x H1; Rewrite cos_sin; Elim H1; Intros x0 H2; Rewrite H2; Replace ``PI/2+((IZR x0)*PI+PI/2)`` with ``(IZR x0)*PI+PI``.
Rewrite neg_sin; Rewrite <- Ropp_O.
Apply eq_Ropp; Apply sin_eq_0_1; Exists x0; Reflexivity.
Pattern 2 PI; Rewrite (double_var PI); Ring.
Qed.

Lemma sin_eq_O_2PI_0 : (x:R) ``0<=x`` -> ``x<=2*PI`` -> ``(sin x)==0`` -> ``x==0``\/``x==PI``\/``x==2*PI``.
Intros; Generalize (sin_eq_0_0 x H1); Intro.
Elim H2; Intros k0 H3.
Case (total_order PI x); Intro.
Rewrite H3 in H4; Rewrite H3 in H0.
Right; Right.
Generalize (Rlt_monotony_r ``/PI`` ``PI`` ``(IZR k0)*PI`` (Rlt_Rinv ``PI`` PI_RGT_0) H4); Rewrite Rmult_assoc; Repeat Rewrite <- Rinv_r_sym.
Rewrite Rmult_1r; Intro; Generalize (Rle_monotony_r ``/PI`` ``(IZR k0)*PI`` ``2*PI`` (Rlt_le ``0`` ``/PI`` (Rlt_Rinv ``PI`` PI_RGT_0)) H0); Repeat Rewrite Rmult_assoc; Repeat Rewrite <- Rinv_r_sym.
Repeat Rewrite Rmult_1r; Intro; Generalize (Rlt_compatibility (IZR `-2`) ``1`` (IZR k0) H5); Rewrite <- plus_IZR.
Replace ``(IZR (NEG (xO xH)))+1`` with ``-1``.
Intro; Generalize (Rle_compatibility (IZR `-2`) (IZR k0) ``2`` H6); Rewrite <- plus_IZR.
Replace ``(IZR (NEG (xO xH)))+2`` with ``0``.
Intro; Cut ``-1 < (IZR (Zplus (NEG (xO xH)) k0)) < 1``.
Intro; Generalize (one_IZR_lt1 (Zplus (NEG (xO xH)) k0) H9); Intro.
Cut k0=`2`.
Intro; Rewrite H11 in H3; Rewrite H3; Simpl.
Reflexivity.
Rewrite <- (Zplus_inverse_l `2`) in H10; Generalize (Zsimpl_plus_l `-2` k0 `2` H10); Intro; Assumption.
Split.
Assumption.
Apply Rle_lt_trans with ``0``.
Assumption.
Apply Rlt_R0_R1.
Simpl; Ring.
Simpl; Ring.
Apply PI_neq0.
Apply PI_neq0.
Elim H4; Intro.
Right; Left.
Symmetry; Assumption.
Left.
Rewrite H3 in H5; Rewrite H3 in H; Generalize (Rlt_monotony_r ``/PI``  ``(IZR k0)*PI`` PI (Rlt_Rinv ``PI`` PI_RGT_0) H5); Rewrite Rmult_assoc; Repeat Rewrite <- Rinv_r_sym.
Rewrite Rmult_1r; Intro; Generalize (Rle_monotony_r ``/PI`` ``0`` ``(IZR k0)*PI`` (Rlt_le ``0`` ``/PI`` (Rlt_Rinv ``PI`` PI_RGT_0)) H); Repeat Rewrite Rmult_assoc; Repeat Rewrite <- Rinv_r_sym.
Rewrite Rmult_1r; Rewrite Rmult_Ol; Intro.
Cut ``-1 < (IZR (k0)) < 1``.
Intro; Generalize (one_IZR_lt1 k0 H8); Intro; Rewrite H9 in H3; Rewrite H3; Simpl; Apply Rmult_Ol.
Split.
Apply Rlt_le_trans with ``0``.
Rewrite <- Ropp_O; Apply Rgt_Ropp; Apply Rlt_R0_R1.
Assumption.
Assumption.
Apply PI_neq0.
Apply PI_neq0.
Qed.

Lemma sin_eq_O_2PI_1 : (x:R) ``0<=x`` -> ``x<=2*PI`` -> ``x==0``\/``x==PI``\/``x==2*PI`` -> ``(sin x)==0``.
Intros x H1 H2 H3; Elim H3; Intro H4; [ Rewrite H4; Rewrite -> sin_0; Reflexivity | Elim H4; Intro H5; [Rewrite H5; Rewrite -> sin_PI; Reflexivity | Rewrite H5; Rewrite -> sin_2PI; Reflexivity]].
Qed.

Lemma cos_eq_0_2PI_0 : (x:R) ``R0<=x`` -> ``x<=2*PI`` -> ``(cos x)==0`` -> ``x==(PI/2)``\/``x==3*(PI/2)``.
Intros; Case (total_order x ``3*(PI/2)``); Intro.
Rewrite cos_sin in H1.
Cut ``0<=PI/2+x``.
Cut ``PI/2+x<=2*PI``.
Intros; Generalize (sin_eq_O_2PI_0 ``PI/2+x`` H4 H3 H1); Intros.
Decompose [or] H5.
Generalize (Rle_compatibility ``PI/2`` ``0`` x H); Rewrite Rplus_Or; Rewrite H6; Intro.
Elim (Rlt_antirefl ``0`` (Rlt_le_trans ``0`` ``PI/2`` ``0`` PI2_RGT_0 H7)).
Left.
Generalize (Rplus_plus_r ``-(PI/2)`` ``PI/2+x`` PI H7).
Replace ``-(PI/2)+(PI/2+x)`` with x.
Replace ``-(PI/2)+PI`` with ``PI/2``.
Intro; Assumption.
Pattern 3 PI; Rewrite (double_var PI); Ring.
Ring.
Right.
Generalize (Rplus_plus_r ``-(PI/2)`` ``PI/2+x`` ``2*PI`` H7).
Replace ``-(PI/2)+(PI/2+x)`` with x.
Replace ``-(PI/2)+2*PI`` with ``3*(PI/2)``.
Intro; Assumption.
Rewrite double; Pattern 3 4 PI; Rewrite (double_var PI); Ring.
Ring.
Left; Replace ``2*PI`` with ``PI/2+3*(PI/2)``.
Apply Rlt_compatibility; Assumption.
Rewrite (double PI); Pattern 3 4 PI; Rewrite (double_var PI); Ring.
Apply ge0_plus_ge0_is_ge0.
Left; Unfold Rdiv; Apply Rmult_lt_pos.
Apply PI_RGT_0.
Apply Rlt_Rinv; Sup0. 
Assumption.
Elim H2; Intro.
Right; Assumption.
Generalize (cos_eq_0_0 x H1); Intro; Elim H4; Intros k0 H5.
Rewrite H5 in H3; Rewrite H5 in H0; Generalize (Rlt_compatibility ``-(PI/2)`` ``3*PI/2`` ``(IZR k0)*PI+PI/2`` H3); Generalize (Rle_compatibility ``-(PI/2)`` ``(IZR k0)*PI+PI/2`` ``2*PI`` H0).
Replace ``-(PI/2)+3*PI/2`` with PI.
Replace ``-(PI/2)+((IZR k0)*PI+PI/2)`` with ``(IZR k0)*PI``.
Replace ``-(PI/2)+2*PI`` with ``3*(PI/2)``.
Intros; Generalize (Rlt_monotony ``/PI`` ``PI`` ``(IZR k0)*PI`` (Rlt_Rinv PI PI_RGT_0) H7); Generalize (Rle_monotony ``/PI`` ``(IZR k0)*PI`` ``3*(PI/2)`` (Rlt_le ``0`` ``/PI`` (Rlt_Rinv PI PI_RGT_0)) H6).
Replace ``/PI*((IZR k0)*PI)`` with (IZR k0).
Replace ``/PI*(3*PI/2)`` with ``3*/2``.
Rewrite <- Rinv_l_sym.
Intros; Generalize (Rlt_compatibility (IZR `-2`) ``1`` (IZR k0) H9); Rewrite <- plus_IZR.
Replace ``(IZR (NEG (xO xH)))+1`` with ``-1``.
Intro; Generalize (Rle_compatibility (IZR `-2`) (IZR k0) ``3*/2`` H8); Rewrite <- plus_IZR.
Replace ``(IZR (NEG (xO xH)))+2`` with ``0``.
Intro; Cut `` -1 < (IZR (Zplus (NEG (xO xH)) k0)) < 1``.
Intro; Generalize (one_IZR_lt1 (Zplus (NEG (xO xH)) k0) H12); Intro.
Cut k0=`2`.
Intro; Rewrite H14 in H8.
Assert Hyp : ``0<2``.
Sup0.
Generalize (Rle_monotony ``2`` ``(IZR (POS (xO xH)))`` ``3*/2`` (Rlt_le ``0`` ``2`` Hyp) H8); Simpl.
Replace ``2*2`` with ``4``.
Replace ``2*(3*/2)`` with ``3``.
Intro; Cut ``3<4``.
Intro; Elim (Rlt_antirefl ``3`` (Rlt_le_trans ``3`` ``4`` ``3`` H16 H15)).
Generalize (Rlt_compatibility ``3`` ``0`` ``1`` Rlt_R0_R1); Rewrite Rplus_Or.
Replace ``3+1`` with ``4``.
Intro; Assumption.
Ring.
Symmetry; Rewrite <- Rmult_assoc; Apply Rinv_r_simpl_m.
DiscrR.
Ring.
Rewrite <- (Zplus_inverse_l `2`) in H13; Generalize (Zsimpl_plus_l `-2` k0 `2` H13); Intro; Assumption.
Split.
Assumption.
Apply Rle_lt_trans with ``(IZR (NEG (xO xH)))+3*/2``.
Assumption.
Simpl; Replace ``-2+3*/2`` with ``-(1*/2)``.
Apply Rlt_trans with ``0``.
Rewrite <- Ropp_O; Apply Rlt_Ropp.
Apply Rmult_lt_pos; [Apply Rlt_R0_R1 | Apply Rlt_Rinv; Sup0].
Apply Rlt_R0_R1.
Rewrite Rmult_1l; Apply r_Rmult_mult with ``2``.
Rewrite Ropp_mul3; Rewrite <- Rinv_r_sym.
Rewrite Rmult_Rplus_distr; Rewrite <- Rmult_assoc; Rewrite Rinv_r_simpl_m.
Ring.
DiscrR.
DiscrR.
DiscrR.
Simpl; Ring.
Simpl; Ring.
Apply PI_neq0.
Unfold Rdiv; Pattern 1 ``3``; Rewrite (Rmult_sym ``3``); Repeat Rewrite <- Rmult_assoc; Rewrite <- Rinv_l_sym.
Rewrite Rmult_1l; Apply Rmult_sym.
Apply PI_neq0.
Symmetry; Rewrite (Rmult_sym ``/PI``); Rewrite Rmult_assoc; Rewrite <- Rinv_r_sym.
Apply Rmult_1r.
Apply PI_neq0.
Rewrite double; Pattern 3 4 PI; Rewrite double_var; Ring.
Ring.
Pattern 1 PI; Rewrite double_var; Ring.
Qed.

Lemma  cos_eq_0_2PI_1 : (x:R) ``0<=x`` -> ``x<=2*PI`` -> ``x==PI/2``\/``x==3*(PI/2)`` -> ``(cos x)==0``.
Intros x H1 H2 H3; Elim H3; Intro H4; [ Rewrite H4; Rewrite -> cos_PI2; Reflexivity | Rewrite H4; Rewrite -> cos_3PI2; Reflexivity ].
Qed.
