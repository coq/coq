(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

Require ZArith_base.
Require Classical_Prop.
Require DiscrR.
Require Rbase.
Require R_sqr.
Require Rfunctions.
Require Rsigma.
Require Rlimit.
Require Export Rtrigo_def.

Lemma PI_neq0 : ~``PI==0``.
Red; Intro.
Generalize PI_RGT_0; Intro; Rewrite H in H0.
Elim (Rlt_antirefl ``0`` H0).
Qed.

(**********)
Lemma sin2_cos2 : (x:R) ``(Rsqr (sin x)) + (Rsqr (cos x))==1``.
Intro; Unfold Rsqr; Rewrite Rplus_sym; Rewrite <- (cos_minus x x); Unfold Rminus; Rewrite Rplus_Ropp_r; Apply cos_0.
Qed.


(**********)
Definition tan [x:R] : R := ``(sin x)/(cos x)``.

Lemma Ropp_mul3 : (r1,r2:R) ``r1*(-r2) == -(r1*r2)``.
Intros; Rewrite <- Ropp_mul1; Ring.
Qed.

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

Lemma cos2 : (x:R) ``(Rsqr (cos x))==1-(Rsqr (sin x))``.
Intro x; Generalize (sin2_cos2 x); Intro H1; Rewrite <- H1; Unfold Rminus; Rewrite <- (Rplus_sym (Rsqr (cos x))); Rewrite Rplus_assoc; Rewrite Rplus_Ropp_r; Symmetry; Apply Rplus_Or.
Qed.

Lemma sin2 : (x:R) ``(Rsqr (sin x))==1-(Rsqr (cos x))``.
Intro x; Generalize (cos2 x); Intro H1; Rewrite -> H1.
Unfold Rminus; Rewrite Ropp_distr1; Rewrite <- Rplus_assoc; Rewrite Rplus_Ropp_r; Rewrite Rplus_Ol; Symmetry; Apply Ropp_Ropp.
Qed.

Lemma aze : ``2<>0``.
DiscrR.
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

Lemma sin_0 : ``(sin 0)==0``.
Apply Rsqr_eq_0; Rewrite sin2; Rewrite cos_0; SqRing.
Qed.

Lemma sin_neg : (x:R) ``(sin (-x))==-(sin x)``.
Intro x; Replace ``-x`` with ``0-x``; Ring; Replace `` -(sin x)`` with ``(sin 0)*(cos x)-(cos 0)*(sin x)``; [ Apply sin_minus |Rewrite -> sin_0; Rewrite -> cos_0; Ring ].
Qed.

Lemma cos_neg : (x:R) ``(cos (-x))==(cos x)``.
Intro x; Replace ``(-x)`` with ``(0-x)``; Ring; Replace ``(cos x)`` with ``(cos 0)*(cos x)+(sin 0)*(sin x)``; [ Apply cos_minus | Rewrite -> cos_0; Rewrite -> sin_0; Ring ].
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

Lemma cos_PI2 : ``(cos (PI/2))==0``.
Apply Rsqr_eq_0; Rewrite cos2; Rewrite sin_PI2; Rewrite Rsqr_1; Unfold Rminus; Apply Rplus_Ropp_r.
Qed.

Lemma sin_PI : ``(sin PI)==0``.
Replace ``PI`` with ``2*(PI/2)``.
Rewrite -> sin_2a; Rewrite -> sin_PI2; Rewrite -> cos_PI2; Ring.
Unfold Rdiv.
Repeat Rewrite <- Rmult_assoc; Apply Rinv_r_simpl_m.
Apply aze.
Qed.

Lemma cos_PI : ``(cos PI)==(-1)``.
Replace ``PI`` with ``2*(PI/2)``.
Rewrite -> cos_2a; Rewrite -> sin_PI2; Rewrite -> cos_PI2.
Rewrite Rmult_Ol; Rewrite Rmult_1r.
Apply Rminus_Ropp.
Unfold Rdiv.
Repeat Rewrite <- Rmult_assoc.
Apply Rinv_r_simpl_m.
Apply aze.
Qed.

Lemma tan_PI : ``(tan PI)==0``.
Unfold tan; Rewrite -> sin_PI; Rewrite -> cos_PI.
Unfold Rdiv; Apply Rmult_Ol. 
Qed.

Lemma sin_3PI2 : ``(sin (3*(PI/2)))==(-1)``.
Replace ``3*(PI/2)`` with ``PI+(PI/2)``.
Rewrite -> sin_plus; Rewrite -> sin_PI; Rewrite -> cos_PI; Rewrite -> sin_PI2; Ring.
Pattern 1 PI; Rewrite (double_var PI).
Ring.
Qed.

Lemma cos_3PI2 : ``(cos (3*(PI/2)))==0``.
Replace ``3*(PI/2)`` with ``PI+(PI/2)``.
Rewrite -> cos_plus; Rewrite -> sin_PI; Rewrite -> cos_PI2; Ring.
Pattern 1 PI; Rewrite (double_var PI).
Ring.
Qed.

Lemma sin_2PI : ``(sin (2*PI))==0``.
Rewrite -> sin_2a; Rewrite -> sin_PI.
Rewrite Rmult_Or.
Rewrite Rmult_Ol.
Reflexivity.
Qed.

Lemma cos_2PI : ``(cos (2*PI))==1``.
Rewrite -> cos_2a; Rewrite -> sin_PI; Rewrite -> cos_PI; Rewrite Rmult_Or; Rewrite minus_R0; Rewrite Ropp_mul1; Rewrite Rmult_1l; Apply Ropp_Ropp.
Qed.

Lemma tan_2PI : ``(tan (2*PI))==0``.
Unfold tan; Rewrite sin_2PI; Unfold Rdiv; Apply Rmult_Ol.
Qed.

Lemma neg_cos : (x:R) ``(cos (x+PI))==-(cos x)``.
Intro x; Rewrite -> cos_plus; Rewrite -> sin_PI; Rewrite -> cos_PI; Rewrite Rmult_Or; Rewrite minus_R0; Rewrite Ropp_mul3; Rewrite Rmult_1r; Reflexivity.
Qed.

Lemma neg_sin : (x:R) ``(sin (x+PI))==-(sin x)``.
Intro x; Rewrite -> sin_plus; Rewrite -> sin_PI; Rewrite -> cos_PI.
Rewrite Rmult_Or; Rewrite Rplus_Or; Rewrite Ropp_mul3; Rewrite Rmult_1r; Reflexivity.
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

Lemma sin_cos : (x:R) ``(sin x)==-(cos (PI/2+x))``.
Intro x; Rewrite -> cos_plus; Rewrite -> sin_PI2; Rewrite -> cos_PI2; Ring.
Qed.

Axiom sin_eq_0 : (x:R) (sin x)==R0 <-> (EXT k:Z | x==(Rmult (IZR k) PI)).

Lemma sin_eq_0_0 : (x:R) (sin x)==R0 -> (EXT k:Z | x==(Rmult (IZR k) PI)).
Intros; Elim (sin_eq_0 x); Intros; Apply  (H0 H).
Qed.

Lemma sin_eq_0_1 : (x:R) (EXT k:Z | x==(Rmult (IZR k) PI)) -> (sin x)==R0.
Intros; Elim (sin_eq_0 x); Intros; Apply  (H1 H).
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

Lemma PI2_RGT_0 : ``0<PI/2``.
Cut ~(O=(2)); [Intro H; Generalize (lt_INR_0 (2) (neq_O_lt (2) H)); Rewrite INR_eq_INR2; Unfold INR2; Intro H1; Generalize (Rmult_lt_pos PI (Rinv ``2``) PI_RGT_0 (Rlt_Rinv ``2`` H1)); Intro H2; Assumption | Discriminate].
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
Apply Rlt_Rinv; Apply Rgt_2_0. 
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
Generalize (Rle_monotony ``2`` ``(IZR (POS (xO xH)))`` ``3*/2`` (Rlt_le ``0`` ``2`` Rgt_2_0) H8); Simpl.
Replace ``2*2`` with ``4``.
Replace ``2*(3*/2)`` with ``3``.
Intro; Cut ``3<4``.
Intro; Elim (Rlt_antirefl ``3`` (Rlt_le_trans ``3`` ``4`` ``3`` H16 H15)).
Generalize (Rlt_compatibility ``3`` ``0`` ``1`` Rlt_R0_R1); Rewrite Rplus_Or.
Replace ``3+1`` with ``4``.
Intro; Assumption.
Ring.
Symmetry; Rewrite <- Rmult_assoc; Apply Rinv_r_simpl_m.
Apply aze.
Ring.
Rewrite <- (Zplus_inverse_l `2`) in H13; Generalize (Zsimpl_plus_l `-2` k0 `2` H13); Intro; Assumption.
Split.
Assumption.
Apply Rle_lt_trans with ``(IZR (NEG (xO xH)))+3*/2``.
Assumption.
Simpl; Replace ``-2+3*/2`` with ``-(1*/2)``.
Apply Rlt_trans with ``0``.
Rewrite <- Ropp_O; Apply Rlt_Ropp.
Apply Rmult_lt_pos; [Apply Rlt_R0_R1 | Apply Rlt_Rinv; Apply Rgt_2_0].
Apply Rlt_R0_R1.
Rewrite Rmult_1l; Apply r_Rmult_mult with ``2``.
Rewrite Ropp_mul3; Rewrite <- Rinv_r_sym.
Rewrite Rmult_Rplus_distr; Rewrite <- Rmult_assoc; Rewrite Rinv_r_simpl_m.
Ring.
Apply aze.
Apply aze.
Apply aze.
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
Intro; Case (total_order_Rle ``-1`` (cos x)); Intro.
Case (total_order_Rle (cos x) ``1``); Intro.
Split; Assumption.
Cut ``1<(cos x)``.
Intro; Generalize (Rsqr_incrst_1 ``1`` (cos x) H (Rlt_le ``0`` ``1`` Rlt_R0_R1) (Rlt_le ``0`` (cos x) (Rlt_trans ``0`` ``1`` (cos x) Rlt_R0_R1 H))); Rewrite Rsqr_1; Intro; Rewrite cos2 in H0; Unfold Rminus in H0; Generalize (Rlt_compatibility ``-1`` ``1`` ``1+ -(Rsqr (sin x))`` H0); Repeat Rewrite <- Rplus_assoc; Repeat Rewrite Rplus_Ropp_l; Rewrite Rplus_Ol; Intro; Rewrite <- Ropp_O in H1; Generalize (Rlt_Ropp ``-0`` ``-(Rsqr (sin x))`` H1); Repeat Rewrite Ropp_Ropp; Intro; Generalize (pos_Rsqr (sin x)); Intro; Elim (Rlt_antirefl ``0`` (Rle_lt_trans ``0`` (Rsqr (sin x)) ``0`` H3 H2)).
Auto with real.
Cut ``(cos x)< -1``.
Intro; Generalize (Rlt_Ropp (cos x) ``-1`` H); Rewrite Ropp_Ropp; Clear H; Intro; Generalize (Rsqr_incrst_1 ``1`` ``-(cos x)`` H (Rlt_le ``0`` ``1`` Rlt_R0_R1) (Rlt_le ``0`` ``-(cos x)`` (Rlt_trans ``0`` ``1`` ``-(cos x)`` Rlt_R0_R1 H))); Rewrite Rsqr_1; Intro; Rewrite <- Rsqr_neg in H0; Rewrite cos2 in H0; Unfold Rminus in H0; Generalize (Rlt_compatibility ``-1`` ``1`` ``1+ -(Rsqr (sin x))`` H0); Repeat Rewrite <- Rplus_assoc; Repeat Rewrite Rplus_Ropp_l; Rewrite Rplus_Ol; Intro; Rewrite <- Ropp_O in H1; Generalize (Rlt_Ropp ``-0`` ``-(Rsqr (sin x))`` H1); Repeat Rewrite Ropp_Ropp; Intro; Generalize (pos_Rsqr (sin x)); Intro; Elim (Rlt_antirefl ``0`` (Rle_lt_trans ``0`` (Rsqr (sin x)) ``0`` H3 H2)).
Auto with real.
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

Definition sin_term [a:R] : nat->R := [i:nat] ``(pow (-1) i)*(pow a (plus (mult (S (S O)) i) (S O)))/(INR (fact (plus (mult (S (S O)) i) (S O))))``.

Definition cos_term [a:R] : nat->R := [i:nat] ``(pow (-1) i)*(pow a (mult (S (S O)) i))/(INR (fact (mult (S (S O)) i)))``.

Definition sin_approx [a:R;n:nat] : R := (sum_f_R0 (sin_term a) n).

Definition cos_approx [a:R;n:nat] : R := (sum_f_R0 (cos_term a) n).

Axiom sin_bound : (a:R)(n:nat) ``0<=a``->``a<=PI``->``(sin_approx a (plus (mult (S (S O)) n) (S O)))<=(sin a)<=(sin_approx a (mult (S (S O)) (plus n (S O))))``.

Axiom cos_bound : (a:R)(n:nat) ``-PI/2<=a``->``a<=PI/2``->``(cos_approx a (plus (mult (S (S O)) n) (S O)))<=(cos a)<=(cos_approx a (mult ((S (S O))) (plus n (S O))))``.

Definition sin_lb [a:R] : R := (sin_approx a (3)).
Definition sin_ub [a:R] : R := (sin_approx a (4)).
Definition cos_lb [a:R] : R := (cos_approx a (3)).
Definition cos_ub [a:R] : R := (cos_approx a (4)).

Axiom sin_lb_gt_0 : (a:R) ``0<a``->``a<=PI/2``->``0<(sin_lb a)``.

Lemma SIN : (a:R) ``0<=a`` -> ``a<=PI`` -> ``(sin_lb a)<=(sin a)<=(sin_ub a)``.
Intros; Unfold sin_lb sin_ub; Apply (sin_bound a (S O) H H0).
Qed.

Lemma COS : (a:R) ``-PI/2<=a`` -> ``a<=PI/2`` -> ``(cos_lb a)<=(cos a)<=(cos_ub a)``.
Intros; Unfold cos_lb cos_ub; Apply (cos_bound a (S O) H H0).
Qed.

(**********)
Lemma PI4_RGT_0 : ``0<PI/4``.
Cut ~(O=(4)); [Intro H; Generalize (lt_INR_0 (4) (neq_O_lt (4) H)); Rewrite INR_eq_INR2; Unfold INR2; Intro H1; Generalize (Rmult_lt_pos PI (Rinv ``4``) PI_RGT_0 (Rlt_Rinv ``4`` H1)); Intro H2; Assumption | Discriminate].
Qed.

Lemma PI6_RGT_0 : ``0<PI/6``.
Cut ~(O=(6)); [Intro H; Generalize (lt_INR_0 (6) (neq_O_lt (6) H)); Rewrite INR_eq_INR2; Unfold INR2; Intro H1; Generalize (Rmult_lt_pos PI (Rinv ``6``) PI_RGT_0 (Rlt_Rinv ``6`` H1)); Intro H2; Assumption | Discriminate].
Qed.

Lemma _PI2_RLT_0 : ``-(PI/2)<0``.
Rewrite <- Ropp_O; Apply Rlt_Ropp1; Apply PI2_RGT_0.
Qed.

Lemma PI4_RLT_PI2 : ``PI/4<PI/2``.
Cut ~(O=(2)). 
Intro H; Cut ~(O=(1)).
Intro H0; Generalize (lt_INR_0 (2) (neq_O_lt (2) H)); Rewrite INR_eq_INR2; Unfold INR2; Intro H1; Generalize (Rlt_compatibility ``2`` ``0`` ``2`` H1); Rewrite Rplus_sym.
Rewrite Rplus_Ol.
Replace ``2+2`` with ``4``.
Intro H2; Generalize (lt_INR_0 (1) (neq_O_lt (1) H0)); Unfold INR; Intro H3; Generalize (Rlt_compatibility ``1`` ``0`` ``1`` H3); Rewrite Rplus_sym.
Rewrite Rplus_Ol. 
Clear H3; Intro H3; Generalize (Rlt_Rinv_R1 ``2`` ``4`` (Rlt_le ``1`` ``2`` H3) H2); Intro H4; Generalize (Rlt_monotony PI (Rinv ``4``) (Rinv ``2``) PI_RGT_0 H4); Intro H5; Assumption.
Ring.
Discriminate.
Discriminate.
Qed.

Lemma PI6_RLT_PI2 : ``PI/6<PI/2``.
Cut ~(O=(4)); [ Intro H; Cut ~(O=(1)); [Intro H0; Generalize (lt_INR_0 (4) (neq_O_lt (4) H)); Rewrite INR_eq_INR2; Unfold INR2; Intro H1; Generalize (Rlt_compatibility ``2`` ``0`` ``4`` H1); Rewrite Rplus_sym; Rewrite Rplus_Ol; Replace ``2+4`` with ``6``; [Intro H2; Generalize (lt_INR_0 (1) (neq_O_lt (1) H0)); Rewrite INR_eq_INR2; Unfold INR2; Intro H3; Generalize (Rlt_compatibility ``1`` ``0`` ``1`` H3); Rewrite Rplus_sym; Rewrite Rplus_Ol; Clear H3; Intro H3; Generalize (Rlt_Rinv_R1 ``2`` ``6`` (Rlt_le ``1`` ``2`` H3) H2); Intro H4; Generalize (Rlt_monotony PI (Rinv ``6``) (Rinv ``2``) PI_RGT_0 H4); Intro H5; Assumption | Ring] | Discriminate] | Discriminate ].
Qed.

Lemma sqrt2_neq_0 : ~``(sqrt 2)==0``.
Generalize (Rlt_le ``0`` ``2`` Rgt_2_0); Intro H1; Red; Intro H2; Generalize (sqrt_eq_0 ``2`` H1 H2); Intro H; Absurd ``2==0``; [ DiscrR | Assumption].
Qed.

Lemma R1_sqrt2_neq_0 : ~``1/(sqrt 2)==0``.
Generalize (Rinv_neq_R0 ``(sqrt 2)`` sqrt2_neq_0); Intro H; Generalize (prod_neq_R0 ``1`` ``(Rinv (sqrt 2))`` R1_neq_R0 H); Intro H0; Assumption.
Qed.

Lemma sqrt3_2_neq_0 : ~``2*(sqrt 3)==0``.
Apply prod_neq_R0; [DiscrR | Generalize (Rlt_le ``0`` ``3`` Rgt_3_0); Intro H1; Red; Intro H2; Generalize (sqrt_eq_0 ``3`` H1 H2); Intro H; Absurd ``3==0``; [ DiscrR | Assumption]].
Qed.

Lemma Rlt_sqrt2_0 : ``0<(sqrt 2)``.
Generalize (sqrt_positivity ``2`` (Rlt_le ``0`` ``2`` Rgt_2_0)); Intro H1; Elim H1; Intro H2; [Assumption | Absurd ``0 == (sqrt 2)``; [Apply not_sym; Apply sqrt2_neq_0 | Assumption]].
Qed.

Lemma Rlt_sqrt3_0 : ``0<(sqrt 3)``.
Cut ~(O=(1)); [Intro H0; Generalize (Rlt_le ``0`` ``2`` Rgt_2_0); Intro H1; Generalize (Rlt_le ``0`` ``3`` Rgt_3_0); Intro H2; Generalize (lt_INR_0 (1) (neq_O_lt (1) H0)); Unfold INR; Intro H3; Generalize (Rlt_compatibility ``2`` ``0`` ``1`` H3); Rewrite Rplus_sym; Rewrite Rplus_Ol; Replace ``2+1`` with ``3``; [Intro H4; Generalize (sqrt_lt_1 ``2`` ``3`` H1 H2 H4); Clear H3; Intro H3; Apply (Rlt_trans ``0`` ``(sqrt 2)`` ``(sqrt 3)`` Rlt_sqrt2_0 H3) | Ring] | Discriminate].
Qed.

Lemma PI2_Rlt_PI : ``PI/2<PI``.
Cut ~(O=(1)).
Intro H0; Generalize (lt_INR_0 (1) (neq_O_lt (1) H0)); Unfold INR; Intro H1; Generalize (Rlt_compatibility ``1`` ``0`` ``1`` H1); Rewrite Rplus_sym; Rewrite Rplus_Ol; Intro H2; Cut ``1<=1``.
Intro H3; Generalize (Rlt_Rinv_R1 ``1`` ``2`` H3 H2); Intro H4; Generalize (Rlt_monotony PI (Rinv ``2``) (Rinv ``1``) PI_RGT_0 H4).
Rewrite Rinv_R1. 
Rewrite Rmult_1r.
Intro; Assumption.
Right; Reflexivity.
Discriminate.
Qed.

Theorem sin_gt_0 : (x:R) ``0<x`` -> ``x<PI`` -> ``0<(sin x)``.
Intros; Elim (SIN x (Rlt_le R0 x H) (Rlt_le x PI H0)); Intros H1 _; Case (total_order x ``PI/2``); Intro H2.
Generalize (sin_lb_gt_0 x H (Rlt_le x ``PI/2`` H2)); Intro H3; Apply (Rlt_le_trans ``0`` (sin_lb x) (sin x) H3 H1).
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
Unfold Rdiv Rminus; Rewrite Rmult_Rplus_distrl; Ring.
Rewrite (Rmult_sym ``/2``); Repeat Rewrite <- Ropp_mul1; Assert H := (double_var ``-q``); Unfold Rdiv in H; Symmetry ; Assumption.
Unfold Rdiv Rminus; Rewrite Rmult_Rplus_distrl; Ring; Rewrite (Rmult_sym ``/2``); Repeat Rewrite <- Ropp_mul1; Assert H := (double_var ``p``); Unfold Rdiv in H; Symmetry ; Assumption.
Qed.

Lemma form2 : (p,q:R) ``(cos p)-(cos q)==-2*(sin ((p-q)/2))*(sin ((p+q)/2))``.
Intros p q; Pattern 1 p; Replace ``p`` with ``(p-q)/2+(p+q)/2``.
Rewrite <- (cos_neg q); Replace``-q`` with ``(p-q)/2-(p+q)/2``.
Rewrite cos_plus; Rewrite cos_minus; Ring.
Unfold Rdiv Rminus; Rewrite Rmult_Rplus_distrl; Ring; Rewrite (Rmult_sym ``/2``); Repeat Rewrite <- Ropp_mul1; Assert H := (double_var ``-q``); Unfold Rdiv in H; Symmetry ; Assumption.
Unfold Rdiv Rminus; Rewrite Rmult_Rplus_distrl; Ring; Rewrite (Rmult_sym ``/2``); Repeat Rewrite <- Ropp_mul1; Assert H := (double_var ``p``); Unfold Rdiv in H; Symmetry ; Assumption.
Qed.

Lemma form3 : (p,q:R) ``(sin p)+(sin q)==2*(cos ((p-q)/2))*(sin ((p+q)/2))``.
Intros p q; Pattern 1 p; Replace ``p`` with ``(p-q)/2+(p+q)/2``.
Pattern 3 q; Replace ``q`` with ``(p+q)/2-(p-q)/2``.
Rewrite sin_plus; Rewrite sin_minus; Ring.
Unfold Rdiv Rminus. 
Rewrite Rmult_Rplus_distrl.
Ring.
Rewrite (Rmult_sym ``/2``).
Repeat Rewrite <- Ropp_mul1.
Assert H := (double_var ``q``).
Unfold Rdiv in H; Symmetry ; Assumption.
Unfold Rdiv Rminus. 
Rewrite Rmult_Rplus_distrl.
Ring.
Rewrite (Rmult_sym ``/2``).
Repeat Rewrite <- Ropp_mul1.
Assert H := (double_var ``p``).
Unfold Rdiv in H; Symmetry ; Assumption.
Qed.

Lemma form4 : (p,q:R) ``(sin p)-(sin q)==2*(cos ((p+q)/2))*(sin ((p-q)/2))``.
Intros p q; Pattern 1 p; Replace ``p`` with ``(p-q)/2+(p+q)/2``.
Pattern 3 q; Replace ``q`` with ``(p+q)/2-(p-q)/2``.
Rewrite sin_plus; Rewrite sin_minus; Ring.
Unfold Rdiv Rminus. 
Rewrite Rmult_Rplus_distrl.
Ring.
Rewrite (Rmult_sym ``/2``).
Repeat Rewrite <- Ropp_mul1.
Assert H := (double_var ``q``).
Unfold Rdiv in H; Symmetry ; Assumption.
Unfold Rdiv Rminus. 
Rewrite Rmult_Rplus_distrl.
Ring.
Rewrite (Rmult_sym ``/2``).
Repeat Rewrite <- Ropp_mul1.
Assert H := (double_var ``p``).
Unfold Rdiv in H; Symmetry ; Assumption.
Qed.

Lemma sin_increasing_0 : (x,y:R) ``-(PI/2)<=x``->``x<=PI/2``->``-(PI/2)<=y``->``y<=PI/2``->``(sin x)<(sin y)``->``x<y``.
Intros; Cut ``(sin ((x-y)/2))<0``.
Intro H4; Case (total_order ``(x-y)/2`` ``0``); Intro H5.
Generalize (Rlt_monotony ``2`` ``(x-y)/2`` ``0`` Rgt_2_0 H5).
Unfold Rdiv.
Rewrite <- Rmult_assoc.
Rewrite Rinv_r_simpl_m.
Rewrite Rmult_Or.
Clear H5; Intro H5; Apply Rminus_lt; Assumption.
Apply aze.
Elim H5; Intro H6.
Rewrite H6 in H4; Rewrite sin_0 in H4; Elim (Rlt_antirefl ``0`` H4).
Change ``0<(x-y)/2`` in H6; Generalize (Rle_Ropp ``-(PI/2)`` y H1).
Rewrite Ropp_Ropp.
Intro H7; Generalize (Rle_sym2 ``-y`` ``PI/2`` H7); Clear H7; Intro H7; Generalize (Rplus_le x ``PI/2`` ``-y`` ``PI/2`` H0 H7).
Rewrite <- double_var.
Intro H8; Generalize (Rle_monotony ``(Rinv 2)`` ``x-y`` PI (Rlt_le ``0`` ``/2`` (Rlt_Rinv ``2`` Rgt_2_0)) H8).
Repeat Rewrite (Rmult_sym ``/2``). 
Intro H9; Generalize (sin_gt_0 ``(x-y)/2`` H6 (Rle_lt_trans ``(x-y)/2`` ``PI/2`` PI H9 PI2_Rlt_PI)); Intro H10; Elim (Rlt_antirefl ``(sin ((x-y)/2))`` (Rlt_trans ``(sin ((x-y)/2))`` ``0`` ``(sin ((x-y)/2))`` H4 H10)).
Generalize (Rlt_minus (sin x) (sin y) H3); Clear H3; Intro H3; Rewrite form4 in H3; Generalize (Rplus_le x ``PI/2`` y ``PI/2`` H0 H2).
Rewrite <- double_var.
Intro H4; Generalize (Rle_monotony ``(Rinv 2)`` ``x+y`` PI (Rlt_le ``0`` ``/2`` (Rlt_Rinv ``2`` Rgt_2_0)) H4).
Repeat Rewrite (Rmult_sym ``/2``). 
Clear H4; Intro H4; Generalize (Rplus_le ``-(PI/2)`` x ``-(PI/2)`` y H H1); Replace ``-(PI/2)+(-(PI/2))`` with ``-PI``.
Intro H5; Generalize (Rle_monotony ``(Rinv 2)`` ``-PI`` ``x+y`` (Rlt_le ``0`` ``/2`` (Rlt_Rinv ``2`` Rgt_2_0)) H5).
Replace ``/2*(x+y)`` with ``(x+y)/2``.
Replace ``/2*(-PI)`` with ``-(PI/2)``.
Clear H5; Intro H5; Elim H4; Intro H40.
Elim H5; Intro H50.
Generalize (cos_gt_0 ``(x+y)/2`` H50 H40); Intro H6; Generalize (Rlt_monotony ``2`` ``0`` ``(cos ((x+y)/2))`` Rgt_2_0 H6).
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
Intro H5; Generalize (Rle_lt_trans ``-PI`` ``x+x`` ``x+y`` H5 H4); Intro H6; Generalize (Rlt_monotony ``(Rinv 2)`` ``-PI`` ``x+y`` (Rlt_Rinv ``2`` Rgt_2_0) H6); Replace ``/2*(-PI)`` with ``-(PI/2)``.
Replace ``/2*(x+y)`` with ``(x+y)/2``.
Clear H4 H5 H6; Intro H4; Generalize (Rlt_compatibility ``y`` ``x`` ``y`` H3); Intro H5; Rewrite Rplus_sym in H5; Generalize (Rplus_le y ``PI/2`` y ``PI/2`` H2 H2).
Rewrite <- double_var.
Intro H6; Generalize (Rlt_le_trans ``x+y`` ``y+y`` PI H5 H6); Intro H7; Generalize (Rlt_monotony ``(Rinv 2)``  ``x+y`` PI (Rlt_Rinv ``2`` Rgt_2_0) H7); Replace ``/2*PI`` with ``PI/2``.
Replace ``/2*(x+y)`` with ``(x+y)/2``.
Clear H5 H6 H7; Intro H5; Generalize (Rle_Ropp ``-(PI/2)`` y H1); Rewrite Ropp_Ropp; Clear H1; Intro H1; Generalize (Rle_sym2 ``-y`` ``PI/2`` H1); Clear H1; Intro H1; Generalize (Rle_Ropp y ``PI/2`` H2); Clear H2; Intro H2; Generalize (Rle_sym2 ``-(PI/2)`` ``-y`` H2); Clear H2; Intro H2; Generalize (Rlt_compatibility ``-y`` x y H3); Replace ``-y+x`` with ``x-y``.
Rewrite Rplus_Ropp_l.
Intro H6; Generalize (Rlt_monotony ``(Rinv 2)``  ``x-y`` ``0`` (Rlt_Rinv ``2`` Rgt_2_0) H6); Rewrite Rmult_Or; Replace ``/2*(x-y)`` with ``(x-y)/2``.
Clear H6; Intro H6; Generalize (Rplus_le  ``-(PI/2)`` x ``-(PI/2)`` ``-y`` H H2); Replace ``-(PI/2)+ (-(PI/2))`` with ``-PI``.
Replace `` x+ -y`` with ``x-y``.
Intro H7; Generalize (Rle_monotony ``(Rinv 2)`` ``-PI`` ``x-y`` (Rlt_le ``0`` ``/2`` (Rlt_Rinv ``2`` Rgt_2_0)) H7); Replace ``/2*(-PI)`` with ``-(PI/2)``.
Replace ``/2*(x-y)`` with ``(x-y)/2``.
Clear H7; Intro H7; Clear H H0 H1 H2; Apply Rminus_lt; Rewrite form4; Generalize (cos_gt_0 ``(x+y)/2`` H4 H5); Intro H8; Generalize (Rmult_lt_pos ``2`` ``(cos ((x+y)/2))`` Rgt_2_0 H8); Clear H8; Intro H8; Cut ``-PI< -(PI/2)``.
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
Apply aze.
Apply aze.
Pattern 1 PI; Rewrite double_var.
Unfold Rdiv.
Rewrite Rmult_Rplus_distrl.
Repeat Rewrite Rmult_assoc.
Rewrite <- Rinv_Rmult.
Replace ``2*2`` with ``4``.
Reflexivity.
Ring.
Apply aze.
Apply aze.
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
Apply aze.
Apply aze.
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

Lemma Rgt_3PI2_0 : ``0<3*(PI/2)``.
Cut ~(O=(3)); [Intro H1; Generalize (lt_INR_0 (3) (neq_O_lt (3) H1)); Rewrite INR_eq_INR2; Unfold INR2; Intro H2; Generalize (Rlt_monotony ``PI/2`` ``0`` ``3`` PI2_RGT_0 H2); Rewrite Rmult_Or; Rewrite Rmult_sym; Intro H3; Assumption | Discriminate].
Qed.
  
Lemma Rgt_2PI_0 : ``0<2*PI``.
Cut ~(O=(2)); [Intro H1; Generalize (lt_INR_0 (2) (neq_O_lt (2) H1)); Unfold INR; Intro H2; Generalize (Rlt_monotony PI ``0`` ``2`` PI_RGT_0 H2); Rewrite Rmult_Or; Rewrite Rmult_sym; Intro H3; Assumption | Discriminate].
Qed.

Lemma Rlt_PI_3PI2 : ``PI<3*(PI/2)``.
Generalize PI2_RGT_0; Intro H1; Generalize (Rlt_compatibility PI ``0`` ``PI/2`` H1); Replace ``PI+(PI/2)`` with ``3*(PI/2)``.
Rewrite Rplus_Or; Intro H2; Assumption.
Pattern 2 PI; Rewrite double_var.
Ring.
Qed. 
 
Lemma Rlt_3PI2_2PI : ``3*(PI/2)<2*PI``.
Generalize PI2_RGT_0; Intro H1; Generalize (Rlt_compatibility ``3*(PI/2)`` ``0`` ``PI/2`` H1); Replace ``3*(PI/2)+(PI/2)`` with ``2*PI``.
Rewrite Rplus_Or; Intro H2; Assumption.
Rewrite double; Pattern 1 2 PI; Rewrite double_var. 
Ring.
Qed.

Lemma sin_cos_PI4 : ``(sin (PI/4)) == (cos (PI/4))``.
Rewrite cos_sin; Replace ``PI/2+PI/4`` with ``-(PI/4)+PI``.
Rewrite neg_sin; Rewrite sin_neg; Ring.
Pattern 2 3 PI; Replace ``PI`` with ``PI/2+PI/2``.
Pattern 2 3 PI; Replace ``PI`` with ``PI/2+PI/2``.
Unfold Rdiv.
Cut ``2*2==4``.
Intro.
Rewrite Rmult_Rplus_distrl.
Repeat Rewrite Rmult_assoc.
Rewrite <- Rinv_Rmult.
Rewrite H.
Ring.
Apply aze.
Apply aze.
Ring.
Symmetry; Apply double_var.
Symmetry; Apply double_var.
Qed.

Lemma cos_PI4 : ``(cos (PI/4))==1/(sqrt 2)``.
Apply Rsqr_inj.
Apply cos_ge_0.
Left; Apply (Rlt_trans ``-(PI/2)`` R0 ``PI/4`` _PI2_RLT_0 PI4_RGT_0).
Left; Apply PI4_RLT_PI2.
Left; Apply (Rmult_lt_pos R1 ``(Rinv (sqrt 2))``).
Apply Rlt_R0_R1.
Apply Rlt_Rinv.
Apply Rlt_sqrt2_0.
Rewrite Rsqr_div.
Rewrite Rsqr_1; Rewrite Rsqr_sqrt.
Unfold Rsqr; Pattern 1 ``(cos (PI/4))``; Rewrite <- sin_cos_PI4; Replace ``(sin (PI/4))*(cos (PI/4))`` with ``(1/2)*(2*(sin (PI/4))*(cos (PI/4)))``.
Rewrite <- sin_2a; Replace ``2*(PI/4)`` with ``PI/2``.
Rewrite sin_PI2.
Apply Rmult_1r.
Unfold Rdiv.
Rewrite (Rmult_sym ``2``).
Replace ``4`` with ``2*2``.
Rewrite Rinv_Rmult.
Repeat Rewrite Rmult_assoc.
Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r.
Reflexivity.
Apply aze.
Apply aze.
Apply aze.
Ring.
Unfold Rdiv.
Rewrite Rmult_1l.
Repeat Rewrite <- Rmult_assoc.
Rewrite <- Rinv_l_sym.
Rewrite Rmult_1l.
Reflexivity.
Apply aze.
Left; Apply Rgt_2_0.
Apply sqrt2_neq_0.
Qed.

Lemma sin_PI4 : ``(sin (PI/4))==1/(sqrt 2)``.
Rewrite sin_cos_PI4; Apply cos_PI4.
Qed.

Lemma cos3PI4 : ``(cos (3*(PI/4)))==-1/(sqrt 2)``.
Replace ``3*(PI/4)`` with ``(PI/2)-(-(PI/4))``.
Rewrite cos_shift; Rewrite sin_neg; Rewrite sin_PI4.
Unfold Rdiv.
Rewrite Ropp_mul1.
Reflexivity.
Unfold Rminus.
Rewrite Ropp_Ropp.
Pattern 1 PI; Rewrite double_var.
Unfold Rdiv.
Rewrite Rmult_Rplus_distrl.
Repeat Rewrite Rmult_assoc.
Rewrite <- Rinv_Rmult.
Replace ``2*2`` with ``4``.
Ring.
Ring.
Apply aze.
Apply aze.
Qed.

Lemma sin3PI4 : ``(sin (3*(PI/4)))==1/(sqrt 2)``.
Replace ``3*(PI/4)`` with ``(PI/2)-(-(PI/4))``.
Rewrite sin_shift; Rewrite cos_neg; Rewrite cos_PI4; Reflexivity.
Unfold Rminus.
Rewrite Ropp_Ropp.
Pattern 1 PI; Rewrite double_var.
Unfold Rdiv.
Rewrite Rmult_Rplus_distrl.
Repeat Rewrite Rmult_assoc.
Rewrite <- Rinv_Rmult.
Replace ``2*2`` with ``4``.
Ring.
Ring.
Apply aze.
Apply aze.
Qed.

Lemma tan_PI4 : ``(tan (PI/4))==1``.
Unfold tan; Rewrite sin_cos_PI4.
Unfold Rdiv. 
Apply Rinv_r.
Replace ``PI*/4`` with ``PI/4``.
Rewrite cos_PI4; Apply R1_sqrt2_neq_0.
Unfold Rdiv; Reflexivity.
Qed.

Lemma sin_PI3_cos_PI6 : ``(sin (PI/3))==(cos (PI/6))``.
Replace ``PI/6`` with ``(PI/2)-(PI/3)``.
Rewrite cos_shift; Reflexivity.
Pattern 2 PI; Rewrite double_var.
Cut ``PI == 3*(PI/3)``.
Intro.
Pattern 1 PI; Rewrite H.
Unfold Rdiv.
Repeat Rewrite Rmult_assoc.
Rewrite <- Rinv_Rmult.
Unfold Rminus.
Rewrite (Rmult_Rplus_distrl ``PI*/2`` ``PI*/2`` ``/3``).
Repeat Rewrite Rmult_assoc.
Rewrite <- Rinv_Rmult.
Rewrite (Rmult_sym ``2``).
Replace ``3*2`` with ``6``.
Rewrite Ropp_distr1.
Ring.
Ring.
Apply aze.
DiscrR.
DiscrR.
Apply aze.
Unfold Rdiv.
Rewrite (Rmult_sym ``3``).
Rewrite Rmult_assoc.
Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r; Reflexivity.
DiscrR.
Qed.

Lemma sin_PI6_cos_PI3 : ``(cos (PI/3))==(sin (PI/6))``.
Replace ``PI/6`` with ``(PI/2)-(PI/3)``.
Rewrite sin_shift; Reflexivity.
Pattern 2 PI; Rewrite double_var.
Cut ``PI == 3*(PI/3)``.
Intro.
Pattern 1 PI; Rewrite H.
Unfold Rdiv.
Repeat Rewrite Rmult_assoc.
Rewrite <- Rinv_Rmult.
Unfold Rminus.
Rewrite (Rmult_Rplus_distrl ``PI*/2`` ``PI*/2`` ``/3``).
Repeat Rewrite Rmult_assoc.
Rewrite <- Rinv_Rmult.
Rewrite (Rmult_sym ``2``).
Replace ``3*2`` with ``6``.
Rewrite Ropp_distr1.
Ring.
Ring.
Apply aze.
DiscrR.
DiscrR.
DiscrR.
Unfold Rdiv.
Rewrite (Rmult_sym ``3``).
Rewrite Rmult_assoc.
Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r; Reflexivity.
DiscrR.
Qed.

Lemma sin_PI6 : ``(sin (PI/6))==1/2``.
Apply r_Rmult_mult with ``2*(cos (PI/6))``.
Replace ``2*(cos (PI/6))*(sin (PI/6))`` with ``2*(sin (PI/6))*(cos (PI/6))``.
Rewrite <- sin_2a; Replace ``2*(PI/6)`` with ``PI/3``.
Rewrite sin_PI3_cos_PI6.
Unfold Rdiv. 
Rewrite Rmult_1l.
Rewrite Rmult_assoc.
Rewrite (Rmult_sym ``2``).
Rewrite Rmult_assoc.
Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r; Reflexivity.
Apply aze.
Replace ``6`` with ``2*3``.
Unfold Rdiv.
Rewrite Rinv_Rmult.
Rewrite (Rmult_sym ``/2``).
Rewrite (Rmult_sym ``2``).
Repeat Rewrite Rmult_assoc.
Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r.
Reflexivity.
Apply aze.
Apply aze.
DiscrR.
Ring.
Ring.
Apply prod_neq_R0; [DiscrR | Cut ``0<(cos (PI/6))``; [Intro H1; Auto with real | Apply cos_gt_0; [Apply (Rlt_trans ``-(PI/2)`` ``0`` ``PI/6`` _PI2_RLT_0 PI6_RGT_0) | Apply PI6_RLT_PI2]]].
Qed.

Lemma cos_PI6 : ``(cos (PI/6))==(sqrt 3)/2``.
Apply Rsqr_inj.
Apply cos_ge_0.
Left; Apply (Rlt_trans ``-(PI/2)`` R0 ``PI/6`` _PI2_RLT_0 PI6_RGT_0).
Left; Apply PI6_RLT_PI2.
Left; Apply (Rmult_lt_pos ``(sqrt 3)`` ``(Rinv 2)``).
Apply Rlt_sqrt3_0.
Apply Rlt_Rinv; Apply Rgt_2_0.
Rewrite Rsqr_div.
Rewrite cos2; Unfold Rsqr; Rewrite sin_PI6; Rewrite sqrt_def.
Unfold Rdiv.
Rewrite Rmult_1l.
Rewrite <- Rinv_Rmult.
Replace ``2*2`` with ``4``.
Apply r_Rmult_mult with ``4``.
Unfold Rminus.
Rewrite Rmult_Rplus_distr.
Rewrite Rmult_1r.
Rewrite Ropp_mul3.
Rewrite <- Rinv_r_sym.
Rewrite (Rmult_sym ``3``).
Rewrite <- Rmult_assoc.
Rewrite <- Rinv_r_sym.
Rewrite Rmult_1l.
Ring.
DiscrR.
DiscrR.
DiscrR.
Ring.
Apply aze.
Apply aze.
Left; Apply Rgt_3_0.
Apply aze.
Qed.

Lemma tan_PI6 : ``(tan (PI/6))==1/(sqrt 3)``.
Unfold tan; Rewrite sin_PI6; Rewrite cos_PI6.
Unfold Rdiv.
Repeat Rewrite Rmult_1l.
Rewrite Rinv_Rmult.
Rewrite Rinv_Rinv.
Rewrite (Rmult_sym ``/2``).
Rewrite Rmult_assoc.
Rewrite <- Rinv_r_sym.
Apply Rmult_1r.
Apply aze.
Apply aze.
Red; Intro.
Assert H1 := Rlt_sqrt3_0.
Rewrite H in H1; Elim (Rlt_antirefl ``0`` H1).
Apply Rinv_neq_R0.
Apply aze.
Qed.

Lemma sin_PI3 : ``(sin (PI/3))==(sqrt 3)/2``.
Rewrite sin_PI3_cos_PI6; Apply cos_PI6.
Qed.

Lemma cos_PI3 : ``(cos (PI/3))==1/2``.
Rewrite sin_PI6_cos_PI3; Apply sin_PI6.
Qed.

Lemma tan_PI3 : ``(tan (PI/3))==(sqrt 3)``.
Unfold tan; Rewrite sin_PI3; Rewrite cos_PI3.
Unfold Rdiv.
Rewrite Rmult_1l.
Rewrite Rinv_Rinv.
Rewrite Rmult_assoc.
Rewrite <- Rinv_l_sym.
Apply Rmult_1r.
Apply aze.
Apply aze.
Qed.

Lemma sin_2PI3 : ``(sin (2*(PI/3)))==(sqrt 3)/2``.
Rewrite double.
Rewrite sin_plus; Rewrite sin_PI3; Rewrite cos_PI3.
Unfold Rdiv.
Repeat Rewrite Rmult_1l.
Rewrite (Rmult_sym ``/2``).
Pattern 3 ``(sqrt 3)``; Rewrite double_var.
Rewrite Rmult_Rplus_distrl.
Unfold Rdiv.
Repeat Rewrite Rmult_assoc.
Rewrite <- Rinv_Rmult.
Replace ``2*2`` with ``4``.
Reflexivity.
Ring.
Apply aze.
Apply aze.
Qed.

Lemma cos_2PI3 : ``(cos (2*(PI/3)))==-1/2``.
Rewrite double.
Rewrite cos_plus; Rewrite sin_PI3; Rewrite cos_PI3.
Unfold Rdiv.
Rewrite Rmult_1l.
Apply r_Rmult_mult with ``2*2``.
Rewrite Rminus_distr.
Repeat Rewrite Rmult_assoc.
Rewrite (Rmult_sym ``2``).
Repeat Rewrite Rmult_assoc.
Rewrite <- (Rinv_l_sym).
Rewrite Rmult_1r.
Rewrite <- Rinv_r_sym.
Pattern 4 ``2``; Rewrite (Rmult_sym ``2``).
Repeat Rewrite Rmult_assoc.
Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r.
Rewrite Ropp_mul3.
Rewrite Rmult_1r.
Rewrite (Rmult_sym ``2``).
Repeat Rewrite Rmult_assoc.
Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r.
Rewrite (Rmult_sym ``2``).
Rewrite (Rmult_sym ``/2``).
Repeat Rewrite Rmult_assoc.
Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r.
Rewrite sqrt_def.
Ring.
Replace ``3`` with ``(INR (S (S (S O))))`` .
Apply pos_INR.
Rewrite INR_eq_INR2.
Reflexivity.
Apply aze.
Apply aze.
Apply aze.
Apply aze.
Apply aze.
Apply prod_neq_R0; Apply aze.
Qed.

Lemma tan_2PI3 : ``(tan (2*(PI/3)))==-(sqrt 3)``.
Unfold tan; Rewrite sin_2PI3; Rewrite cos_2PI3.
Unfold Rdiv.
Rewrite Rinv_Rmult.
Rewrite Rinv_Rinv.
Repeat Rewrite Rmult_assoc.
Rewrite (Rmult_sym ``/2``).
Repeat Rewrite Rmult_assoc.
Rewrite <- Rinv_r_sym.
Rewrite Rmult_1r.
Rewrite <- Ropp_Rinv.
Rewrite Ropp_mul3.
Rewrite Rinv_R1; Rewrite Rmult_1r; Reflexivity.
DiscrR.
Apply aze.
Apply aze.
DiscrR.
Apply Rinv_neq_R0; Apply aze.
Qed.

Lemma cos_5PI4 : ``(cos (5*(PI/4)))==-1/(sqrt 2)``.
Replace ``5*(PI/4)`` with ``(PI/4)+(PI)``.
Rewrite neg_cos; Rewrite cos_PI4.
Unfold Rdiv.
Symmetry; Apply Ropp_mul1.
Pattern 2 PI; Rewrite double_var.
Pattern 2 3 PI; Rewrite double_var.
Unfold Rdiv.
Rewrite Rmult_Rplus_distrl.
Repeat Rewrite Rmult_assoc.
Rewrite <- Rinv_Rmult.
Replace ``2*2`` with ``4``.
Ring.
Ring.
Apply aze.
Apply aze.
Qed.

Lemma sin_5PI4 : ``(sin (5*(PI/4)))==-1/(sqrt 2)``.
Replace ``5*(PI/4)`` with ``(PI/4)+(PI)``.
Rewrite neg_sin; Rewrite sin_PI4.
Unfold Rdiv; Symmetry; Apply Ropp_mul1.
Pattern 2 PI; Rewrite double_var.
Pattern 2 3 PI; Rewrite double_var.
Unfold Rdiv.
Rewrite Rmult_Rplus_distrl.
Repeat Rewrite Rmult_assoc.
Rewrite <- Rinv_Rmult.
Replace ``2*2`` with ``4``.
Ring.
Ring.
Apply aze.
Apply aze.
Qed.

Lemma sin_cos5PI4 : ``(cos (5*(PI/4)))==(sin (5*(PI/4)))``.
Rewrite cos_5PI4; Rewrite sin_5PI4; Reflexivity.
Qed.

(***************************************************************)
(* Radian -> Degree | Degree -> Radian                         *)
(***************************************************************)

Definition plat : R := (IZR `180`).
Definition toRad [x:R] : R := ``x*PI*/plat``.
Definition toDeg [x:R] : R := ``x*plat*/PI``.

Lemma rad_deg : (x:R) (toRad (toDeg x))==x.
Intro x; Unfold toRad toDeg.
Rewrite <- (Rmult_sym plat).
Repeat Rewrite Rmult_assoc.
Rewrite (Rmult_sym plat).
Repeat Rewrite Rmult_assoc.
Rewrite <- Rinv_l_sym. 
Rewrite Rmult_1r; Rewrite <- Rinv_l_sym. 
Apply Rmult_1r.
Apply PI_neq0.
Unfold plat.
Apply not_O_IZR.
Discriminate.
Qed.

Lemma toRad_inj : (x,y:R) (toRad x)==(toRad y) -> x==y.
Intros; Unfold toRad in H; Apply r_Rmult_mult with PI.
Rewrite <- (Rmult_sym x); Rewrite <- (Rmult_sym y).
Apply r_Rmult_mult with ``/plat``.
Rewrite <- (Rmult_sym ``x*PI``); Rewrite <- (Rmult_sym ``y*PI``); Assumption.
Apply Rinv_neq_R0.
Unfold plat.
Apply not_O_IZR.
Discriminate.
Apply PI_neq0.
Qed.

Lemma deg_rad : (x:R) (toDeg (toRad x))==x.
Intro x; Apply toRad_inj; Rewrite -> (rad_deg (toRad x)); Reflexivity.
Qed.

Definition sind [x:R] : R := (sin (toRad x)).
Definition cosd [x:R] : R := (cos (toRad x)).
Definition tand [x:R] : R := (tan (toRad x)).

Lemma Rsqr_sin_cos_d_one : (x:R) ``(Rsqr (sind x))+(Rsqr (cosd x))==1``.
Intro x; Unfold sind; Unfold cosd; Apply sin2_cos2.
Qed.

(***************************************************)
(*                Other properties                 *)
(***************************************************)

Lemma sin_lb_ge_0 : (a:R) ``0<=a``->``a<=PI/2``->``0<=(sin_lb a)``.
Intros; Case (total_order R0 a); Intro.
Left; Apply sin_lb_gt_0; Assumption.
Elim H1; Intro.
Rewrite <- H2; Unfold sin_lb; Unfold sin_approx; Unfold sum_f_R0; Unfold sin_term; Repeat Rewrite pow_ne_zero.
Unfold Rdiv; Repeat Rewrite Rmult_Ol; Repeat Rewrite Rmult_Or; Repeat Rewrite Rplus_Or; Right; Reflexivity.
Simpl; Discriminate.
Simpl; Discriminate.
Simpl; Discriminate.
Simpl; Discriminate.
Elim (Rlt_antirefl ``0`` (Rle_lt_trans ``0`` a ``0`` H H2)).
Qed.
