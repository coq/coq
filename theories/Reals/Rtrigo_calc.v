(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

Require Rbase.
Require DiscrR.
Require Rseries.
Require R_sqr.
Require Rlimit.
Require Rtrigo.
Require R_sqrt.

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

Lemma tan_2PI : ``(tan (2*PI))==0``.
Unfold tan; Rewrite sin_2PI; Unfold Rdiv; Apply Rmult_Ol.
Qed.

Lemma sin_cos_PI4 : ``(sin (PI/4)) == (cos (PI/4))``.
Rewrite cos_sin.
Replace ``PI/2+PI/4`` with ``-(PI/4)+PI``.
Rewrite neg_sin; Rewrite sin_neg; Ring.
Cut ``PI==PI/2+PI/2``; [Intro | Apply double_var].
Pattern 2 3 PI; Rewrite H.
Pattern 2 3 PI; Rewrite H.
Unfold Rdiv; Cut ``2*2==4``.
Intro; Rewrite Rmult_Rplus_distrl.
Repeat Rewrite Rmult_assoc.
Rewrite <- Rinv_Rmult; [Rewrite H0; Ring | Apply aze | Apply aze].
Ring.
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

Lemma PI6_RGT_0 : ``0<PI/6``.
Unfold Rdiv; Apply Rmult_lt_pos; [Apply PI_RGT_0 | Apply Rlt_Rinv; Sup0].
Qed.

Lemma PI6_RLT_PI2 : ``PI/6<PI/2``.
Unfold Rdiv; Apply Rlt_monotony.
Apply PI_RGT_0.
Apply Rinv_lt.
Apply Rmult_lt_pos; Sup0.
Pattern 1 ``2``; Rewrite <- Rplus_Or.
Replace ``6`` with ``2+4``; [Apply Rlt_compatibility; Sup0 | Ring].
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

Lemma PI4_RGT_0 : ``0<PI/4``.
Unfold Rdiv; Apply Rmult_lt_pos; [Apply PI_RGT_0 | Apply Rlt_Rinv; Sup0].
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
DiscrR.
DiscrR.
DiscrR.
Ring.
Unfold Rdiv.
Rewrite Rmult_1l.
Repeat Rewrite <- Rmult_assoc.
Rewrite <- Rinv_l_sym.
Rewrite Rmult_1l.
Reflexivity.
DiscrR.
Left; Apply Rgt_2_0.
Apply sqrt2_neq_0.
Qed.

Lemma sin_PI4 : ``(sin (PI/4))==1/(sqrt 2)``.
Rewrite sin_cos_PI4; Apply cos_PI4.
Qed.

Lemma tan_PI4 : ``(tan (PI/4))==1``.
Unfold tan; Rewrite sin_cos_PI4.
Unfold Rdiv. 
Apply Rinv_r.
Replace ``PI*/4`` with ``PI/4``.
Rewrite cos_PI4; Apply R1_sqrt2_neq_0.
Unfold Rdiv; Reflexivity.
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

Lemma Rgt_3PI2_0 : ``0<3*(PI/2)``.
Apply Rmult_lt_pos; [Apply Rgt_3_0 | Unfold Rdiv; Apply Rmult_lt_pos; [Apply PI_RGT_0 | Apply Rlt_Rinv; Apply Rgt_2_0]].
Qed.

Lemma Rgt_2PI_0 : ``0<2*PI``.
Apply Rmult_lt_pos; [Apply Rgt_2_0 | Apply PI_RGT_0].
Qed.

Lemma Rlt_PI_3PI2 : ``PI<3*(PI/2)``.
Generalize PI2_RGT_0; Intro H1; Generalize (Rlt_compatibility PI ``0`` ``PI/2`` H1); Replace ``PI+(PI/2)`` with ``3*(PI/2)``.
Rewrite Rplus_Or; Intro H2; Assumption.
Pattern 2 PI; Rewrite double_var; Ring.
Qed. 
 
Lemma Rlt_3PI2_2PI : ``3*(PI/2)<2*PI``.
Generalize PI2_RGT_0; Intro H1; Generalize (Rlt_compatibility ``3*(PI/2)`` ``0`` ``PI/2`` H1); Replace ``3*(PI/2)+(PI/2)`` with ``2*PI``.
Rewrite Rplus_Or; Intro H2; Assumption.
Rewrite double; Pattern 1 2 PI; Rewrite double_var; Ring.
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