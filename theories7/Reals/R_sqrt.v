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
Require Rsqrt_def.
V7only [Import R_scope.]. Open Local Scope R_scope.

(* Here is a continuous extension of Rsqrt on R *)
Definition sqrt : R->R := [x:R](Cases (case_Rabsolu x) of
      (leftT _) => R0
    | (rightT a) => (Rsqrt (mknonnegreal x (Rle_sym2 ? ? a))) end).

Lemma sqrt_positivity : (x:R) ``0<=x`` -> ``0<=(sqrt x)``.
Intros.
Unfold sqrt.
Case (case_Rabsolu x); Intro.
Elim (Rlt_antirefl ? (Rlt_le_trans ? ? ? r H)).
Apply Rsqrt_positivity.
Qed.

Lemma sqrt_sqrt : (x:R) ``0<=x`` -> ``(sqrt x)*(sqrt x)==x``.
Intros.
Unfold sqrt.
Case (case_Rabsolu x); Intro.
Elim (Rlt_antirefl ? (Rlt_le_trans ? ? ? r H)).
Rewrite Rsqrt_Rsqrt; Reflexivity.
Qed.

Lemma sqrt_0 : ``(sqrt 0)==0``.
Apply Rsqr_eq_0; Unfold Rsqr; Apply sqrt_sqrt; Right; Reflexivity. 
Qed.

Lemma sqrt_1 : ``(sqrt 1)==1``.
Apply (Rsqr_inj (sqrt R1) R1); [Apply sqrt_positivity; Left | Left | Unfold Rsqr; Rewrite -> sqrt_sqrt; [Ring | Left]]; Apply Rlt_R0_R1.
Qed.

Lemma sqrt_eq_0 : (x:R) ``0<=x``->``(sqrt x)==0``->``x==0``.
Intros; Cut ``(Rsqr (sqrt x))==0``.
Intro; Unfold Rsqr in H1; Rewrite -> sqrt_sqrt in H1; Assumption.
Rewrite H0; Apply Rsqr_O.
Qed.

Lemma sqrt_lem_0 : (x,y:R) ``0<=x``->``0<=y``->(sqrt x)==y->``y*y==x``.
Intros; Rewrite <- H1; Apply (sqrt_sqrt x H).
Qed.

Lemma sqtr_lem_1 : (x,y:R) ``0<=x``->``0<=y``->``y*y==x``->(sqrt x)==y.
Intros; Apply Rsqr_inj; [Apply (sqrt_positivity x H) | Assumption | Unfold Rsqr; Rewrite -> H1; Apply (sqrt_sqrt x H)].
Qed.

Lemma sqrt_def : (x:R) ``0<=x``->``(sqrt x)*(sqrt x)==x``.
Intros; Apply (sqrt_sqrt x H).
Qed.

Lemma sqrt_square : (x:R) ``0<=x``->``(sqrt (x*x))==x``.
Intros; Apply (Rsqr_inj (sqrt (Rsqr x)) x (sqrt_positivity (Rsqr x) (pos_Rsqr x)) H); Unfold Rsqr; Apply (sqrt_sqrt (Rsqr x) (pos_Rsqr x)).
Qed.

Lemma sqrt_Rsqr : (x:R) ``0<=x``->``(sqrt (Rsqr x))==x``.
Intros; Unfold Rsqr; Apply sqrt_square; Assumption.
Qed.

Lemma sqrt_Rsqr_abs : (x:R) (sqrt (Rsqr x))==(Rabsolu x).
Intro x; Rewrite -> Rsqr_abs; Apply sqrt_Rsqr; Apply Rabsolu_pos.
Qed.

Lemma Rsqr_sqrt : (x:R) ``0<=x``->(Rsqr (sqrt x))==x.
Intros x H1; Unfold Rsqr; Apply (sqrt_sqrt x H1).
Qed.

Lemma sqrt_times : (x,y:R) ``0<=x``->``0<=y``->``(sqrt (x*y))==(sqrt x)*(sqrt y)``.
Intros x y H1 H2; Apply (Rsqr_inj (sqrt (Rmult x y)) (Rmult (sqrt x) (sqrt y)) (sqrt_positivity (Rmult x y) (Rmult_le_pos x y H1 H2)) (Rmult_le_pos (sqrt x) (sqrt y) (sqrt_positivity x H1) (sqrt_positivity y H2))); Rewrite Rsqr_times; Repeat Rewrite Rsqr_sqrt; [Ring | Assumption |Assumption | Apply (Rmult_le_pos x y H1 H2)].
Qed.

Lemma sqrt_lt_R0 : (x:R) ``0<x`` -> ``0<(sqrt x)``.
Intros x H1; Apply Rsqr_incrst_0; [Rewrite Rsqr_O; Rewrite Rsqr_sqrt ; [Assumption | Left; Assumption] | Right; Reflexivity | Apply (sqrt_positivity x (Rlt_le R0 x H1))].
Qed.

Lemma sqrt_div : (x,y:R) ``0<=x``->``0<y``->``(sqrt (x/y))==(sqrt x)/(sqrt y)``.
Intros x y H1 H2; Apply Rsqr_inj; [ Apply sqrt_positivity; Apply (Rmult_le_pos x (Rinv y)); [ Assumption | Generalize (Rlt_Rinv y H2); Clear H2; Intro H2; Left; Assumption] | Apply (Rmult_le_pos (sqrt x) (Rinv (sqrt y))) ; [ Apply (sqrt_positivity x H1) | Generalize (sqrt_lt_R0 y H2); Clear H2; Intro H2; Generalize (Rlt_Rinv (sqrt y) H2); Clear H2; Intro H2; Left; Assumption] | Rewrite Rsqr_div; Repeat Rewrite Rsqr_sqrt; [ Reflexivity | Left; Assumption | Assumption | Generalize (Rlt_Rinv y H2); Intro H3; Generalize (Rlt_le R0 (Rinv y) H3); Intro H4; Apply (Rmult_le_pos x (Rinv y) H1 H4) |Red; Intro H3; Generalize (Rlt_le R0 y H2); Intro H4; Generalize (sqrt_eq_0 y H4 H3); Intro H5; Rewrite H5 in H2; Elim (Rlt_antirefl R0 H2)]].
Qed.

Lemma sqrt_lt_0 : (x,y:R) ``0<=x``->``0<=y``->``(sqrt x)<(sqrt y)``->``x<y``.
Intros x y H1 H2 H3; Generalize (Rsqr_incrst_1 (sqrt x) (sqrt y) H3 (sqrt_positivity x H1) (sqrt_positivity y H2)); Intro H4; Rewrite (Rsqr_sqrt x H1) in H4; Rewrite (Rsqr_sqrt y H2) in H4; Assumption.
Qed.

Lemma sqrt_lt_1 : (x,y:R) ``0<=x``->``0<=y``->``x<y``->``(sqrt x)<(sqrt y)``.
Intros x y H1 H2 H3; Apply Rsqr_incrst_0; [Rewrite (Rsqr_sqrt x H1); Rewrite (Rsqr_sqrt y H2); Assumption | Apply (sqrt_positivity x H1) | Apply (sqrt_positivity y H2)].
Qed.

Lemma sqrt_le_0 : (x,y:R) ``0<=x``->``0<=y``->``(sqrt x)<=(sqrt y)``->``x<=y``.
Intros x y H1 H2 H3; Generalize (Rsqr_incr_1 (sqrt x) (sqrt y) H3 (sqrt_positivity x H1) (sqrt_positivity y H2)); Intro H4; Rewrite (Rsqr_sqrt x H1) in H4; Rewrite (Rsqr_sqrt y H2) in H4; Assumption.
Qed.

Lemma sqrt_le_1 : (x,y:R) ``0<=x``->``0<=y``->``x<=y``->``(sqrt x)<=(sqrt y)``.
Intros x y H1 H2 H3; Apply Rsqr_incr_0; [ Rewrite (Rsqr_sqrt x H1); Rewrite (Rsqr_sqrt y H2); Assumption | Apply (sqrt_positivity x H1) | Apply (sqrt_positivity y H2)].
Qed.

Lemma sqrt_inj : (x,y:R) ``0<=x``->``0<=y``->(sqrt x)==(sqrt y)->x==y.
Intros; Cut ``(Rsqr (sqrt x))==(Rsqr (sqrt y))``.
Intro; Rewrite (Rsqr_sqrt x H) in H2; Rewrite (Rsqr_sqrt y H0) in H2; Assumption.
Rewrite H1; Reflexivity.
Qed.

Lemma sqrt_less : (x:R)  ``0<=x``->``1<x``->``(sqrt x)<x``.
Intros x H1 H2; Generalize (sqrt_lt_1 R1 x (Rlt_le R0 R1 (Rlt_R0_R1)) H1 H2); Intro H3; Rewrite  sqrt_1 in H3; Generalize (Rmult_ne (sqrt x)); Intro H4; Elim H4; Intros H5 H6; Rewrite <- H5; Pattern 2 x; Rewrite <- (sqrt_def x H1); Apply (Rlt_monotony (sqrt x) R1 (sqrt x) (sqrt_lt_R0 x (Rlt_trans R0 R1 x Rlt_R0_R1 H2)) H3).
Qed.

Lemma sqrt_more : (x:R) ``0<x``->``x<1``->``x<(sqrt x)``.
Intros x H1 H2; Generalize (sqrt_lt_1 x R1 (Rlt_le R0 x H1) (Rlt_le R0 R1 (Rlt_R0_R1)) H2); Intro H3; Rewrite  sqrt_1 in H3; Generalize (Rmult_ne (sqrt x)); Intro H4; Elim H4; Intros H5 H6; Rewrite <- H5; Pattern 1 x; Rewrite <- (sqrt_def x (Rlt_le R0 x H1)); Apply (Rlt_monotony (sqrt x) (sqrt x) R1 (sqrt_lt_R0 x H1) H3).
Qed.

Lemma sqrt_cauchy : (a,b,c,d:R) ``a*c+b*d<=(sqrt ((Rsqr a)+(Rsqr b)))*(sqrt ((Rsqr c)+(Rsqr d)))``.
Intros a b c d; Apply Rsqr_incr_0_var; [Rewrite Rsqr_times; Repeat Rewrite Rsqr_sqrt; Unfold Rsqr; [Replace ``(a*c+b*d)*(a*c+b*d)`` with ``(a*a*c*c+b*b*d*d)+(2*a*b*c*d)``; [Replace ``(a*a+b*b)*(c*c+d*d)`` with ``(a*a*c*c+b*b*d*d)+(a*a*d*d+b*b*c*c)``; [Apply Rle_compatibility; Replace ``a*a*d*d+b*b*c*c`` with ``(2*a*b*c*d)+(a*a*d*d+b*b*c*c-2*a*b*c*d)``; [Pattern 1 ``2*a*b*c*d``; Rewrite <- Rplus_Or; Apply Rle_compatibility; Replace ``a*a*d*d+b*b*c*c-2*a*b*c*d`` with (Rsqr (Rminus (Rmult a d) (Rmult b c))); [Apply pos_Rsqr | Unfold Rsqr; Ring] | Ring] | Ring] | Ring] | Apply (ge0_plus_ge0_is_ge0 (Rsqr c) (Rsqr d) (pos_Rsqr c) (pos_Rsqr d)) | Apply (ge0_plus_ge0_is_ge0 (Rsqr a) (Rsqr b) (pos_Rsqr a) (pos_Rsqr b))] | Apply Rmult_le_pos; Apply sqrt_positivity; Apply ge0_plus_ge0_is_ge0; Apply pos_Rsqr].
Qed.

(************************************************************)
(* Resolution of [a*X^2+b*X+c=0]                            *)
(************************************************************)

Definition Delta [a:nonzeroreal;b,c:R] : R := ``(Rsqr b)-4*a*c``.

Definition Delta_is_pos [a:nonzeroreal;b,c:R] : Prop := ``0<=(Delta a b c)``.

Definition sol_x1 [a:nonzeroreal;b,c:R] : R := ``(-b+(sqrt (Delta a b c)))/(2*a)``.

Definition sol_x2 [a:nonzeroreal;b,c:R] : R := ``(-b-(sqrt (Delta a b c)))/(2*a)``.

Lemma Rsqr_sol_eq_0_1 : (a:nonzeroreal;b,c,x:R) (Delta_is_pos a b c) -> (x==(sol_x1 a b c))\/(x==(sol_x2 a b c)) -> ``a*(Rsqr x)+b*x+c==0``.
Intros; Elim H0; Intro.
Unfold sol_x1 in H1; Unfold Delta in H1; Rewrite H1; Unfold Rdiv; Repeat Rewrite Rsqr_times; Rewrite Rsqr_plus; Rewrite <- Rsqr_neg; Rewrite Rsqr_sqrt.
Rewrite Rsqr_inv.
Unfold Rsqr; Repeat Rewrite Rinv_Rmult.
Repeat Rewrite Rmult_assoc; Rewrite (Rmult_sym a).
Repeat Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r; Rewrite Rmult_Rplus_distrl.
Repeat Rewrite Rmult_assoc.
Pattern 2 ``2``; Rewrite (Rmult_sym ``2``).
Repeat Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r.
Rewrite (Rmult_Rplus_distrl ``-b`` ``(sqrt (b*b-(2*(2*(a*c)))))`` ``(/2*/a)``).
Rewrite Rmult_Rplus_distr; Repeat Rewrite Rplus_assoc.
Replace ``( -b*((sqrt (b*b-(2*(2*(a*c)))))*(/2*/a))+(b*( -b*(/2*/a))+(b*((sqrt (b*b-(2*(2*(a*c)))))*(/2*/a))+c)))`` with ``(b*( -b*(/2*/a)))+c``.
Unfold Rminus; Repeat Rewrite <- Rplus_assoc.
Replace ``b*b+b*b`` with ``2*(b*b)``.
Rewrite Rmult_Rplus_distrl; Repeat Rewrite Rmult_assoc.
Rewrite (Rmult_sym ``2``); Repeat Rewrite Rmult_assoc.
Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r.
Rewrite Ropp_mul1; Repeat Rewrite Rmult_assoc; Rewrite (Rmult_sym ``2``).
Repeat Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r; Rewrite (Rmult_sym ``/2``); Repeat Rewrite Rmult_assoc; Rewrite (Rmult_sym ``2``).
Repeat Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r; Repeat Rewrite Rmult_assoc.
Rewrite (Rmult_sym a); Rewrite Rmult_assoc.
Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r; Rewrite <- Ropp_mul2.
Ring.
Apply (cond_nonzero a).
DiscrR.
DiscrR.
DiscrR.
Ring.
Ring.
DiscrR.
Apply (cond_nonzero a).
DiscrR.
Apply (cond_nonzero a).
Apply prod_neq_R0; [DiscrR | Apply (cond_nonzero a)].
Apply prod_neq_R0; [DiscrR | Apply (cond_nonzero a)].
Apply prod_neq_R0; [DiscrR | Apply (cond_nonzero a)].
Assumption.
Unfold sol_x2 in H1; Unfold Delta in H1; Rewrite H1; Unfold Rdiv; Repeat Rewrite Rsqr_times; Rewrite Rsqr_minus; Rewrite <- Rsqr_neg; Rewrite Rsqr_sqrt.
Rewrite Rsqr_inv.
Unfold Rsqr; Repeat Rewrite Rinv_Rmult; Repeat Rewrite Rmult_assoc.
Rewrite (Rmult_sym a); Repeat Rewrite Rmult_assoc.
Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r; Unfold Rminus; Rewrite Rmult_Rplus_distrl.
Rewrite Ropp_mul1; Repeat Rewrite Rmult_assoc; Pattern 2 ``2``; Rewrite (Rmult_sym ``2``).
Repeat Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r; Rewrite (Rmult_Rplus_distrl ``-b`` ``-(sqrt (b*b+ -(2*(2*(a*c))))) `` ``(/2*/a)``).
Rewrite Rmult_Rplus_distr; Repeat Rewrite Rplus_assoc.
Rewrite Ropp_mul1; Rewrite Ropp_Ropp.
Replace ``(b*((sqrt (b*b+ -(2*(2*(a*c)))))*(/2*/a))+(b*( -b*(/2*/a))+(b*( -(sqrt (b*b+ -(2*(2*(a*c)))))*(/2*/a))+c)))`` with ``(b*( -b*(/2*/a)))+c``.
Repeat Rewrite <- Rplus_assoc; Replace ``b*b+b*b`` with ``2*(b*b)``.
Rewrite Rmult_Rplus_distrl; Repeat Rewrite Rmult_assoc; Rewrite (Rmult_sym ``2``); Repeat Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym.
Rewrite Ropp_mul1; Repeat Rewrite Rmult_assoc.
Rewrite (Rmult_sym ``2``); Repeat Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r; Rewrite (Rmult_sym ``/2``); Repeat Rewrite Rmult_assoc.
Rewrite (Rmult_sym ``2``); Repeat Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r; Repeat Rewrite Rmult_assoc; Rewrite (Rmult_sym a); Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r; Rewrite <- Ropp_mul2; Ring.
Apply (cond_nonzero a).
DiscrR.
DiscrR.
DiscrR.
Ring.
Ring.
DiscrR.
Apply (cond_nonzero a).
DiscrR.
DiscrR.
Apply (cond_nonzero a).
Apply prod_neq_R0; DiscrR Orelse Apply (cond_nonzero a).
Apply prod_neq_R0; DiscrR Orelse Apply (cond_nonzero a).
Apply prod_neq_R0; DiscrR Orelse Apply (cond_nonzero a).
Assumption.
Qed.

Lemma Rsqr_sol_eq_0_0 : (a:nonzeroreal;b,c,x:R) (Delta_is_pos a b c) -> ``a*(Rsqr x)+b*x+c==0`` -> (x==(sol_x1 a b c))\/(x==(sol_x2 a b c)).
Intros; Rewrite (canonical_Rsqr a b c x) in H0; Rewrite Rplus_sym in H0; Generalize (Rplus_Ropp  ``(4*a*c-(Rsqr b))/(4*a)`` ``a*(Rsqr (x+b/(2*a)))`` H0); Cut ``(Rsqr b)-4*a*c==(Delta a b c)``.
Intro; Replace ``-((4*a*c-(Rsqr b))/(4*a))`` with ``((Rsqr b)-4*a*c)/(4*a)``.
Rewrite H1; Intro; Generalize (Rmult_mult_r ``/a`` ``a*(Rsqr (x+b/(2*a)))`` ``(Delta a b c)/(4*a)`` H2); Replace ``/a*(a*(Rsqr (x+b/(2*a))))`` with ``(Rsqr (x+b/(2*a)))``.
Replace ``/a*(Delta a b c)/(4*a)`` with ``(Rsqr ((sqrt (Delta a b c))/(2*a)))``.
Intro; Generalize (Rsqr_eq ``(x+b/(2*a))`` ``((sqrt (Delta a b c))/(2*a))`` H3); Intro; Elim H4; Intro.
Left; Unfold sol_x1; Generalize (Rplus_plus_r ``-(b/(2*a))`` ``x+b/(2*a)`` ``(sqrt (Delta a b c))/(2*a)`` H5); Replace `` -(b/(2*a))+(x+b/(2*a))`` with x.
Intro; Rewrite H6; Unfold Rdiv; Ring.
Ring.
Right; Unfold sol_x2; Generalize (Rplus_plus_r ``-(b/(2*a))`` ``x+b/(2*a)`` ``-((sqrt (Delta a b c))/(2*a))`` H5); Replace `` -(b/(2*a))+(x+b/(2*a))`` with x.
Intro; Rewrite H6; Unfold Rdiv; Ring.
Ring.
Rewrite Rsqr_div.
Rewrite Rsqr_sqrt.
Unfold Rdiv.
Repeat Rewrite Rmult_assoc.
Rewrite (Rmult_sym ``/a``).
Rewrite Rmult_assoc.
Rewrite <- Rinv_Rmult.
Replace ``(2*(2*a))*a`` with ``(Rsqr (2*a))``.
Reflexivity.
SqRing.
Rewrite <- Rmult_assoc; Apply prod_neq_R0; [DiscrR | Apply (cond_nonzero a)].
Apply (cond_nonzero a).
Assumption.
Apply prod_neq_R0; [DiscrR | Apply (cond_nonzero a)].
Rewrite <- Rmult_assoc; Rewrite <- Rinv_l_sym.
Symmetry; Apply Rmult_1l.
Apply (cond_nonzero a).
Unfold Rdiv; Rewrite <- Ropp_mul1.
Rewrite Ropp_distr2.
Reflexivity.
Reflexivity.
Qed.
