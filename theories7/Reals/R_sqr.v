(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Rbase.
Require Rbasic_fun.
V7only [Import R_scope.]. Open Local Scope R_scope.

(****************************************************)
(* Rsqr : some results                              *)
(****************************************************)

Tactic Definition SqRing := Unfold Rsqr; Ring.

Lemma Rsqr_neg : (x:R) ``(Rsqr x)==(Rsqr (-x))``.
Intros; SqRing.
Qed.

Lemma Rsqr_times : (x,y:R) ``(Rsqr (x*y))==(Rsqr x)*(Rsqr y)``.
Intros; SqRing.
Qed.

Lemma Rsqr_plus : (x,y:R) ``(Rsqr (x+y))==(Rsqr x)+(Rsqr y)+2*x*y``.
Intros; SqRing.
Qed.

Lemma Rsqr_minus : (x,y:R) ``(Rsqr (x-y))==(Rsqr x)+(Rsqr y)-2*x*y``.
Intros; SqRing.
Qed.

Lemma Rsqr_neg_minus : (x,y:R) ``(Rsqr (x-y))==(Rsqr (y-x))``.
Intros; SqRing.
Qed.

Lemma Rsqr_1 : ``(Rsqr 1)==1``.
SqRing.
Qed.

Lemma Rsqr_gt_0_0 : (x:R) ``0<(Rsqr x)`` -> ~``x==0``.
Intros; Red; Intro; Rewrite H0 in H; Rewrite Rsqr_O in H; Elim (Rlt_antirefl ``0`` H).
Qed.

Lemma Rsqr_pos_lt : (x:R) ~(x==R0)->``0<(Rsqr x)``.
Intros; Case (total_order R0 x); Intro; [Unfold Rsqr; Apply Rmult_lt_pos; Assumption | Elim H0; Intro; [Elim H; Symmetry; Exact H1 | Rewrite Rsqr_neg; Generalize (Rlt_Ropp x ``0`` H1); Rewrite Ropp_O; Intro; Unfold Rsqr; Apply Rmult_lt_pos; Assumption]].
Qed.

Lemma Rsqr_div : (x,y:R) ~``y==0`` -> ``(Rsqr (x/y))==(Rsqr x)/(Rsqr y)``.
Intros; Unfold Rsqr.
Unfold Rdiv.
Rewrite Rinv_Rmult.
Repeat Rewrite Rmult_assoc.
Apply Rmult_mult_r.
Pattern 2 x; Rewrite Rmult_sym.
Repeat Rewrite Rmult_assoc.
Apply Rmult_mult_r.
Reflexivity.
Assumption.
Assumption.
Qed.

Lemma Rsqr_eq_0 : (x:R) ``(Rsqr x)==0`` -> ``x==0``.
Unfold Rsqr; Intros; Generalize (without_div_Od x x H); Intro; Elim H0; Intro ; Assumption.
Qed.

Lemma Rsqr_minus_plus : (a,b:R) ``(a-b)*(a+b)==(Rsqr a)-(Rsqr b)``.
Intros; SqRing.
Qed.

Lemma Rsqr_plus_minus : (a,b:R) ``(a+b)*(a-b)==(Rsqr a)-(Rsqr b)``.
Intros; SqRing.
Qed.

Lemma Rsqr_incr_0 : (x,y:R) ``(Rsqr x)<=(Rsqr y)`` -> ``0<=x`` -> ``0<=y`` -> ``x<=y``.
Intros; Case (total_order_Rle x y); Intro; [Assumption | Cut ``y<x``; [Intro; Unfold Rsqr in H; Generalize (Rmult_lt2 y x y x H1 H1 H2 H2); Intro; Generalize (Rle_lt_trans ``x*x`` ``y*y`` ``x*x`` H H3); Intro; Elim (Rlt_antirefl ``x*x`` H4) | Auto with real]].
Qed.

Lemma Rsqr_incr_0_var : (x,y:R) ``(Rsqr x)<=(Rsqr y)`` -> ``0<=y`` -> ``x<=y``.
Intros; Case (total_order_Rle x y); Intro; [Assumption | Cut ``y<x``; [Intro; Unfold Rsqr in H; Generalize (Rmult_lt2 y x y x H0 H0 H1 H1); Intro; Generalize (Rle_lt_trans ``x*x`` ``y*y`` ``x*x`` H H2); Intro; Elim (Rlt_antirefl ``x*x`` H3) | Auto with real]].
Qed.

Lemma Rsqr_incr_1 : (x,y:R) ``x<=y``->``0<=x``->``0<= y``->``(Rsqr x)<=(Rsqr y)``.
Intros; Unfold Rsqr; Apply Rle_Rmult_comp; Assumption.
Qed.

Lemma Rsqr_incrst_0 : (x,y:R) ``(Rsqr x)<(Rsqr y)``->``0<=x``->``0<=y``-> ``x<y``.
Intros; Case (total_order x y); Intro; [Assumption | Elim H2; Intro; [Rewrite H3 in H; Elim (Rlt_antirefl (Rsqr y) H) | Generalize (Rmult_lt2 y x y x H1 H1 H3 H3); Intro; Unfold Rsqr in H; Generalize (Rlt_trans ``x*x`` ``y*y`` ``x*x`` H H4); Intro; Elim (Rlt_antirefl ``x*x`` H5)]].
Qed.

Lemma Rsqr_incrst_1 : (x,y:R) ``x<y``->``0<=x``->``0<=y``->``(Rsqr x)<(Rsqr y)``.
Intros; Unfold Rsqr; Apply Rmult_lt2; Assumption.
Qed.

Lemma Rsqr_neg_pos_le_0 : (x,y:R) ``(Rsqr x)<=(Rsqr y)``->``0<=y``->``-y<=x``.
Intros; Case (case_Rabsolu x); Intro.
Generalize (Rlt_Ropp x ``0`` r); Rewrite Ropp_O; Intro; Generalize (Rlt_le ``0`` ``-x`` H1); Intro; Rewrite (Rsqr_neg x) in H; Generalize (Rsqr_incr_0 (Ropp x) y H H2 H0); Intro; Rewrite <- (Ropp_Ropp x); Apply Rge_Ropp; Apply Rle_sym1; Assumption.
Apply Rle_trans with ``0``; [Rewrite <- Ropp_O; Apply Rge_Ropp; Apply Rle_sym1; Assumption | Apply Rle_sym2; Assumption].
Qed.

Lemma Rsqr_neg_pos_le_1 : (x,y:R) ``(-y)<=x`` -> ``x<=y`` -> ``0<=y`` -> ``(Rsqr x)<=(Rsqr y)``.
Intros; Case (case_Rabsolu x); Intro.
Generalize (Rlt_Ropp x ``0`` r); Rewrite Ropp_O; Intro; Generalize (Rlt_le ``0`` ``-x`` H2); Intro; Generalize (Rle_Ropp ``-y`` x H); Rewrite Ropp_Ropp; Intro; Generalize (Rle_sym2 ``-x`` y H4); Intro; Rewrite (Rsqr_neg x); Apply Rsqr_incr_1; Assumption.
Generalize (Rle_sym2 ``0`` x r); Intro; Apply Rsqr_incr_1; Assumption.
Qed.

Lemma neg_pos_Rsqr_le : (x,y:R) ``(-y)<=x``->``x<=y``->``(Rsqr x)<=(Rsqr y)``.
Intros; Case (case_Rabsolu x); Intro.
Generalize (Rlt_Ropp x ``0`` r); Rewrite Ropp_O; Intro; Generalize (Rle_Ropp ``-y`` x H); Rewrite Ropp_Ropp; Intro; Generalize (Rle_sym2 ``-x`` y H2); Intro; Generalize (Rlt_le ``0`` ``-x`` H1); Intro; Generalize (Rle_trans ``0`` ``-x`` y H4 H3); Intro; Rewrite (Rsqr_neg x); Apply Rsqr_incr_1; Assumption.
Generalize (Rle_sym2 ``0`` x r); Intro; Generalize (Rle_trans ``0`` x y H1 H0); Intro; Apply Rsqr_incr_1; Assumption.
Qed.

Lemma Rsqr_abs : (x:R) ``(Rsqr x)==(Rsqr (Rabsolu x))``.
Intro; Unfold Rabsolu; Case (case_Rabsolu x); Intro; [Apply Rsqr_neg | Reflexivity].
Qed.

Lemma Rsqr_le_abs_0 : (x,y:R) ``(Rsqr x)<=(Rsqr y)`` -> ``(Rabsolu x)<=(Rabsolu y)``.
Intros; Apply Rsqr_incr_0; Repeat Rewrite <- Rsqr_abs; [Assumption | Apply Rabsolu_pos | Apply Rabsolu_pos].
Qed.

Lemma Rsqr_le_abs_1 : (x,y:R) ``(Rabsolu x)<=(Rabsolu y)`` -> ``(Rsqr x)<=(Rsqr y)``.
Intros; Rewrite (Rsqr_abs x); Rewrite (Rsqr_abs y); Apply (Rsqr_incr_1 (Rabsolu x) (Rabsolu y)  H (Rabsolu_pos x) (Rabsolu_pos y)).
Qed.

Lemma Rsqr_lt_abs_0 : (x,y:R) ``(Rsqr x)<(Rsqr y)`` -> ``(Rabsolu x)<(Rabsolu y)``.
Intros; Apply Rsqr_incrst_0; Repeat Rewrite <- Rsqr_abs; [Assumption | Apply Rabsolu_pos | Apply Rabsolu_pos].
Qed.

Lemma Rsqr_lt_abs_1 : (x,y:R) ``(Rabsolu x)<(Rabsolu y)`` -> ``(Rsqr x)<(Rsqr y)``.
Intros; Rewrite (Rsqr_abs x); Rewrite (Rsqr_abs y); Apply (Rsqr_incrst_1 (Rabsolu x) (Rabsolu y)  H (Rabsolu_pos x) (Rabsolu_pos y)).
Qed.

Lemma Rsqr_inj : (x,y:R) ``0<=x`` -> ``0<=y`` -> (Rsqr x)==(Rsqr y) -> x==y.
Intros; Generalize (Rle_le_eq (Rsqr x) (Rsqr y)); Intro; Elim H2; Intros _ H3; Generalize (H3 H1); Intro; Elim H4; Intros; Apply Rle_antisym; Apply Rsqr_incr_0; Assumption.
Qed.

Lemma Rsqr_eq_abs_0 : (x,y:R) (Rsqr x)==(Rsqr y) -> (Rabsolu x)==(Rabsolu y).
Intros; Unfold Rabsolu; Case (case_Rabsolu x); Case (case_Rabsolu y); Intros.
Rewrite -> (Rsqr_neg x) in H; Rewrite -> (Rsqr_neg y) in H; Generalize (Rlt_Ropp y ``0`` r); Generalize (Rlt_Ropp x ``0`` r0); Rewrite Ropp_O; Intros; Generalize (Rlt_le ``0`` ``-x`` H0); Generalize (Rlt_le ``0`` ``-y`` H1); Intros; Apply Rsqr_inj; Assumption.
Rewrite -> (Rsqr_neg x) in H; Generalize (Rle_sym2 ``0`` y r); Intro; Generalize (Rlt_Ropp x ``0`` r0); Rewrite Ropp_O; Intro; Generalize (Rlt_le ``0`` ``-x`` H1); Intro; Apply Rsqr_inj; Assumption.
Rewrite -> (Rsqr_neg y) in H; Generalize (Rle_sym2 ``0`` x r0); Intro; Generalize (Rlt_Ropp y ``0`` r); Rewrite Ropp_O; Intro; Generalize (Rlt_le ``0`` ``-y`` H1); Intro; Apply Rsqr_inj; Assumption.
Generalize (Rle_sym2 ``0`` x r0); Generalize (Rle_sym2 ``0`` y r); Intros; Apply Rsqr_inj; Assumption.
Qed.

Lemma Rsqr_eq_asb_1 : (x,y:R) (Rabsolu x)==(Rabsolu y) -> (Rsqr x)==(Rsqr y).
Intros; Cut ``(Rsqr (Rabsolu x))==(Rsqr (Rabsolu y))``.
Intro; Repeat Rewrite <- Rsqr_abs in H0; Assumption.
Rewrite H; Reflexivity.
Qed.

Lemma triangle_rectangle : (x,y,z:R) ``0<=z``->``(Rsqr x)+(Rsqr y)<=(Rsqr z)``->``-z<=x<=z`` /\``-z<=y<=z``.
Intros; Generalize (plus_le_is_le (Rsqr x) (Rsqr y) (Rsqr z) (pos_Rsqr y) H0); Rewrite Rplus_sym in H0; Generalize (plus_le_is_le (Rsqr y) (Rsqr x) (Rsqr z) (pos_Rsqr x) H0); Intros; Split; [Split; [Apply Rsqr_neg_pos_le_0; Assumption | Apply Rsqr_incr_0_var; Assumption] | Split; [Apply Rsqr_neg_pos_le_0; Assumption | Apply Rsqr_incr_0_var; Assumption]].
Qed.

Lemma triangle_rectangle_lt : (x,y,z:R) ``(Rsqr x)+(Rsqr y)<(Rsqr z)`` -> ``(Rabsolu x)<(Rabsolu z)``/\``(Rabsolu y)<(Rabsolu z)``.
Intros; Split; [Generalize (plus_lt_is_lt (Rsqr x) (Rsqr y) (Rsqr z) (pos_Rsqr y) H); Intro; Apply Rsqr_lt_abs_0; Assumption | Rewrite Rplus_sym in H; Generalize (plus_lt_is_lt (Rsqr y) (Rsqr x) (Rsqr z) (pos_Rsqr x) H); Intro; Apply Rsqr_lt_abs_0; Assumption].
Qed.

Lemma triangle_rectangle_le : (x,y,z:R) ``(Rsqr x)+(Rsqr y)<=(Rsqr z)`` -> ``(Rabsolu x)<=(Rabsolu z)``/\``(Rabsolu y)<=(Rabsolu z)``.
Intros; Split; [Generalize (plus_le_is_le (Rsqr x) (Rsqr y) (Rsqr z) (pos_Rsqr y) H); Intro; Apply Rsqr_le_abs_0; Assumption | Rewrite Rplus_sym in H; Generalize (plus_le_is_le (Rsqr y) (Rsqr x) (Rsqr z) (pos_Rsqr x) H); Intro; Apply Rsqr_le_abs_0; Assumption].
Qed.

Lemma Rsqr_inv : (x:R) ~``x==0`` -> ``(Rsqr (/x))==/(Rsqr x)``.
Intros; Unfold Rsqr.
Rewrite Rinv_Rmult; Try Reflexivity Orelse Assumption.
Qed.

Lemma canonical_Rsqr : (a:nonzeroreal;b,c,x:R) ``a*(Rsqr x)+b*x+c == a* (Rsqr (x+b/(2*a))) + (4*a*c - (Rsqr b))/(4*a)``.
Intros.
Rewrite Rsqr_plus.
Repeat Rewrite Rmult_Rplus_distr.
Repeat Rewrite Rplus_assoc.
Apply Rplus_plus_r.
Unfold Rdiv Rminus.
Replace ``2*1+2*1`` with ``4``; [Idtac | Ring].
Rewrite (Rmult_Rplus_distrl ``4*a*c`` ``-(Rsqr b)`` ``/(4*a)``).
Rewrite Rsqr_times.
Repeat Rewrite Rinv_Rmult.
Repeat Rewrite (Rmult_sym a).
Repeat Rewrite Rmult_assoc.
Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r.
Rewrite (Rmult_sym ``2``).
Repeat Rewrite Rmult_assoc.
Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r.
Rewrite (Rmult_sym ``/2``).
Rewrite (Rmult_sym ``2``).
Repeat Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r.
Rewrite (Rmult_sym a).
Repeat Rewrite Rmult_assoc.
Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r.
Rewrite (Rmult_sym ``2``).
Repeat Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r.
Repeat Rewrite Rplus_assoc.
Rewrite (Rplus_sym ``(Rsqr b)*((Rsqr (/a*/2))*a)``).
Repeat Rewrite Rplus_assoc.
Rewrite (Rmult_sym x).
Apply Rplus_plus_r.
Rewrite (Rmult_sym ``/a``).
Unfold Rsqr; Repeat Rewrite Rmult_assoc.
Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r.
Ring.
Apply (cond_nonzero a).
DiscrR.
Apply (cond_nonzero a).
DiscrR.
DiscrR.
Apply (cond_nonzero a).
DiscrR.
DiscrR.
DiscrR.
Apply (cond_nonzero a).
DiscrR.
Apply (cond_nonzero a).
Qed.

Lemma Rsqr_eq : (x,y:R) (Rsqr x)==(Rsqr y) -> x==y \/ x==``-y``.
Intros; Unfold Rsqr in H; Generalize (Rplus_plus_r ``-(y*y)`` ``x*x`` ``y*y`` H); Rewrite Rplus_Ropp_l; Replace ``-(y*y)+x*x`` with ``(x-y)*(x+y)``.
Intro; Generalize (without_div_Od ``x-y`` ``x+y`` H0); Intro; Elim H1; Intros.
Left; Apply Rminus_eq; Assumption.
Right; Apply Rminus_eq; Unfold Rminus; Rewrite Ropp_Ropp; Assumption.
Ring.
Qed.
