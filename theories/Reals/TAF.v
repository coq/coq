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
Require Rlimit.
Require Ranalysis1.

(* Toute fonction continue sur un compact (ferme borne de R) est majoree 
   et atteint cette borne *)
Axiom compacity_continuity : (f:R->R;a,b:R) ``a<=b`` -> ((c:R)``a<=c<=b``->(continuity_pt f c)) -> (EXT Mx : R |  ((c:R)``a<=c<=b``->``(f c)<=(f Mx)``)/\``a<=Mx<=b``).

Lemma compacity_continuity_cor : (f:R->R;a,b:R) ``a<=b`` -> ((c:R)``a<=c<=b``->(continuity_pt f c)) -> (EXT mx : R | ((c:R)``a<=c<=b``->``(f mx)<=(f c)``)/\``a<=mx<=b``).
Intros; Cut (c:R)``a <= c <= b``->(continuity_pt (opp_fct f) c).
Intro; Assert H2 := (compacity_continuity (opp_fct f) a b H H1).
Elim H2; Intros x0 H3.
Exists x0; Intros; Split.
Intros; Rewrite <- (Ropp_Ropp (f x0)); Rewrite <- (Ropp_Ropp (f c)); Apply Rle_Ropp1.
Elim H3; Intros; Unfold opp_fct in H5; Apply H5; Apply H4.
Elim H3; Intros; Assumption.
Intros; Apply continuity_pt_opp.
Apply H0; Apply H1.
Qed.

(* Th�or�me des accroissements finis g�n�ralis�s *)
Theorem TAF_gen : (f,g:R->R;a,b:R;pr1:(c:R)``a<c<b``->(derivable_pt f c);pr2:(c:R)``a<c<b``->(derivable_pt g c)) ``a<b`` -> ((c:R)``a<=c<=b``->(continuity_pt f c)) -> ((c:R)``a<=c<=b``->(continuity_pt g c)) -> (EXT c : R | (EXT P : ``a<c<b`` | ``((g b)-(g a))*(derive_pt f c (pr1 c P))==((f b)-(f a))*(derive_pt g c (pr2 c P))``)).
Intros; Assert H2 := (Rlt_le ? ? H).
Pose h := [y:R]``((g b)-(g a))*(f y)-((f b)-(f a))*(g y)``.
Cut (c:R)``a<c<b``->(derivable_pt h c).
Intro; Cut (c:R)``a<=c<=b``->(continuity_pt h c).
Intro; Assert H4 := (compacity_continuity h a b H2 H3).
Assert H5 := (compacity_continuity_cor h a b H2 H3).
Elim H4; Intros Mx H6.
Elim H5; Intros mx H7.
Cut (h a)==(h b).
Intro; Pose M := (h Mx); Pose m := (h mx).
Cut (c:R;P:``a<c<b``) (derive_pt h c (X c P))==``((g b)-(g a))*(derive_pt f c (pr1 c P))-((f b)-(f a))*(derive_pt g c (pr2 c P))``.
Intro; Case (Req_EM (h a) M); Intro.
Case (Req_EM (h a) m); Intro.
Cut ((c:R)``a<=c<=b``->(h c)==M).
Intro; Cut ``a<(a+b)/2<b``.
(*** h constant ***)
Intro; Exists ``(a+b)/2``.
Exists H13.
Apply Rminus_eq; Rewrite <- H9; Apply deriv_constant2 with a b.
Elim H13; Intros; Assumption.
Elim H13; Intros; Assumption.
Intros; Rewrite (H12 ``(a+b)/2``).
Apply H12; Split; Left; Assumption.
Elim H13; Intros; Split; Left; Assumption.
Split.
Apply Rlt_monotony_contra with ``2``.
Sup0.
Unfold Rdiv; Rewrite <- (Rmult_sym ``/2``); Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym.
Rewrite Rmult_1l; Rewrite double; Apply Rlt_compatibility; Apply H.
DiscrR.
Apply Rlt_monotony_contra with ``2``.
Sup0.
Unfold Rdiv; Rewrite <- (Rmult_sym ``/2``); Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym.
Rewrite Rmult_1l; Rewrite Rplus_sym; Rewrite double; Apply Rlt_compatibility; Apply H.
DiscrR.
Intros; Elim H6; Intros H13 _.
Elim H7; Intros H14 _.
Apply Rle_antisym.
Apply H13; Apply H12.
Rewrite H10 in H11; Rewrite H11; Apply H14; Apply H12.
Cut ``a<mx<b``.
(*** h admet un minimum global sur [a,b] ***)
Intro; Exists mx.
Exists H12.
Apply Rminus_eq; Rewrite <- H9; Apply deriv_minimum with a b.
Elim H12; Intros; Assumption.
Elim H12; Intros; Assumption.
Intros; Elim H7; Intros.
Apply H15; Split; Left; Assumption.
Elim H7; Intros _ H12; Elim H12; Intros; Split.
Inversion H13.
Apply H15.
Rewrite H15 in H11; Elim H11; Reflexivity.
Inversion H14.
Apply H15.
Rewrite H8 in H11; Rewrite <- H15 in H11; Elim H11; Reflexivity.
Cut ``a<Mx<b``.
(*** h admet un maximum global sur [a,b] ***)
Intro; Exists Mx.
Exists H11.
Apply Rminus_eq; Rewrite <- H9; Apply deriv_maximum with a b.
Elim H11; Intros; Assumption.
Elim H11; Intros; Assumption.
Intros; Elim H6; Intros; Apply H14.
Split; Left; Assumption.
Elim H6; Intros _ H11; Elim H11; Intros; Split.
Inversion H12.
Apply H14.
Rewrite H14 in H10; Elim H10; Reflexivity.
Inversion H13.
Apply H14.
Rewrite H8 in H10; Rewrite <- H14 in H10; Elim H10; Reflexivity.
Intros; Unfold h; Replace (derive_pt [y:R]``((g b)-(g a))*(f y)-((f b)-(f a))*(g y)`` c (X c P)) with (derive_pt (minus_fct (mult_fct (fct_cte ``(g b)-(g a)``) f) (mult_fct (fct_cte ``(f b)-(f a)``) g)) c (derivable_pt_minus ? ? ? (derivable_pt_mult ? ? ? (derivable_pt_const ``(g b)-(g a)`` c) (pr1 c P)) (derivable_pt_mult ? ? ? (derivable_pt_const ``(f b)-(f a)`` c) (pr2 c P)))); [Idtac | Apply pr_nu].
Rewrite derive_pt_minus; Do 2 Rewrite derive_pt_mult; Do 2 Rewrite derive_pt_const; Do 2 Rewrite Rmult_Ol; Do 2 Rewrite Rplus_Ol; Reflexivity.
Unfold h; Ring.
Intros; Unfold h; Change (continuity_pt (minus_fct (mult_fct (fct_cte ``(g b)-(g a)``) f) (mult_fct (fct_cte ``(f b)-(f a)``) g)) c).
Apply continuity_pt_minus; Apply continuity_pt_mult.
Apply derivable_continuous_pt; Apply derivable_pt_const.
Apply (H0 ? H3).
Apply derivable_continuous_pt; Apply derivable_pt_const.
Apply (H1 ? H3).
Intros; Change (derivable_pt (minus_fct (mult_fct (fct_cte ``(g b)-(g a)``) f) (mult_fct (fct_cte ``(f b)-(f a)``) g)) c).
Apply derivable_pt_minus; Apply derivable_pt_mult.
Apply derivable_pt_const.
Apply (pr1 ? H3).
Apply derivable_pt_const.
Apply (pr2 ? H3).
Qed.

(* Une version plus faible (mais usuelle ) *)
Lemma TAF : (f:(R->R); a,b:R; pr:(derivable f)) ``a < b``->(EXT c:R | ``(f b)-(f a) == (derive_pt f c (pr c))*(b-a)``/\``a < c < b``).
Intros; Cut (c:R)``a<c<b``->(derivable_pt f c); [Intro | Intros; Apply pr].
Cut (c:R)``a<c<b``->(derivable_pt id c); [Intro | Intros; Apply derivable_pt_id].
Cut (c:R)``a<=c<=b``->(continuity_pt f c); [Intro | Intros; Apply derivable_continuous_pt; Apply pr].
Cut (c:R)``a<=c<=b``->(continuity_pt id c); [Intro | Intros; Apply derivable_continuous_pt; Apply derivable_pt_id].
Assert H2 := (TAF_gen f id a b X X0 H H0 H1).
Elim H2; Intros c H3; Elim H3; Intros.
Exists c; Split.
Cut (derive_pt id c (X0 c x)) == (derive_pt id c (derivable_pt_id c)); [Intro | Apply pr_nu].
Rewrite H5 in H4; Rewrite (derive_pt_id c) in H4; Rewrite Rmult_1r in H4; Rewrite <- H4; Replace (derive_pt f c (X c x)) with (derive_pt f c (pr c)); [Idtac | Apply pr_nu]; Apply Rmult_sym.
Apply x.
Qed.

(*** Corollaires ***)

(**********)
Lemma nonneg_derivative_1 : (f:R->R;pr:(derivable f)) ((x:R) ``0<=(derive_pt f x (pr x))``) -> (increasing f).
Intros.
Unfold increasing.
Intros.
Case (total_order_T x y); Intro.
Elim s; Intro.
Apply Rle_anti_compatibility with ``-(f x)``.
Rewrite Rplus_Ropp_l; Rewrite Rplus_sym.
Assert H1 := (TAF f ? ? pr a).
Elim H1; Intros.
Elim H2; Intros.
Unfold Rminus in H3.
Rewrite H3.
Apply Rmult_le_pos.
Apply H.
Apply Rle_anti_compatibility with x.
Rewrite Rplus_Or; Replace ``x+(y+ -x)`` with y; [Assumption | Ring].
Rewrite b; Right; Reflexivity.
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H0 r)).
Qed.
 
(**********)
Lemma nonpos_derivative_0 : (f:R->R;pr:(derivable f)) (decreasing f) -> ((x:R) ``(derive_pt f x (pr x))<=0``).
Intros; Assert H0 :=H; Unfold decreasing in H0; Generalize (derivable_derive f x (pr x)); Intro; Elim H1; Intros l H2.
Rewrite H2; Case (total_order l R0); Intro.
Left; Assumption.
Elim H3; Intro.
Right; Assumption.
Generalize (derive_pt_eq_1 f x l (pr x) H2); Intros; Cut ``0< (l/2)``.
Intro; Elim (H5 ``(l/2)`` H6); Intros delta H7; Cut ``delta/2<>0``/\``0<delta/2``/\``(Rabsolu delta/2)<delta``.
Intro; Decompose [and] H8; Intros; Generalize (H7 ``delta/2`` H9 H12); Cut ``((f (x+delta/2))-(f x))/(delta/2)<=0``.
Intro; Cut ``0< -(((f (x+delta/2))-(f x))/(delta/2)-l)``.
Intro; Unfold Rabsolu; Case (case_Rabsolu ``((f (x+delta/2))-(f x))/(delta/2)-l``).
Intros; Generalize (Rlt_compatibility_r ``-l`` ``-(((f (x+delta/2))-(f x))/(delta/2)-l)`` ``(l/2)`` H14); Unfold Rminus.
Replace ``(l/2)+ -l`` with ``-(l/2)``.
Replace `` -(((f (x+delta/2))+ -(f x))/(delta/2)+ -l)+ -l`` with ``-(((f (x+delta/2))+ -(f x))/(delta/2))``.
Intro.
Generalize (Rlt_Ropp ``-(((f (x+delta/2))+ -(f x))/(delta/2))`` ``-(l/2)`` H15). 
Repeat Rewrite Ropp_Ropp.
Intro.
Generalize (Rlt_trans ``0`` ``l/2`` ``((f (x+delta/2))-(f x))/(delta/2)`` H6 H16); Intro.
Elim (Rlt_antirefl ``0`` (Rlt_le_trans ``0`` ``((f (x+delta/2))-(f x))/(delta/2)`` ``0`` H17 H10)).
Ring.
Pattern 3 l; Rewrite double_var.
Ring.
Intros.
Generalize (Rge_Ropp ``((f (x+delta/2))-(f x))/(delta/2)-l`` ``0`` r).
Rewrite Ropp_O.
Intro.
Elim (Rlt_antirefl ``0`` (Rlt_le_trans ``0`` ``-(((f (x+delta/2))-(f x))/(delta/2)-l)`` ``0`` H13 H15)).
Replace ``-(((f (x+delta/2))-(f x))/(delta/2)-l)`` with ``(((f (x))-(f (x+delta/2)))/(delta/2)) +l``.
Unfold Rminus.
Apply ge0_plus_gt0_is_gt0.
Unfold Rdiv; Apply Rmult_le_pos.
Cut ``x<=(x+(delta*/2))``.
Intro; Generalize (H0 x ``x+(delta*/2)`` H13); Intro; Generalize (Rle_compatibility ``-(f (x+delta/2))`` ``(f (x+delta/2))`` ``(f x)`` H14); Rewrite Rplus_Ropp_l; Rewrite Rplus_sym; Intro; Assumption.
Pattern 1 x; Rewrite <- (Rplus_Or x); Apply Rle_compatibility; Left; Assumption.
Left; Apply Rlt_Rinv; Assumption.
Assumption.
Rewrite Ropp_distr2.
Unfold Rminus.
Rewrite (Rplus_sym l).
Unfold Rdiv.
Rewrite <- Ropp_mul1.
Rewrite Ropp_distr1.
Rewrite Ropp_Ropp.
Rewrite (Rplus_sym (f x)).
Reflexivity.
Replace ``((f (x+delta/2))-(f x))/(delta/2)`` with ``-(((f x)-(f (x+delta/2)))/(delta/2))``.
Rewrite <- Ropp_O.
Apply Rge_Ropp.
Apply Rle_sym1.
Unfold Rdiv; Apply Rmult_le_pos.
Cut ``x<=(x+(delta*/2))``.
Intro; Generalize (H0 x ``x+(delta*/2)`` H10); Intro.
Generalize (Rle_compatibility ``-(f (x+delta/2))`` ``(f (x+delta/2))`` ``(f x)`` H13); Rewrite Rplus_Ropp_l; Rewrite Rplus_sym; Intro; Assumption.
Pattern 1 x; Rewrite <- (Rplus_Or x); Apply Rle_compatibility; Left; Assumption.
Left; Apply Rlt_Rinv; Assumption.
Unfold Rdiv; Rewrite <- Ropp_mul1.
Rewrite Ropp_distr2.
Reflexivity.
Split.
Unfold Rdiv; Apply prod_neq_R0.
Generalize (cond_pos delta); Intro; Red; Intro H9; Rewrite H9 in H8; Elim (Rlt_antirefl ``0`` H8).
Apply Rinv_neq_R0; DiscrR.
Split.
Unfold Rdiv; Apply Rmult_lt_pos; [Apply (cond_pos delta) | Apply Rlt_Rinv; Sup0].
Rewrite Rabsolu_right.
Unfold Rdiv; Apply Rlt_monotony_contra with ``2``.
Sup0.
Rewrite <- (Rmult_sym ``/2``); Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym.
Rewrite Rmult_1l; Rewrite double; Pattern 1 (pos delta); Rewrite <- Rplus_Or.
Apply Rlt_compatibility; Apply (cond_pos delta).
DiscrR.
Apply Rle_sym1; Unfold Rdiv; Left; Apply Rmult_lt_pos.
Apply (cond_pos delta).
Apply Rlt_Rinv; Sup0.
Unfold Rdiv; Apply Rmult_lt_pos; [Apply H4 | Apply Rlt_Rinv; Sup0].
Qed.

(**********)
Lemma increasing_decreasing_opp : (f:R->R) (increasing f) -> (decreasing (opp_fct f)).
Unfold increasing decreasing opp_fct; Intros; Generalize (H x y H0); Intro; Apply Rge_Ropp; Apply Rle_sym1; Assumption.
Qed.

(**********)
Lemma nonpos_derivative_1 : (f:R->R;pr:(derivable f)) ((x:R) ``(derive_pt f x (pr x))<=0``) -> (decreasing f).
Intros.
Cut (h:R)``-(-(f h))==(f h)``.
Intro.
Generalize (increasing_decreasing_opp (opp_fct f)).
Unfold decreasing.
Unfold opp_fct.
Intros.
Rewrite <- (H0 x); Rewrite <- (H0 y).
Apply H1.
Cut (x:R)``0<=(derive_pt (opp_fct f) x ((derivable_opp f pr) x))``.
Intros.
Replace [x:R]``-(f x)`` with (opp_fct f); [Idtac | Reflexivity].
Apply (nonneg_derivative_1 (opp_fct f) (derivable_opp f pr) H3).
Intro.
Assert H3 := (derive_pt_opp f x0 (pr x0)).
Cut ``(derive_pt (opp_fct f) x0 (derivable_pt_opp f x0 (pr x0)))==(derive_pt (opp_fct f) x0 (derivable_opp f pr x0))``.
Intro.
Rewrite <- H4.
Rewrite H3.
Rewrite <- Ropp_O; Apply Rge_Ropp; Apply Rle_sym1; Apply (H x0).
Apply pr_nu.
Assumption.
Intro; Ring.
Qed.
 
(**********)
Lemma positive_derivative : (f:R->R;pr:(derivable f)) ((x:R) ``0<(derive_pt f x (pr x))``)->(strict_increasing f).
Intros.
Unfold strict_increasing.
Intros.
Apply Rlt_anti_compatibility with ``-(f x)``.
Rewrite Rplus_Ropp_l; Rewrite Rplus_sym.
Assert H1 := (TAF f ? ? pr H0).
Elim H1; Intros.
Elim H2; Intros.
Unfold Rminus in H3.
Rewrite H3.
Apply Rmult_lt_pos.
Apply H.
Apply Rlt_anti_compatibility with x.
Rewrite Rplus_Or; Replace ``x+(y+ -x)`` with y; [Assumption | Ring].
Qed.

(**********)
Lemma strictincreasing_strictdecreasing_opp : (f:R->R) (strict_increasing f) ->
(strict_decreasing (opp_fct f)).
Unfold strict_increasing strict_decreasing opp_fct; Intros; Generalize (H x y H0); Intro; Apply Rlt_Ropp; Assumption.
Qed.
 
(**********)
Lemma negative_derivative : (f:R->R;pr:(derivable f)) ((x:R) ``(derive_pt f x (pr x))<0``)->(strict_decreasing f).
Intros.
Cut (h:R)``- (-(f h))==(f h)``.
Intros.
Generalize (strictincreasing_strictdecreasing_opp (opp_fct f)).
Unfold strict_decreasing opp_fct.
Intros.
Rewrite <- (H0 x).
Rewrite <- (H0 y).
Apply H1; [Idtac | Assumption].
Cut (x:R)``0<(derive_pt (opp_fct f) x (derivable_opp f pr x))``.
Intros; EApply positive_derivative; Apply H3.
Intro.
Assert H3 := (derive_pt_opp f x0 (pr x0)).
Cut ``(derive_pt (opp_fct f) x0 (derivable_pt_opp f x0 (pr x0)))==(derive_pt (opp_fct f) x0 (derivable_opp f pr x0))``.
Intro.
Rewrite <- H4; Rewrite H3.
Rewrite <- Ropp_O; Apply Rlt_Ropp; Apply (H x0).
Apply pr_nu.
Intro; Ring.
Qed.
 
(**********)
Lemma null_derivative_0 : (f:R->R;pr:(derivable f)) (constant f)->((x:R) ``(derive_pt f x (pr x))==0``). 
Intros.
Unfold constant in H.
Apply derive_pt_eq_0.
Intros; Exists (mkposreal ``1`` Rlt_R0_R1); Simpl; Intros.
Rewrite (H x ``x+h``); Unfold Rminus; Unfold Rdiv; Rewrite Rplus_Ropp_r; Rewrite Rmult_Ol; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Assumption.
Qed.

(**********)
Lemma increasing_decreasing : (f:R->R) (increasing f) -> (decreasing f) -> (constant f).
Unfold increasing decreasing constant; Intros; Case (total_order x y); Intro.
Generalize (Rlt_le x y H1); Intro; Apply (Rle_antisym (f x) (f y) (H x y H2) (H0 x y H2)).
Elim H1; Intro.
Rewrite H2; Reflexivity.
Generalize (Rlt_le y x H2); Intro; Symmetry; Apply (Rle_antisym (f y) (f x) (H y x H3) (H0 y x H3)).
Qed.

(**********)
Lemma null_derivative_1 : (f:R->R;pr:(derivable f)) ((x:R) ``(derive_pt f x (pr x))==0``)->(constant f).
Intros.
Cut (x:R)``(derive_pt f x (pr x)) <= 0``.
Cut (x:R)``0 <= (derive_pt f x (pr x))``.
Intros.
Assert H2 := (nonneg_derivative_1 f pr H0).
Assert H3 := (nonpos_derivative_1 f  pr H1).
Apply increasing_decreasing; Assumption.
Intro; Right; Symmetry; Apply (H x).
Intro; Right; Apply (H x).
Qed.

(**********)
Lemma derive_increasing_interv_ax : (a,b:R;f:R->R;pr:(derivable f)) ``a<b``-> (((t:R) ``a<t<b`` -> ``0<(derive_pt f t (pr t))``) -> ((x,y:R) ``a<=x<=b``->``a<=y<=b``->``x<y``->``(f x)<(f y)``)) /\ (((t:R) ``a<t<b`` -> ``0<=(derive_pt f t (pr t))``) -> ((x,y:R) ``a<=x<=b``->``a<=y<=b``->``x<y``->``(f x)<=(f y)``)).
Intros.
Split; Intros.
Apply Rlt_anti_compatibility with ``-(f x)``.
Rewrite Rplus_Ropp_l; Rewrite Rplus_sym.
Assert H4 := (TAF f ? ? pr H3).
Elim H4; Intros.
Elim H5; Intros.
Unfold Rminus in H6.
Rewrite H6.
Apply Rmult_lt_pos.
Apply H0.
Elim H7; Intros.
Split.
Elim H1; Intros.
Apply Rle_lt_trans with x; Assumption.
Elim H2; Intros.
Apply Rlt_le_trans with y; Assumption.
Apply Rlt_anti_compatibility with x.
Rewrite Rplus_Or; Replace ``x+(y+ -x)`` with y; [Assumption | Ring].
Apply Rle_anti_compatibility with ``-(f x)``.
Rewrite Rplus_Ropp_l; Rewrite Rplus_sym.
Assert H4 := (TAF f ? ? pr H3).
Elim H4; Intros.
Elim H5; Intros.
Unfold Rminus in H6.
Rewrite H6.
Apply Rmult_le_pos.
Apply H0.
Elim H7; Intros.
Split.
Elim H1; Intros.
Apply Rle_lt_trans with x; Assumption.
Elim H2; Intros.
Apply Rlt_le_trans with y; Assumption.
Apply Rle_anti_compatibility with x.
Rewrite Rplus_Or; Replace ``x+(y+ -x)`` with y; [Left; Assumption | Ring].
Qed.

(**********)
Lemma derive_increasing_interv : (a,b:R;f:R->R;pr:(derivable f)) ``a<b``-> ((t:R) ``a<t<b`` -> ``0<(derive_pt f t (pr t))``) -> ((x,y:R) ``a<=x<=b``->``a<=y<=b``->``x<y``->``(f x)<(f y)``).
Intros.
Generalize (derive_increasing_interv_ax a b f pr H); Intro.
Elim H4; Intros H5 _; Apply (H5 H0 x y H1 H2 H3).
Qed.

(**********)
Lemma derive_increasing_interv_var : (a,b:R;f:R->R;pr:(derivable f)) ``a<b``-> ((t:R) ``a<t<b`` -> ``0<=(derive_pt f t (pr t))``) -> ((x,y:R) ``a<=x<=b``->``a<=y<=b``->``x<y``->``(f x)<=(f y)``).
Intros; Generalize (derive_increasing_interv_ax a b f pr H); Intro; Elim H4; Intros _ H5; Apply (H5 H0 x y H1 H2 H3).
Qed.

(**********)
(**********)
Theorem IAF : (f:R->R;a,b,k:R;pr:(derivable f)) ``a<=b`` -> ((c:R) ``a<=c<=b`` -> ``(derive_pt f c (pr c))<=k``) -> ``(f b)-(f a)<=k*(b-a)``.
Intros.
Case (total_order_T a b); Intro.
Elim s; Intro.
Assert H1 := (TAF f ? ? pr a0).
Elim H1; Intros.
Elim H2; Intros.
Rewrite H3.
Do 2 Rewrite <- (Rmult_sym ``(b-a)``).
Apply Rle_monotony.
Apply Rle_anti_compatibility with ``a``; Rewrite Rplus_Or.
Replace ``a+(b-a)`` with b; [Assumption | Ring].
Apply H0.
Elim H4; Intros.
Split; Left; Assumption.
Rewrite b0.
Unfold Rminus; Do 2 Rewrite Rplus_Ropp_r.
Rewrite Rmult_Or; Right; Reflexivity.
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H r)).
Qed.

Lemma IAF_var : (f,g:R->R;a,b:R;pr1:(derivable f);pr2:(derivable g)) ``a<=b`` -> ((c:R) ``a<=c<=b`` -> ``(derive_pt g c (pr2 c))<=(derive_pt f c (pr1 c))``) -> ``(g b)-(g a)<=(f b)-(f a)``.
Intros.
Cut (derivable (minus_fct g f)).
Intro.
Cut (c:R)``a<=c<=b``->``(derive_pt (minus_fct g f) c (X c))<=0``.
Intro. 
Assert H2 := (IAF (minus_fct g f) a b R0 X H H1).
Rewrite Rmult_Ol in H2; Unfold minus_fct in H2.
Apply Rle_anti_compatibility with ``-(f b)+(f a)``.
Replace ``-(f b)+(f a)+((f b)-(f a))`` with R0; [Idtac | Ring].
Replace ``-(f b)+(f a)+((g b)-(g a))`` with ``(g b)-(f b)-((g a)-(f a))``; [Apply H2 | Ring].
Intros.
Cut (derive_pt (minus_fct g f) c (X c))==(derive_pt (minus_fct g f) c (derivable_pt_minus ? ? ? (pr2 c) (pr1 c))).
Intro.
Rewrite H2.
Rewrite derive_pt_minus.
Apply Rle_anti_compatibility with (derive_pt f c (pr1 c)).
Rewrite Rplus_Or.
Replace ``(derive_pt f c (pr1 c))+((derive_pt g c (pr2 c))-(derive_pt f c (pr1 c)))`` with ``(derive_pt g c (pr2 c))``; [Idtac | Ring].
Apply H0; Assumption.
Apply pr_nu.
Apply derivable_minus; Assumption.
Qed.