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
Require Rtrigo.
Require Ranalysis.
V7only [Import R_scope.]. Open Local Scope R_scope.

(*******************************************)
(*            Newton's Integral            *)
(*******************************************)

Definition Newton_integrable [f:R->R;a,b:R] : Type := (sigTT ? [g:R->R](antiderivative f g a b)\/(antiderivative f g b a)).

Definition NewtonInt [f:R->R;a,b:R;pr:(Newton_integrable f a b)] : R := let g = Cases pr of (existTT a b) => a end in ``(g b)-(g a)``.

(* If f is differentiable, then f' is Newton integrable (Tautology ?) *)
Lemma FTCN_step1 : (f:Differential;a,b:R) (Newton_integrable [x:R](derive_pt f x (cond_diff f x)) a b).
Intros f a b; Unfold Newton_integrable; Apply existTT with (d1 f); Unfold antiderivative; Intros; Case (total_order_Rle a b); Intro; [Left; Split; [Intros; Exists (cond_diff f x); Reflexivity | Assumption] | Right; Split; [Intros; Exists (cond_diff f x); Reflexivity | Auto with real]].
Defined.

(* By definition, we have the Fondamental Theorem of Calculus *)
Lemma FTC_Newton : (f:Differential;a,b:R) (NewtonInt [x:R](derive_pt f x (cond_diff f x)) a b (FTCN_step1 f a b))==``(f b)-(f a)``.
Intros; Unfold NewtonInt; Reflexivity.
Qed.

(* $\int_a^a f$ exists forall a:R and f:R->R *)
Lemma NewtonInt_P1 : (f:R->R;a:R) (Newton_integrable f a a).
Intros f a; Unfold Newton_integrable; Apply existTT with (mult_fct (fct_cte (f a)) id); Left; Unfold antiderivative; Split.
Intros; Assert H1 : (derivable_pt (mult_fct (fct_cte (f a)) id) x).
Apply derivable_pt_mult.
Apply derivable_pt_const.
Apply derivable_pt_id.
Exists H1; Assert H2 : x==a.
Elim H; Intros; Apply Rle_antisym; Assumption.
Symmetry; Apply derive_pt_eq_0; Replace (f x) with ``0*(id x)+(fct_cte (f a) x)*1``; [Apply (derivable_pt_lim_mult (fct_cte (f a)) id x); [Apply derivable_pt_lim_const | Apply derivable_pt_lim_id] | Unfold id fct_cte; Rewrite H2; Ring].
Right; Reflexivity.
Defined.

(* $\int_a^a f = 0$ *)
Lemma NewtonInt_P2 : (f:R->R;a:R) ``(NewtonInt f a a (NewtonInt_P1 f a))==0``.
Intros; Unfold NewtonInt; Simpl; Unfold mult_fct fct_cte id; Ring.
Qed.

(* If $\int_a^b f$ exists, then $\int_b^a f$ exists too *)
Lemma NewtonInt_P3 : (f:R->R;a,b:R;X:(Newton_integrable f a b)) (Newton_integrable f b a).
Unfold Newton_integrable; Intros; Elim X; Intros g H; Apply existTT with g; Tauto.
Defined.

(* $\int_a^b f = -\int_b^a f$ *)
Lemma NewtonInt_P4 : (f:R->R;a,b:R;pr:(Newton_integrable f a b)) ``(NewtonInt f a b pr)==-(NewtonInt f b a (NewtonInt_P3 f a b pr))``.
Intros; Unfold Newton_integrable in pr; Elim pr; Intros; Elim p; Intro.
Unfold NewtonInt; Case (NewtonInt_P3 f a b (existTT R->R [g:(R->R)](antiderivative f g a b)\/(antiderivative f g b a) x p)).
Intros; Elim o; Intro.
Unfold antiderivative in H0; Elim H0; Intros; Elim H2; Intro.
Unfold antiderivative in H; Elim H; Intros; Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H5 H3)).
Rewrite H3; Ring.
Assert H1 := (antiderivative_Ucte f x x0 a b H H0); Elim H1; Intros; Unfold antiderivative in H0; Elim H0; Clear H0; Intros _ H0.
Assert H3 : ``a<=a<=b``.
Split; [Right; Reflexivity | Assumption].
Assert H4 : ``a<=b<=b``.
Split; [Assumption | Right; Reflexivity].
Assert H5 := (H2 ? H3); Assert H6 := (H2 ? H4); Rewrite H5; Rewrite H6; Ring.
Unfold NewtonInt; Case (NewtonInt_P3 f a b (existTT R->R [g:(R->R)](antiderivative f g a b)\/(antiderivative f g b a) x p)); Intros; Elim o; Intro.
Assert H1 := (antiderivative_Ucte f x x0 b a H H0); Elim H1; Intros; Unfold antiderivative in H0; Elim H0; Clear H0; Intros _ H0.
Assert H3 : ``b<=a<=a``.
Split; [Assumption | Right; Reflexivity].
Assert H4 : ``b<=b<=a``.
Split; [Right; Reflexivity | Assumption].
Assert H5 := (H2 ? H3); Assert H6 := (H2 ? H4); Rewrite H5; Rewrite H6; Ring.
Unfold antiderivative in H0; Elim H0; Intros; Elim H2; Intro.
Unfold antiderivative in H; Elim H; Intros; Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H5 H3)).
Rewrite H3; Ring.
Qed.

(* The set of Newton integrable functions is a vectorial space *)
Lemma NewtonInt_P5 : (f,g:R->R;l,a,b:R) (Newton_integrable f a b) -> (Newton_integrable g a b) -> (Newton_integrable [x:R]``l*(f x)+(g x)`` a b).
Unfold Newton_integrable; Intros; Elim X; Intros; Elim X0; Intros; Exists [y:R]``l*(x y)+(x0 y)``.
Elim p; Intro.
Elim p0; Intro.
Left; Unfold antiderivative; Unfold antiderivative in H H0; Elim H; Clear H; Intros; Elim H0; Clear H0; Intros H0 _.
Split.
Intros; Elim (H ? H2); Elim (H0 ? H2); Intros.
Assert H5 : (derivable_pt [y:R]``l*(x y)+(x0 y)`` x1).
Reg.
Exists H5; Symmetry; Reg; Rewrite <- H3; Rewrite <- H4; Reflexivity.
Assumption.
Unfold antiderivative in H H0; Elim H; Elim H0; Intros; Elim H4; Intro.
Elim (Rlt_antirefl ? (Rlt_le_trans ? ? ? H5 H2)).
Left; Rewrite <- H5; Unfold antiderivative; Split.
Intros; Elim H6; Intros; Assert H9 : ``x1==a``.
Apply Rle_antisym; Assumption.
Assert H10 : ``a<=x1<=b``.
Split; Right; [Symmetry; Assumption | Rewrite <- H5; Assumption].
Assert H11 : ``b<=x1<=a``.
Split; Right; [Rewrite <- H5; Symmetry; Assumption | Assumption].
Assert H12 : (derivable_pt x x1).
Unfold derivable_pt; Exists (f x1); Elim (H3 ? H10); Intros; EApply derive_pt_eq_1; Symmetry; Apply H12.
Assert H13 : (derivable_pt x0 x1).
Unfold derivable_pt; Exists (g x1); Elim (H1 ? H11); Intros; EApply derive_pt_eq_1; Symmetry; Apply H13.
Assert H14 : (derivable_pt [y:R]``l*(x y)+(x0 y)`` x1).
Reg.
Exists H14; Symmetry; Reg.
Assert H15 : ``(derive_pt x0 x1 H13)==(g x1)``.
Elim (H1 ? H11); Intros; Rewrite H15; Apply pr_nu.
Assert H16 : ``(derive_pt x x1 H12)==(f x1)``.
Elim (H3 ? H10); Intros; Rewrite H16; Apply pr_nu.
Rewrite H15; Rewrite H16; Ring.
Right; Reflexivity.
Elim p0; Intro.
Unfold antiderivative in H H0; Elim H; Elim H0; Intros; Elim H4; Intro.
Elim (Rlt_antirefl ? (Rlt_le_trans ? ? ? H5 H2)).
Left; Rewrite H5; Unfold antiderivative; Split.
Intros; Elim H6; Intros; Assert H9 : ``x1==a``.
Apply Rle_antisym; Assumption.
Assert H10 : ``a<=x1<=b``.
Split; Right; [Symmetry; Assumption | Rewrite H5; Assumption].
Assert H11 : ``b<=x1<=a``.
Split; Right; [Rewrite H5; Symmetry; Assumption | Assumption].
Assert H12 : (derivable_pt x x1).
Unfold derivable_pt; Exists (f x1); Elim (H3 ? H11); Intros; EApply derive_pt_eq_1; Symmetry; Apply H12.
Assert H13 : (derivable_pt x0 x1).
Unfold derivable_pt; Exists (g x1); Elim (H1 ? H10); Intros; EApply derive_pt_eq_1; Symmetry; Apply H13.
Assert H14 : (derivable_pt [y:R]``l*(x y)+(x0 y)`` x1).
Reg.
Exists H14; Symmetry; Reg.
Assert H15 : ``(derive_pt x0 x1 H13)==(g x1)``.
Elim (H1 ? H10); Intros; Rewrite H15; Apply pr_nu.
Assert H16 : ``(derive_pt x x1 H12)==(f x1)``.
Elim (H3 ? H11); Intros; Rewrite H16; Apply pr_nu.
Rewrite H15; Rewrite H16; Ring.
Right; Reflexivity.
Right; Unfold antiderivative; Unfold antiderivative in H H0; Elim H; Clear H; Intros; Elim H0; Clear H0; Intros H0 _; Split.
Intros; Elim (H ? H2); Elim (H0 ? H2); Intros.
Assert H5 : (derivable_pt [y:R]``l*(x y)+(x0 y)`` x1).
Reg.
Exists H5; Symmetry; Reg; Rewrite <- H3; Rewrite <- H4; Reflexivity.
Assumption.
Defined.

(**********)
Lemma antiderivative_P1 : (f,g,F,G:R->R;l,a,b:R) (antiderivative f F a b) -> (antiderivative g G a b) -> (antiderivative [x:R]``l*(f x)+(g x)`` [x:R]``l*(F x)+(G x)`` a b).
Unfold antiderivative; Intros; Elim H; Elim H0; Clear H H0; Intros; Split.
Intros; Elim (H ? H3); Elim (H1 ? H3); Intros.
Assert H6 : (derivable_pt [x:R]``l*(F x)+(G x)`` x).
Reg.
Exists H6; Symmetry; Reg; Rewrite <- H4; Rewrite <- H5; Ring.
Assumption.
Qed.

(* $\int_a^b \lambda f + g = \lambda \int_a^b f + \int_a^b f *)
Lemma NewtonInt_P6 : (f,g:R->R;l,a,b:R;pr1:(Newton_integrable f a b);pr2:(Newton_integrable g a b)) (NewtonInt [x:R]``l*(f x)+(g x)`` a b (NewtonInt_P5 f g l a b pr1 pr2))==``l*(NewtonInt f a b pr1)+(NewtonInt g a b pr2)``.
Intros f g l a b pr1 pr2; Unfold NewtonInt; Case (NewtonInt_P5 f g l a b pr1 pr2); Intros; Case pr1; Intros; Case pr2; Intros; Case (total_order_T a b); Intro.
Elim s; Intro.
Elim o; Intro.
Elim o0; Intro.
Elim o1; Intro.
Assert H2 := (antiderivative_P1 f g x0 x1 l a b H0 H1); Assert H3 := (antiderivative_Ucte ? ? ? ? ? H H2); Elim H3; Intros; Assert H5 : ``a<=a<=b``.
Split; [Right; Reflexivity | Left; Assumption].
Assert H6 : ``a<=b<=b``.
Split; [Left; Assumption | Right; Reflexivity].
Assert H7 := (H4 ? H5); Assert H8 := (H4 ? H6); Rewrite H7; Rewrite H8; Ring.
Unfold antiderivative in H1; Elim H1; Intros; Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H3 a0)).
Unfold antiderivative in H0; Elim H0; Intros; Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H2 a0)).
Unfold antiderivative in H; Elim H; Intros; Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H1 a0)).
Rewrite b0; Ring.
Elim o; Intro.
Unfold antiderivative in H; Elim H; Intros; Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H1 r)).
Elim o0; Intro.
Unfold antiderivative in H0; Elim H0; Intros; Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H2 r)).
Elim o1; Intro.
Unfold antiderivative in H1; Elim H1; Intros; Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H3 r)).
Assert H2 := (antiderivative_P1 f g x0 x1 l b a H0 H1); Assert H3 := (antiderivative_Ucte ? ? ? ? ? H H2); Elim H3; Intros; Assert H5 : ``b<=a<=a``.
Split; [Left; Assumption | Right; Reflexivity].
Assert H6 : ``b<=b<=a``.
Split; [Right; Reflexivity | Left; Assumption].
Assert H7 := (H4 ? H5); Assert H8 := (H4 ? H6); Rewrite H7; Rewrite H8; Ring.
Qed.

Lemma antiderivative_P2 : (f,F0,F1:R->R;a,b,c:R) (antiderivative f F0 a b) -> (antiderivative f F1 b c) -> (antiderivative f [x:R](Cases (total_order_Rle x b) of (leftT _) => (F0 x) | (rightT _) => ``(F1 x)+((F0 b)-(F1 b))``  end) a c).
Unfold antiderivative; Intros; Elim H; Clear H; Intros; Elim H0; Clear H0; Intros; Split.
2:Apply Rle_trans with b; Assumption.
Intros; Elim H3; Clear H3; Intros; Case (total_order_T x b); Intro.
Elim s; Intro.
Assert H5 : ``a<=x<=b``.
Split; [Assumption | Left; Assumption].
Assert H6 := (H ? H5); Elim H6; Clear H6; Intros; Assert H7 : (derivable_pt_lim [x:R](Cases (total_order_Rle x b) of (leftT _) => (F0 x) | (rightT _) => ``(F1 x)+((F0 b)-(F1 b))`` end) x (f x)).
Unfold derivable_pt_lim; Assert H7 : ``(derive_pt F0 x x0)==(f x)``.
Symmetry; Assumption.
Assert H8 := (derive_pt_eq_1 F0 x (f x) x0 H7); Unfold derivable_pt_lim in H8; Intros; Elim (H8 ? H9); Intros; Pose D := (Rmin x1 ``b-x``).
Assert H11 : ``0<D``.
Unfold D; Unfold Rmin; Case (total_order_Rle x1 ``b-x``); Intro.
Apply (cond_pos x1).
Apply Rlt_Rminus; Assumption.
Exists (mkposreal ? H11); Intros; Case (total_order_Rle x b); Intro.
Case (total_order_Rle ``x+h`` b); Intro.
Apply H10.
Assumption.
Apply Rlt_le_trans with D; [Assumption | Unfold D; Apply Rmin_l].
Elim n; Left; Apply Rlt_le_trans with ``x+D``.
Apply Rlt_compatibility; Apply Rle_lt_trans with (Rabsolu h).
Apply Rle_Rabsolu.
Apply H13.
Apply Rle_anti_compatibility with ``-x``; Rewrite <- Rplus_assoc; Rewrite Rplus_Ropp_l; Rewrite Rplus_Ol; Rewrite Rplus_sym; Unfold D; Apply Rmin_r.
Elim n; Left; Assumption.
Assert H8 : (derivable_pt  [x:R]Cases (total_order_Rle x b) of (leftT _) => (F0 x) | (rightT _) => ``(F1 x)+((F0 b)-(F1 b))`` end x).
Unfold derivable_pt; Apply Specif.existT with (f x); Apply H7.
Exists H8; Symmetry; Apply derive_pt_eq_0; Apply H7.
Assert H5 : ``a<=x<=b``.
Split; [Assumption | Right; Assumption].
Assert H6 :  ``b<=x<=c``.
Split; [Right; Symmetry; Assumption | Assumption].
Elim (H ? H5); Elim (H0 ? H6); Intros; Assert H9 : (derive_pt F0 x x1)==(f x).
Symmetry; Assumption.
Assert H10 : (derive_pt F1 x x0)==(f x).
Symmetry; Assumption.
Assert H11 := (derive_pt_eq_1 F0 x (f x) x1 H9); Assert H12 := (derive_pt_eq_1 F1 x (f x) x0 H10); Assert H13 : (derivable_pt_lim [x:R]Cases (total_order_Rle x b) of (leftT _) => (F0 x) | (rightT _) => ``(F1 x)+((F0 b)-(F1 b))`` end x (f x)).
Unfold derivable_pt_lim; Unfold derivable_pt_lim in H11 H12; Intros; Elim (H11 ? H13); Elim (H12 ? H13); Intros; Pose D := (Rmin x2 x3); Assert H16 : ``0<D``.
Unfold D; Unfold Rmin; Case (total_order_Rle x2 x3); Intro.
Apply (cond_pos x2).
Apply (cond_pos x3).
Exists (mkposreal ? H16); Intros; Case (total_order_Rle x b); Intro.
Case (total_order_Rle ``x+h`` b); Intro.
Apply H15.
Assumption.
Apply Rlt_le_trans with D; [Assumption | Unfold D; Apply Rmin_r].
Replace ``(F1 (x+h))+((F0 b)-(F1 b))-(F0 x)`` with ``(F1 (x+h))-(F1 x)``.
Apply H14.
Assumption.
Apply Rlt_le_trans with D; [Assumption | Unfold D; Apply Rmin_l].
Rewrite b0; Ring.
Elim n; Right; Assumption.
Assert H14 : (derivable_pt [x:R](Cases (total_order_Rle x b) of (leftT _) => (F0 x) | (rightT _) => ``(F1 x)+((F0 b)-(F1 b))`` end) x).
Unfold derivable_pt; Apply Specif.existT with (f x); Apply H13.
Exists H14; Symmetry; Apply derive_pt_eq_0; Apply H13.
Assert H5 : ``b<=x<=c``.
Split; [Left; Assumption | Assumption].
Assert H6 := (H0 ? H5); Elim H6; Clear H6; Intros; Assert H7 : (derivable_pt_lim [x:R]Cases (total_order_Rle x b) of (leftT _) => (F0 x) | (rightT _) => ``(F1 x)+((F0 b)-(F1 b))`` end x (f x)).
Unfold derivable_pt_lim; Assert H7 : ``(derive_pt F1 x x0)==(f x)``.
Symmetry; Assumption.
Assert H8 := (derive_pt_eq_1 F1 x (f x) x0 H7); Unfold derivable_pt_lim in H8; Intros; Elim (H8 ? H9); Intros; Pose D := (Rmin x1 ``x-b``); Assert H11 : ``0<D``.
Unfold D; Unfold Rmin; Case (total_order_Rle x1 ``x-b``); Intro.
Apply (cond_pos x1).
Apply Rlt_Rminus; Assumption.
Exists (mkposreal ? H11); Intros; Case (total_order_Rle x b); Intro.
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? r0 r)).
Case (total_order_Rle ``x+h`` b); Intro.
Cut ``b<x+h``.
Intro; Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? r0 H14)).
Apply Rlt_anti_compatibility with ``-h-b``; Replace ``-h-b+b`` with ``-h``; [Idtac | Ring]; Replace ``-h-b+(x+h)`` with ``x-b``; [Idtac | Ring]; Apply Rle_lt_trans with (Rabsolu h).
Rewrite <- Rabsolu_Ropp; Apply Rle_Rabsolu.
Apply Rlt_le_trans with D.
Apply H13.
Unfold D; Apply Rmin_r.
Replace ``((F1 (x+h))+((F0 b)-(F1 b)))-((F1 x)+((F0 b)-(F1 b)))`` with ``(F1 (x+h))-(F1 x)``; [Idtac | Ring]; Apply H10.
Assumption.
Apply Rlt_le_trans with D.
Assumption.
Unfold D; Apply Rmin_l.
Assert H8 : (derivable_pt  [x:R]Cases (total_order_Rle x b) of (leftT _) => (F0 x) | (rightT _) => ``(F1 x)+((F0 b)-(F1 b))`` end x).
Unfold derivable_pt; Apply Specif.existT with (f x); Apply H7.
Exists H8; Symmetry; Apply derive_pt_eq_0; Apply H7.
Qed.

Lemma antiderivative_P3 : (f,F0,F1:R->R;a,b,c:R) (antiderivative f F0 a b) -> (antiderivative f F1 c b) -> (antiderivative f F1 c a)\/(antiderivative f F0 a c).
Intros; Unfold antiderivative in H H0; Elim H; Clear H; Elim H0; Clear H0; Intros; Case (total_order_T a c); Intro.
Elim s; Intro.
Right; Unfold antiderivative; Split.
Intros; Apply H1; Elim H3; Intros; Split; [Assumption | Apply Rle_trans with c; Assumption].
Left; Assumption.
Right; Unfold antiderivative; Split.
Intros; Apply H1; Elim H3; Intros; Split; [Assumption | Apply Rle_trans with c; Assumption].
Right; Assumption.
Left; Unfold antiderivative; Split.
Intros; Apply H; Elim H3; Intros; Split; [Assumption | Apply Rle_trans with a; Assumption].
Left; Assumption.
Qed.

Lemma antiderivative_P4 : (f,F0,F1:R->R;a,b,c:R) (antiderivative f F0 a b) -> (antiderivative f F1 a c) -> (antiderivative f F1 b c)\/(antiderivative f F0 c b).
Intros; Unfold antiderivative in H H0; Elim H; Clear H; Elim H0; Clear H0; Intros; Case (total_order_T c b); Intro.
Elim s; Intro.
Right; Unfold antiderivative; Split.
Intros; Apply H1; Elim H3; Intros; Split; [Apply Rle_trans with c; Assumption | Assumption].
Left; Assumption.
Right; Unfold antiderivative; Split.
Intros; Apply H1; Elim H3; Intros; Split; [Apply Rle_trans with c; Assumption | Assumption].
Right; Assumption.
Left; Unfold antiderivative; Split.
Intros; Apply H; Elim H3; Intros; Split; [Apply Rle_trans with b; Assumption | Assumption].
Left; Assumption.
Qed.

Lemma NewtonInt_P7 : (f:R->R;a,b,c:R) ``a<b`` -> ``b<c`` -> (Newton_integrable f a b) -> (Newton_integrable f b c) -> (Newton_integrable f a c).
Unfold Newton_integrable; Intros f a b c Hab Hbc X X0; Elim X; Clear X; Intros F0 H0; Elim X0; Clear X0; Intros F1 H1; Pose g := [x:R](Cases (total_order_Rle x b) of (leftT _) => (F0 x) | (rightT _) => ``(F1 x)+((F0 b)-(F1 b))``  end); Apply existTT with g; Left; Unfold g; Apply antiderivative_P2.
Elim H0; Intro.
Assumption.
Unfold antiderivative in H; Elim H; Clear H; Intros; Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H2 Hab)).
Elim H1; Intro.
Assumption.
Unfold antiderivative in H; Elim H; Clear H; Intros; Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H2 Hbc)).
Qed.

Lemma NewtonInt_P8 : (f:(R->R); a,b,c:R) (Newton_integrable f a b) -> (Newton_integrable f b c) -> (Newton_integrable f a c).
Intros.
Elim X; Intros F0 H0.
Elim X0; Intros F1 H1.
Case (total_order_T a b); Intro.
Elim s; Intro.
Case (total_order_T b c); Intro.
Elim s0; Intro.
(* a<b & b<c *)
Unfold Newton_integrable; Apply existTT with [x:R](Cases (total_order_Rle x b) of (leftT _) => (F0 x) | (rightT _) => ``(F1 x)+((F0 b)-(F1 b))`` end).
Elim H0; Intro.
Elim H1; Intro.
Left; Apply antiderivative_P2; Assumption.
Unfold antiderivative in H2; Elim H2; Clear H2; Intros _ H2.
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H2 a1)).
Unfold antiderivative in H; Elim H; Clear H; Intros _ H.
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H a0)).
(* a<b & b=c *)
Rewrite b0 in X; Apply X.
(* a<b & b>c *)
Case (total_order_T a c); Intro.
Elim s0; Intro.
Unfold Newton_integrable; Apply existTT with F0.
Left.
Elim H1; Intro.
Unfold antiderivative in H; Elim H; Clear H; Intros _ H.
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H r)).
Elim H0; Intro.
Assert H3 := (antiderivative_P3 f F0 F1 a b c H2 H).
Elim H3; Intro.
Unfold antiderivative in H4; Elim H4; Clear H4; Intros _ H4.
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H4 a1)).
Assumption.
Unfold antiderivative in H2; Elim H2; Clear H2; Intros _ H2.
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H2 a0)).
Rewrite b0; Apply NewtonInt_P1.
Unfold Newton_integrable; Apply existTT with F1.
Right.
Elim H1; Intro.
Unfold antiderivative in H; Elim H; Clear H; Intros _ H.
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H r)).
Elim H0; Intro.
Assert H3 := (antiderivative_P3 f F0 F1 a b c H2 H).
Elim H3; Intro.
Assumption.
Unfold antiderivative in H4; Elim H4; Clear H4; Intros _ H4.
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H4 r0)).
Unfold antiderivative in H2; Elim H2; Clear H2; Intros _ H2.
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H2 a0)).
(* a=b *)
Rewrite b0; Apply X0.
Case (total_order_T b c); Intro.
Elim s; Intro.
(* a>b & b<c *)
Case (total_order_T a c); Intro.
Elim s0; Intro.
Unfold Newton_integrable; Apply existTT with F1.
Left.
Elim H1; Intro.
(*****************)
Elim H0; Intro.
Unfold antiderivative in H2; Elim H2; Clear H2; Intros _ H2.
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H2 r)).
Assert H3 := (antiderivative_P4 f F0 F1 b a c H2 H).
Elim H3; Intro.
Assumption.
Unfold antiderivative in H4; Elim H4; Clear H4; Intros _ H4.
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H4 a1)).
Unfold antiderivative in H; Elim H; Clear H; Intros _ H.
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H a0)).
Rewrite b0; Apply NewtonInt_P1.
Unfold Newton_integrable; Apply existTT with F0.
Right.
Elim H0; Intro.
Unfold antiderivative in H; Elim H; Clear H; Intros _ H.
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H r)).
Elim H1; Intro.
Assert H3 := (antiderivative_P4 f F0 F1 b a c H H2).
Elim H3; Intro.
Unfold antiderivative in H4; Elim H4; Clear H4; Intros _ H4.
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H4 r0)).
Assumption.
Unfold antiderivative in H2; Elim H2; Clear H2; Intros _ H2.
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H2 a0)).
(* a>b & b=c *)
Rewrite b0 in X; Apply X.
(* a>b & b>c *)
Assert X1 := (NewtonInt_P3 f a b X).
Assert X2 := (NewtonInt_P3 f b c X0).
Apply NewtonInt_P3.
Apply NewtonInt_P7 with b; Assumption.
Defined.

(* Chasles' relation *)
Lemma NewtonInt_P9 : (f:R->R;a,b,c:R;pr1:(Newton_integrable f a b);pr2:(Newton_integrable f b c)) ``(NewtonInt f a c (NewtonInt_P8 f a b c pr1 pr2))==(NewtonInt f a b pr1)+(NewtonInt f b c pr2)``.
Intros; Unfold NewtonInt.
Case (NewtonInt_P8 f a b c pr1 pr2); Intros.
Case pr1; Intros.
Case pr2; Intros.
Case (total_order_T a b); Intro.
Elim s; Intro.
Case (total_order_T b c); Intro.
Elim s0; Intro.
(* a<b & b<c *)
Elim o0; Intro.
Elim o1; Intro.
Elim o; Intro.
Assert H2 := (antiderivative_P2 f x0 x1 a b c H H0).
Assert H3 := (antiderivative_Ucte f x [x:R]
          Cases (total_order_Rle x b) of
            (leftT _) => (x0 x)
          | (rightT _) => ``(x1 x)+((x0 b)-(x1 b))``
          end a c H1 H2).
Elim H3; Intros.
Assert H5 : ``a<=a<=c``.
Split; [Right; Reflexivity | Left; Apply Rlt_trans with b; Assumption].
Assert H6 : ``a<=c<=c``.
Split; [Left; Apply Rlt_trans with b; Assumption | Right; Reflexivity].
Rewrite (H4 ? H5); Rewrite (H4 ? H6).
Case (total_order_Rle a b); Intro.
Case (total_order_Rle c b); Intro.
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? r0 a1)).
Ring.
Elim n; Left; Assumption.
Unfold antiderivative in H1; Elim H1; Clear H1; Intros _ H1.
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H1 (Rlt_trans ? ? ? a0 a1))).
Unfold antiderivative in H0; Elim H0; Clear H0; Intros _ H0.
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H0 a1)).
Unfold antiderivative in H; Elim H; Clear H; Intros _ H.
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H a0)).
(* a<b & b=c *)
Rewrite <- b0.
Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rplus_Or.
Rewrite <- b0 in o.
Elim o0; Intro.
Elim o; Intro.
Assert H1 := (antiderivative_Ucte f x x0 a b H0 H).
Elim H1; Intros.
Rewrite (H2 b).
Rewrite (H2 a).
Ring.
Split; [Right; Reflexivity | Left; Assumption].
Split; [Left; Assumption | Right; Reflexivity].
Unfold antiderivative in H0; Elim H0; Clear H0; Intros _ H0.
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H0 a0)).
Unfold antiderivative in H; Elim H; Clear H; Intros _ H.
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H a0)).
(* a<b & b>c *)
Elim o1; Intro.
Unfold antiderivative in H; Elim H; Clear H; Intros _ H.
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H r)).
Elim o0; Intro.
Elim o; Intro.
Assert H2 := (antiderivative_P2 f x x1 a c b H1 H).
Assert H3 := (antiderivative_Ucte ? ? ? a b H0 H2).
Elim H3; Intros.
Rewrite (H4 a).
Rewrite (H4 b).
Case (total_order_Rle b c); Intro.
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? r0 r)).
Case (total_order_Rle a c); Intro.
Ring.
Elim n0; Unfold antiderivative in H1; Elim H1; Intros; Assumption.
Split; [Left; Assumption | Right; Reflexivity].
Split; [Right; Reflexivity | Left; Assumption].
Assert H2 := (antiderivative_P2 ? ? ? ? ? ? H1 H0).
Assert H3 := (antiderivative_Ucte ? ? ? c b H H2).
Elim H3; Intros.
Rewrite (H4 c).
Rewrite (H4 b).
Case (total_order_Rle b a); Intro.
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? r0 a0)).
Case (total_order_Rle c a); Intro.
Ring.
Elim n0; Unfold antiderivative in H1; Elim H1; Intros; Assumption.
Split; [Left; Assumption | Right; Reflexivity].
Split; [Right; Reflexivity | Left; Assumption].
Unfold antiderivative in H0; Elim H0; Clear H0; Intros _ H0.
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H0 a0)).
(* a=b *)
Rewrite b0 in o; Rewrite b0.
Elim o; Intro.
Elim o1; Intro.
Assert H1 := (antiderivative_Ucte ? ? ? b c H H0).
Elim H1; Intros.
Assert H3 : ``b<=c``.
Unfold antiderivative in H; Elim H; Intros; Assumption.
Rewrite (H2 b).
Rewrite (H2 c).
Ring.
Split; [Assumption | Right; Reflexivity].
Split; [Right; Reflexivity | Assumption].
Assert H1 : ``b==c``.
Unfold antiderivative in H H0; Elim H; Elim H0; Intros; Apply Rle_antisym; Assumption.
Rewrite H1; Ring.
Elim o1; Intro.
Assert H1 : ``b==c``.
Unfold antiderivative in H H0; Elim H; Elim H0; Intros; Apply Rle_antisym; Assumption.
Rewrite H1; Ring.
Assert H1 := (antiderivative_Ucte ? ? ? c b H H0).
Elim H1; Intros.
Assert H3 : ``c<=b``.
Unfold antiderivative in H; Elim H; Intros; Assumption.
Rewrite (H2 c).
Rewrite (H2 b).
Ring.
Split; [Assumption | Right; Reflexivity].
Split; [Right; Reflexivity | Assumption].
(* a>b & b<c *)
Case (total_order_T b c); Intro.
Elim s; Intro.
Elim o0; Intro.
Unfold antiderivative in H; Elim H; Clear H; Intros _ H.
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H r)).
Elim o1; Intro.
Elim o; Intro.
Assert H2 := (antiderivative_P2 ? ? ? ? ? ? H H1).
Assert H3 := (antiderivative_Ucte ? ? ? b c H0 H2).
Elim H3; Intros.
Rewrite (H4 b).
Rewrite (H4 c).
Case (total_order_Rle b a); Intro.
Case (total_order_Rle c a); Intro.
Assert H5 : ``a==c``.
Unfold antiderivative in  H1; Elim H1; Intros; Apply Rle_antisym; Assumption.
Rewrite H5; Ring.
Ring.
Elim n; Left; Assumption.
Split; [Left; Assumption | Right; Reflexivity].
Split; [Right; Reflexivity | Left; Assumption].
Assert H2 := (antiderivative_P2 ? ? ? ? ? ? H0 H1).
Assert H3 := (antiderivative_Ucte ? ? ? b a H H2).
Elim H3; Intros.
Rewrite (H4 a).
Rewrite (H4 b).
Case (total_order_Rle b c); Intro.
Case (total_order_Rle a c); Intro.
Assert H5 : ``a==c``.
Unfold antiderivative in  H1; Elim H1; Intros; Apply Rle_antisym; Assumption.
Rewrite H5; Ring.
Ring.
Elim n; Left; Assumption.
Split; [Right; Reflexivity | Left; Assumption].
Split; [Left; Assumption | Right; Reflexivity].
Unfold antiderivative in H0; Elim H0; Clear H0; Intros _ H0.
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H0 a0)).
(* a>b & b=c *)
Rewrite <- b0.
Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rplus_Or.
Rewrite <- b0 in o.
Elim o0; Intro.
Unfold antiderivative in H; Elim H; Clear H; Intros _ H.
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H r)).
Elim o; Intro.
Unfold antiderivative in H0; Elim H0; Clear H0; Intros _ H0.
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H0 r)).
Assert H1 := (antiderivative_Ucte f x x0 b a H0 H).
Elim H1; Intros.
Rewrite (H2 b).
Rewrite (H2 a).
Ring.
Split; [Left; Assumption | Right; Reflexivity].
Split; [Right; Reflexivity | Left; Assumption].
(* a>b & b>c *)
Elim o0; Intro.
Unfold antiderivative in H; Elim H; Clear H; Intros _ H.
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H r)).
Elim o1; Intro.
Unfold antiderivative in H0; Elim H0; Clear H0; Intros _ H0.
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H0 r0)).
Elim o; Intro.
Unfold antiderivative in H1; Elim H1; Clear H1; Intros _ H1.
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H1 (Rlt_trans ? ? ? r0 r))).
Assert H2 := (antiderivative_P2 ? ? ? ? ? ? H0 H).
Assert H3 := (antiderivative_Ucte ? ? ? c a H1 H2).
Elim H3; Intros.
Assert H5 : ``c<=a``.
Unfold antiderivative in H1; Elim H1; Intros; Assumption.
Rewrite (H4 c).
Rewrite (H4 a).
Case (total_order_Rle a b); Intro.
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? r1 r)).
Case (total_order_Rle c b); Intro.
Ring.
Elim n0; Left; Assumption.
Split; [Assumption | Right; Reflexivity].
Split; [Right; Reflexivity | Assumption].
Qed.

