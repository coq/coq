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
Require R_sqrt.
V7only [Import R_scope.]. Open Local Scope R_scope.

Definition dist_euc [x0,y0,x1,y1:R] : R := ``(sqrt ((Rsqr (x0-x1))+(Rsqr (y0-y1))))``.

Lemma distance_refl : (x0,y0:R) ``(dist_euc x0 y0 x0 y0)==0``.
Intros x0 y0; Unfold dist_euc; Apply Rsqr_inj; [Apply sqrt_positivity; Apply ge0_plus_ge0_is_ge0; [Apply pos_Rsqr | Apply pos_Rsqr] | Right; Reflexivity | Rewrite Rsqr_O; Rewrite Rsqr_sqrt; [Unfold Rsqr; Ring | Apply ge0_plus_ge0_is_ge0; [Apply pos_Rsqr | Apply pos_Rsqr]]].
Qed.

Lemma distance_symm : (x0,y0,x1,y1:R) ``(dist_euc x0 y0 x1 y1) == (dist_euc x1 y1 x0 y0)``. 
Intros x0 y0 x1 y1; Unfold dist_euc; Apply Rsqr_inj; [ Apply sqrt_positivity; Apply ge0_plus_ge0_is_ge0 | Apply sqrt_positivity; Apply ge0_plus_ge0_is_ge0 | Repeat Rewrite Rsqr_sqrt; [Unfold Rsqr; Ring | Apply ge0_plus_ge0_is_ge0 |Apply ge0_plus_ge0_is_ge0]]; Apply pos_Rsqr.
Qed.

Lemma law_cosines : (x0,y0,x1,y1,x2,y2,ac:R) let a = (dist_euc x1 y1 x0 y0) in let b=(dist_euc x2 y2 x0 y0) in let c=(dist_euc x2 y2 x1 y1) in ( ``a*c*(cos ac) == ((x0-x1)*(x2-x1) + (y0-y1)*(y2-y1))`` -> ``(Rsqr b)==(Rsqr c)+(Rsqr a)-2*(a*c*(cos ac))`` ).
Unfold dist_euc; Intros; Repeat Rewrite -> Rsqr_sqrt; [ Rewrite H; Unfold Rsqr; Ring | Apply ge0_plus_ge0_is_ge0 | Apply ge0_plus_ge0_is_ge0 | Apply ge0_plus_ge0_is_ge0]; Apply pos_Rsqr.
Qed.

Lemma triangle : (x0,y0,x1,y1,x2,y2:R) ``(dist_euc x0 y0 x1 y1)<=(dist_euc x0 y0 x2 y2)+(dist_euc x2 y2 x1 y1)``.
Intros; Unfold dist_euc; Apply Rsqr_incr_0; [Rewrite Rsqr_plus; Repeat Rewrite Rsqr_sqrt; [Replace ``(Rsqr (x0-x1))`` with ``(Rsqr (x0-x2))+(Rsqr (x2-x1))+2*(x0-x2)*(x2-x1)``; [Replace ``(Rsqr (y0-y1))`` with ``(Rsqr (y0-y2))+(Rsqr (y2-y1))+2*(y0-y2)*(y2-y1)``; [Apply Rle_anti_compatibility with ``-(Rsqr (x0-x2))-(Rsqr (x2-x1))-(Rsqr (y0-y2))-(Rsqr (y2-y1))``; Replace `` -(Rsqr (x0-x2))-(Rsqr (x2-x1))-(Rsqr (y0-y2))-(Rsqr (y2-y1))+((Rsqr (x0-x2))+(Rsqr (x2-x1))+2*(x0-x2)*(x2-x1)+((Rsqr (y0-y2))+(Rsqr (y2-y1))+2*(y0-y2)*(y2-y1)))`` with ``2*((x0-x2)*(x2-x1)+(y0-y2)*(y2-y1))``; [Replace ``-(Rsqr (x0-x2))-(Rsqr (x2-x1))-(Rsqr (y0-y2))-(Rsqr (y2-y1))+((Rsqr (x0-x2))+(Rsqr (y0-y2))+((Rsqr (x2-x1))+(Rsqr (y2-y1)))+2*(sqrt ((Rsqr (x0-x2))+(Rsqr (y0-y2))))*(sqrt ((Rsqr (x2-x1))+(Rsqr (y2-y1)))))`` with ``2*((sqrt ((Rsqr (x0-x2))+(Rsqr (y0-y2))))*(sqrt ((Rsqr (x2-x1))+(Rsqr (y2-y1)))))``; [Apply Rle_monotony; [Left; Cut ~(O=(2)); [Intros; Generalize (lt_INR_0 (2) (neq_O_lt (2) H)); Intro H0; Assumption | Discriminate] | Apply sqrt_cauchy] | Ring] | Ring] | SqRing] | SqRing] | Apply ge0_plus_ge0_is_ge0; Apply pos_Rsqr | Apply ge0_plus_ge0_is_ge0; Apply pos_Rsqr | Apply ge0_plus_ge0_is_ge0; Apply pos_Rsqr] | Apply sqrt_positivity; Apply ge0_plus_ge0_is_ge0; Apply pos_Rsqr | Apply ge0_plus_ge0_is_ge0; Apply sqrt_positivity; Apply ge0_plus_ge0_is_ge0; Apply pos_Rsqr].
Qed.

(******************************************************************)
(**                         Translation                           *)
(******************************************************************)

Definition xt[x,tx:R] : R := ``x+tx``.
Definition yt[y,ty:R] : R := ``y+ty``.

Lemma translation_0 : (x,y:R) ``(xt x 0)==x``/\``(yt y 0)==y``.
Intros x y; Split; [Unfold xt | Unfold yt]; Ring.
Qed.

Lemma isometric_translation : (x1,x2,y1,y2,tx,ty:R) ``(Rsqr (x1-x2))+(Rsqr (y1-y2))==(Rsqr ((xt x1 tx)-(xt x2 tx)))+(Rsqr ((yt y1 ty)-(yt y2 ty)))``.
Intros; Unfold Rsqr xt yt; Ring.
Qed.

(******************************************************************)
(**                           Rotation                            *)
(******************************************************************)

Definition xr [x,y,theta:R] : R := ``x*(cos theta)+y*(sin theta)``.
Definition yr [x,y,theta:R] : R := ``-x*(sin theta)+y*(cos theta)``.

Lemma rotation_0 : (x,y:R) ``(xr x y 0)==x`` /\ ``(yr x y 0)==y``.
Intros x y; Unfold xr yr; Split; Rewrite cos_0; Rewrite sin_0; Ring.
Qed.

Lemma rotation_PI2 : (x,y:R) ``(xr x y PI/2)==y`` /\ ``(yr x y PI/2)==-x``.
Intros  x y; Unfold xr yr; Split; Rewrite cos_PI2; Rewrite sin_PI2; Ring.
Qed.

Lemma isometric_rotation_0 : (x1,y1,x2,y2,theta:R) ``(Rsqr (x1-x2))+(Rsqr (y1-y2)) == (Rsqr ((xr x1 y1 theta))-(xr x2 y2 theta)) + (Rsqr ((yr x1 y1 theta))-(yr x2 y2 theta))``.
Intros; Unfold xr yr; Replace ``x1*(cos theta)+y1*(sin theta)-(x2*(cos theta)+y2*(sin theta))`` with ``(cos theta)*(x1-x2)+(sin theta)*(y1-y2)``; [Replace ``-x1*(sin theta)+y1*(cos theta)-( -x2*(sin theta)+y2*(cos theta))`` with ``(cos theta)*(y1-y2)+(sin theta)*(x2-x1)``; [Repeat Rewrite Rsqr_plus; Repeat Rewrite Rsqr_times; Repeat Rewrite cos2; Ring; Replace ``x2-x1`` with ``-(x1-x2)``; [Rewrite <- Rsqr_neg; Ring | Ring] |Ring] | Ring].
Qed.

Lemma isometric_rotation : (x1,y1,x2,y2,theta:R) ``(dist_euc x1 y1 x2 y2) == (dist_euc (xr x1 y1 theta) (yr x1 y1 theta) (xr x2 y2 theta) (yr x2 y2 theta))``.
Unfold dist_euc; Intros; Apply Rsqr_inj; [Apply sqrt_positivity; Apply ge0_plus_ge0_is_ge0 | Apply sqrt_positivity; Apply ge0_plus_ge0_is_ge0 | Repeat Rewrite Rsqr_sqrt; [ Apply isometric_rotation_0 | Apply ge0_plus_ge0_is_ge0 | Apply ge0_plus_ge0_is_ge0]]; Apply pos_Rsqr.
Qed.

(******************************************************************)
(**                         Similarity                            *)
(******************************************************************)

Lemma isometric_rot_trans : (x1,y1,x2,y2,tx,ty,theta:R) ``(Rsqr (x1-x2))+(Rsqr (y1-y2)) == (Rsqr ((xr (xt x1 tx) (yt y1 ty) theta)-(xr (xt x2 tx) (yt y2 ty) theta))) + (Rsqr ((yr (xt x1 tx) (yt y1 ty) theta)-(yr (xt x2 tx) (yt y2 ty) theta)))``. 
Intros; Rewrite <- isometric_rotation_0; Apply isometric_translation.
Qed.

Lemma isometric_trans_rot : (x1,y1,x2,y2,tx,ty,theta:R) ``(Rsqr (x1-x2))+(Rsqr (y1-y2)) == (Rsqr ((xt (xr x1 y1 theta) tx)-(xt (xr x2 y2 theta) tx))) + (Rsqr ((yt (yr x1 y1 theta) ty)-(yt (yr x2 y2 theta) ty)))``. 
Intros; Rewrite <- isometric_translation; Apply isometric_rotation_0.
Qed.
