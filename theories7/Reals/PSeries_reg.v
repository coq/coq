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
Require Ranalysis1.
Require Max.
Require Even.
V7only [Import R_scope.]. Open Local Scope R_scope.

Definition Boule [x:R;r:posreal] : R -> Prop := [y:R]``(Rabsolu (y-x))<r``.

(* Uniform convergence *)
Definition CVU [fn:nat->R->R;f:R->R;x:R;r:posreal] : Prop := (eps:R)``0<eps``->(EX N:nat | (n:nat;y:R) (le N n)->(Boule x r y)->``(Rabsolu ((f y)-(fn n y)))<eps``). 

(* Normal convergence *)
Definition CVN_r [fn:nat->R->R;r:posreal] : Type := (SigT ? [An:nat->R](sigTT R [l:R]((Un_cv [n:nat](sum_f_R0 [k:nat](Rabsolu (An k)) n) l)/\((n:nat)(y:R)(Boule R0 r y)->(Rle (Rabsolu (fn n y)) (An n)))))).

Definition CVN_R [fn:nat->R->R] : Type := (r:posreal) (CVN_r fn r).

Definition SFL [fn:nat->R->R;cv:(x:R)(sigTT ? [l:R](Un_cv [N:nat](SP fn N x) l))] : R-> R := [y:R](Cases (cv y) of (existTT a b) => a end).

(* In a complete space, normal convergence implies uniform convergence *)
Lemma CVN_CVU : (fn:nat->R->R;cv:(x:R)(sigTT ? [l:R](Un_cv [N:nat](SP fn N x) l));r:posreal) (CVN_r fn r) -> (CVU [n:nat](SP fn n) (SFL fn cv) ``0`` r).
Intros; Unfold CVU; Intros.
Unfold CVN_r in X.
Elim X; Intros An X0.
Elim X0; Intros s H0.
Elim H0; Intros.
Cut (Un_cv [n:nat](Rminus (sum_f_R0 [k:nat]``(Rabsolu (An k))`` n) s) R0).
Intro; Unfold Un_cv in H3.
Elim (H3 eps H); Intros N0 H4.
Exists N0; Intros.
Apply Rle_lt_trans with (Rabsolu (Rminus (sum_f_R0 [k:nat]``(Rabsolu (An k))`` n) s)).
Rewrite <- (Rabsolu_Ropp (Rminus (sum_f_R0 [k:nat]``(Rabsolu (An k))`` n) s)); Rewrite Ropp_distr3; Rewrite (Rabsolu_right (Rminus s (sum_f_R0 [k:nat]``(Rabsolu (An k))`` n))).
EApply sum_maj1.
Unfold SFL; Case (cv y); Intro.
Trivial.
Apply H1.
Intro; Elim H0; Intros.
Rewrite (Rabsolu_right (An n0)).
Apply H8; Apply H6.
Apply Rle_sym1; Apply Rle_trans with (Rabsolu (fn n0 y)).
Apply Rabsolu_pos.
Apply H8; Apply H6.
Apply Rle_sym1; Apply Rle_anti_compatibility with (sum_f_R0 [k:nat](Rabsolu (An k)) n).
Rewrite Rplus_Or; Unfold Rminus; Rewrite (Rplus_sym s); Rewrite <- Rplus_assoc; Rewrite Rplus_Ropp_r; Rewrite Rplus_Ol; Apply sum_incr.
Apply H1.
Intro; Apply Rabsolu_pos.
Unfold R_dist in H4; Unfold Rminus in H4; Rewrite Ropp_O in H4.
Assert H7 := (H4 n H5).
Rewrite Rplus_Or in H7; Apply H7.
Unfold Un_cv in H1; Unfold Un_cv; Intros.
Elim (H1? H3); Intros.
Exists x; Intros.
Unfold R_dist; Unfold R_dist in H4.
Rewrite minus_R0; Apply H4; Assumption.
Qed.

(* Each limit of a sequence of functions which converges uniformly is continue *)
Lemma CVU_continuity : (fn:nat->R->R;f:R->R;x:R;r:posreal) (CVU fn f x r) -> ((n:nat)(y:R) (Boule x r y)->(continuity_pt (fn n) y)) -> ((y:R) (Boule x r y) -> (continuity_pt f y)).
Intros; Unfold continuity_pt; Unfold continue_in; Unfold limit1_in; Unfold limit_in; Simpl; Unfold R_dist; Intros.
Unfold CVU in H.
Cut ``0<eps/3``; [Intro | Unfold Rdiv; Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Sup0]].
Elim (H ? H3); Intros N0 H4.
Assert H5 := (H0 N0 y H1).
Cut (EXT del : posreal | (h:R) ``(Rabsolu h)<del`` -> (Boule x r ``y+h``) ).
Intro.
Elim H6; Intros del1 H7.
Unfold continuity_pt in H5; Unfold continue_in in H5; Unfold limit1_in in H5; Unfold limit_in in H5; Simpl in H5; Unfold R_dist in H5.
Elim (H5 ? H3); Intros del2 H8.
Pose del := (Rmin del1 del2).
Exists del; Intros.
Split.
Unfold del; Unfold Rmin; Case (total_order_Rle del1 del2); Intro.
Apply (cond_pos del1).
Elim H8; Intros; Assumption.
Intros; Apply Rle_lt_trans with ``(Rabsolu ((f x0)-(fn N0 x0)))+(Rabsolu ((fn N0 x0)-(f y)))``.
Replace ``(f x0)-(f y)`` with ``((f x0)-(fn N0 x0))+((fn N0 x0)-(f y))``; [Apply Rabsolu_triang | Ring].
Apply Rle_lt_trans with ``(Rabsolu ((f x0)-(fn N0 x0)))+(Rabsolu ((fn N0 x0)-(fn N0 y)))+(Rabsolu ((fn N0 y)-(f y)))``.
Rewrite Rplus_assoc; Apply Rle_compatibility.
Replace ``(fn N0 x0)-(f y)`` with ``((fn N0 x0)-(fn N0 y))+((fn N0 y)-(f y))``; [Apply Rabsolu_triang | Ring].
Replace ``eps`` with ``eps/3+eps/3+eps/3``.
Repeat Apply Rplus_lt.
Apply H4.
Apply le_n.
Replace x0 with ``y+(x0-y)``; [Idtac | Ring]; Apply H7.
Elim H9; Intros.
Apply Rlt_le_trans with del.
Assumption.
Unfold del; Apply Rmin_l.
Elim H8; Intros.
Apply H11.
Split.
Elim H9; Intros; Assumption.
Elim H9; Intros; Apply Rlt_le_trans with del.
Assumption.
Unfold del; Apply Rmin_r.
Rewrite <- Rabsolu_Ropp; Rewrite Ropp_distr3; Apply H4.
Apply le_n.
Assumption.
Apply r_Rmult_mult with ``3``.
Do 2 Rewrite Rmult_Rplus_distr; Unfold Rdiv; Rewrite <- Rmult_assoc; Rewrite Rinv_r_simpl_m.
Ring.
DiscrR.
DiscrR.
Cut ``0<r-(Rabsolu (x-y))``.
Intro; Exists (mkposreal ? H6).
Simpl; Intros.
Unfold Boule; Replace ``y+h-x`` with ``h+(y-x)``; [Idtac | Ring]; Apply Rle_lt_trans with ``(Rabsolu h)+(Rabsolu (y-x))``.
Apply Rabsolu_triang.
Apply Rlt_anti_compatibility with ``-(Rabsolu (x-y))``.
Rewrite <- (Rabsolu_Ropp ``y-x``); Rewrite Ropp_distr3.
Replace ``-(Rabsolu (x-y))+r`` with ``r-(Rabsolu (x-y))``.
Replace ``-(Rabsolu (x-y))+((Rabsolu h)+(Rabsolu (x-y)))`` with (Rabsolu h).
Apply H7.
Ring.
Ring.
Unfold Boule in H1; Rewrite <- (Rabsolu_Ropp ``x-y``); Rewrite Ropp_distr3; Apply Rlt_anti_compatibility with ``(Rabsolu (y-x))``.
Rewrite Rplus_Or; Replace ``(Rabsolu (y-x))+(r-(Rabsolu (y-x)))`` with ``(pos r)``; [Apply H1 | Ring].
Qed.

(**********)
Lemma continuity_pt_finite_SF : (fn:nat->R->R;N:nat;x:R) ((n:nat)(le n N)->(continuity_pt (fn n) x)) -> (continuity_pt [y:R](sum_f_R0 [k:nat]``(fn k y)`` N) x).
Intros; Induction N.
Simpl; Apply (H O); Apply le_n.
Simpl; Replace [y:R](Rplus (sum_f_R0 [k:nat](fn k y) N) (fn (S N) y)) with (plus_fct [y:R](sum_f_R0 [k:nat](fn k y) N) [y:R](fn (S N) y)); [Idtac | Reflexivity].
Apply continuity_pt_plus.
Apply HrecN.
Intros; Apply H.
Apply le_trans with N; [Assumption | Apply le_n_Sn].
Apply (H (S N)); Apply le_n.
Qed.

(* Continuity and normal convergence *)
Lemma SFL_continuity_pt : (fn:nat->R->R;cv:(x:R)(sigTT ? [l:R](Un_cv [N:nat](SP fn N x) l));r:posreal) (CVN_r fn r) -> ((n:nat)(y:R) (Boule ``0`` r y) -> (continuity_pt (fn n) y)) -> ((y:R) (Boule ``0`` r y) -> (continuity_pt (SFL fn cv) y)).
Intros; EApply CVU_continuity.
Apply CVN_CVU.
Apply X.
Intros; Unfold SP; Apply continuity_pt_finite_SF.
Intros; Apply H.
Apply H1.
Apply H0.
Qed.

Lemma SFL_continuity : (fn:nat->R->R;cv:(x:R)(sigTT ? [l:R](Un_cv [N:nat](SP fn N x) l))) (CVN_R fn) -> ((n:nat)(continuity (fn n))) -> (continuity (SFL fn cv)).
Intros; Unfold continuity; Intro.
Cut ``0<(Rabsolu x)+1``; [Intro | Apply ge0_plus_gt0_is_gt0; [Apply Rabsolu_pos | Apply Rlt_R0_R1]].
Cut (Boule ``0`` (mkposreal ? H0) x).
Intro; EApply SFL_continuity_pt with (mkposreal ? H0).
Apply X.
Intros; Apply (H n y).
Apply H1.
Unfold Boule; Simpl; Rewrite minus_R0; Pattern 1 (Rabsolu x); Rewrite <- Rplus_Or; Apply Rlt_compatibility; Apply Rlt_R0_R1.
Qed.

(* As R is complete, normal convergence implies that (fn) is simply-uniformly convergent *) 
Lemma CVN_R_CVS : (fn:nat->R->R) (CVN_R fn) -> ((x:R)(sigTT ? [l:R](Un_cv [N:nat](SP fn N x) l))).
Intros; Apply R_complete.
Unfold SP; Pose An := [N:nat](fn N x).
Change (Cauchy_crit_series An).
Apply cauchy_abs.
Unfold Cauchy_crit_series; Apply CV_Cauchy.
Unfold CVN_R in X; Cut ``0<(Rabsolu x)+1``.
Intro; Assert H0 := (X (mkposreal ? H)).
Unfold CVN_r in H0; Elim H0; Intros Bn H1.
Elim H1; Intros l H2.
Elim H2; Intros.
Apply Rseries_CV_comp with Bn.
Intro; Split.
Apply Rabsolu_pos.
Unfold An; Apply H4; Unfold Boule; Simpl; Rewrite minus_R0.
Pattern 1 (Rabsolu x); Rewrite <- Rplus_Or; Apply Rlt_compatibility; Apply Rlt_R0_R1.
Apply existTT with l.
Cut (n:nat)``0<=(Bn n)``.
Intro; Unfold Un_cv in H3; Unfold Un_cv; Intros.
Elim (H3 ? H6); Intros.
Exists x0; Intros.
Replace (sum_f_R0 Bn n) with (sum_f_R0 [k:nat](Rabsolu (Bn k)) n).
Apply H7; Assumption.
Apply sum_eq; Intros; Apply Rabsolu_right; Apply Rle_sym1; Apply H5.
Intro; Apply Rle_trans with (Rabsolu (An n)).
Apply Rabsolu_pos.
Unfold An; Apply H4; Unfold Boule; Simpl; Rewrite minus_R0; Pattern 1 (Rabsolu x); Rewrite <- Rplus_Or; Apply Rlt_compatibility; Apply Rlt_R0_R1.
Apply ge0_plus_gt0_is_gt0; [Apply Rabsolu_pos | Apply Rlt_R0_R1].
Qed.
