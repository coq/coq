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
Require Rfunctions.
Require Rseries.
Require Rsigma.
Require Alembert.
Require Alembert_compl.
Require Binome.
Require Cv_prop.
Require Rcomplet.
Require Rtrigo_alt.
Require Cos_plus.
Require Ranalysis1.
Require Max.
Require Even.

Definition Boule [x:R;r:posreal] : R -> Prop := [y:R]``(Rabsolu (y-x))<r``.

Definition CVU [fn:nat->R->R;f:R->R;x:R;r:posreal] : Prop := (eps:R)``0<eps``->(EX N:nat | (n:nat;y:R) (le N n)->(Boule x r y)->``(Rabsolu ((f y)-(fn n y)))<eps``). 

Definition CVN_r [fn:nat->R->R;r:posreal] : Type := (SigT ? [An:nat->R](sigTT R [l:R]((Un_cv [n:nat](sum_f_R0 [k:nat](Rabsolu (An k)) n) l)/\((n:nat)(y:R)(Boule R0 r y)->(Rle (Rabsolu (fn n y)) (An n)))))).

Definition CVN_R [fn:nat->R->R] : Type := (r:posreal) (CVN_r fn r).

Definition SP [fn:nat->R->R;N:nat] : R->R := [x:R](sum_f_R0 [k:nat]``(fn k x)`` N).

Definition SFL [fn:nat->R->R;cv:(x:R)(sigTT ? [l:R](Un_cv [N:nat](SP fn N x) l))] : R-> R := [y:R](Cases (cv y) of (existTT a b) => a end).

(**********)
Lemma sum_incr : (An:nat->R;N:nat;l:R) (Un_cv [n:nat](sum_f_R0 An n) l) -> ((n:nat)``0<=(An n)``) -> ``(sum_f_R0 An N)<=l``.
Intros; Case (total_order_T (sum_f_R0 An N) l); Intro.
Elim s; Intro.
Left; Apply a.
Right; Apply b.
Cut (Un_growing [n:nat](sum_f_R0 An n)).
Intro; Pose l1 := (sum_f_R0 An N).
Fold l1 in r.
Unfold Un_cv in H; Cut ``0<l1-l``.
Intro; Elim (H ? H2); Intros.
Pose N0 := (max x N); Cut (ge N0 x).
Intro; Assert H5 := (H3 N0 H4).
Cut ``l1<=(sum_f_R0 An N0)``.
Intro; Unfold R_dist in H5; Rewrite Rabsolu_right in H5.
Cut ``(sum_f_R0 An N0)<l1``.
Intro; Elim (Rlt_antirefl ? (Rlt_le_trans ? ? ? H7 H6)).
Apply Rlt_anti_compatibility with ``-l``.
Do 2 Rewrite (Rplus_sym ``-l``).
Apply H5.
Apply Rle_sym1; Apply Rle_anti_compatibility with l.
Rewrite Rplus_Or; Replace ``l+((sum_f_R0 An N0)-l)`` with (sum_f_R0 An N0); [Idtac | Ring]; Apply Rle_trans with l1.
Left; Apply r.
Apply H6.
Unfold l1; Apply Rle_sym2; Apply (growing_prop [k:nat](sum_f_R0 An k)).
Apply H1.
Unfold ge N0; Apply le_max_r.
Unfold ge N0; Apply le_max_l.
Apply Rlt_anti_compatibility with l; Rewrite Rplus_Or; Replace ``l+(l1-l)`` with l1; [Apply r | Ring].
Unfold Un_growing; Intro; Simpl; Pattern 1 (sum_f_R0 An n); Rewrite <- Rplus_Or; Apply Rle_compatibility; Apply H0.
Qed.

(**********)
Lemma sum_cv_maj : (An:nat->R;fn:nat->R->R;x,l1,l2:R) (Un_cv [n:nat](SP fn n x) l1) -> (Un_cv [n:nat](sum_f_R0 An n) l2) -> ((n:nat)``(Rabsolu (fn n x))<=(An n)``) -> ``(Rabsolu l1)<=l2``.
Intros; Case (total_order_T (Rabsolu l1) l2); Intro.
Elim s; Intro.
Left; Apply a.
Right; Apply b.
Cut (n0:nat)``(Rabsolu (SP fn n0 x))<=(sum_f_R0 An n0)``.
Intro; Cut ``0<((Rabsolu l1)-l2)/2``.
Intro; Unfold Un_cv in H H0.
Elim (H ? H3); Intros Na H4.
Elim (H0 ? H3); Intros Nb H5.
Pose N := (max Na Nb).
Unfold R_dist in H4 H5.
Cut ``(Rabsolu ((sum_f_R0 An N)-l2))<((Rabsolu l1)-l2)/2``.
Intro; Cut ``(Rabsolu ((Rabsolu l1)-(Rabsolu (SP fn N x))))<((Rabsolu l1)-l2)/2``.
Intro; Cut ``(sum_f_R0 An N)<((Rabsolu l1)+l2)/2``.
Intro; Cut ``((Rabsolu l1)+l2)/2<(Rabsolu (SP fn N x))``.
Intro; Cut ``(sum_f_R0 An N)<(Rabsolu (SP fn N x))``.
Intro; Assert H11 := (H2 N).
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H11 H10)).
Apply Rlt_trans with ``((Rabsolu l1)+l2)/2``; Assumption.
Case (case_Rabsolu ``(Rabsolu l1)-(Rabsolu (SP fn N x))``); Intro.
Apply Rlt_trans with (Rabsolu l1).
Apply Rlt_monotony_contra with ``2``.
Apply Rgt_2_0.
Unfold Rdiv; Rewrite (Rmult_sym ``2``); Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r; Rewrite double; Apply Rlt_compatibility; Apply r.
DiscrR.
Apply (Rminus_lt ? ? r0).
Rewrite (Rabsolu_right ? r0) in H7.
Apply Rlt_anti_compatibility with ``((Rabsolu l1)-l2)/2-(Rabsolu (SP fn N x))``.
Replace ``((Rabsolu l1)-l2)/2-(Rabsolu (SP fn N x))+((Rabsolu l1)+l2)/2`` with ``(Rabsolu l1)-(Rabsolu (SP fn N x))``.
Unfold Rminus; Rewrite Rplus_assoc; Rewrite Rplus_Ropp_l; Rewrite Rplus_Or; Apply H7.
Unfold Rdiv; Rewrite Rmult_Rplus_distrl; Rewrite <- (Rmult_sym ``/2``); Rewrite Rminus_distr; Repeat Rewrite (Rmult_sym ``/2``); Pattern 1 (Rabsolu l1); Rewrite double_var; Unfold Rdiv; Ring.
Case (case_Rabsolu ``(sum_f_R0 An N)-l2``); Intro.
Apply Rlt_trans with l2.
Apply (Rminus_lt ? ? r0).
Apply Rlt_monotony_contra with ``2``.
Apply Rgt_2_0.
Rewrite (double l2); Unfold Rdiv; Rewrite (Rmult_sym ``2``); Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r; Rewrite (Rplus_sym (Rabsolu l1)); Apply Rlt_compatibility; Apply r.
DiscrR.
Rewrite (Rabsolu_right ? r0) in H6; Apply Rlt_anti_compatibility with ``-l2``.
Replace ``-l2+((Rabsolu l1)+l2)/2`` with ``((Rabsolu l1)-l2)/2``.
Rewrite Rplus_sym; Apply H6.
Unfold Rdiv; Rewrite <- (Rmult_sym ``/2``); Rewrite Rminus_distr; Rewrite Rmult_Rplus_distrl; Pattern 2 l2; Rewrite double_var; Repeat Rewrite (Rmult_sym ``/2``); Rewrite Ropp_distr1; Unfold Rdiv; Ring.
Apply Rle_lt_trans with ``(Rabsolu ((SP fn N x)-l1))``.
Rewrite <- Rabsolu_Ropp; Rewrite Ropp_distr3; Apply Rabsolu_triang_inv2.
Apply H4; Unfold ge N; Apply le_max_l.
Apply H5; Unfold ge N; Apply le_max_r.
Unfold Rdiv; Apply Rmult_lt_pos.
Apply Rlt_anti_compatibility with l2.
Rewrite Rplus_Or; Replace ``l2+((Rabsolu l1)-l2)`` with (Rabsolu l1); [Apply r | Ring].
Apply Rlt_Rinv; Apply Rgt_2_0.
Intros; Induction n0.
Unfold SP; Simpl; Apply H1.
Unfold SP; Simpl.
Apply Rle_trans with (Rplus (Rabsolu (sum_f_R0 [k:nat](fn k x) n0)) (Rabsolu (fn (S n0) x))).
Apply Rabsolu_triang.
Apply Rle_trans with ``(sum_f_R0 An n0)+(Rabsolu (fn (S n0) x))``.
Do 2 Rewrite <- (Rplus_sym (Rabsolu (fn (S n0) x))).
Apply Rle_compatibility; Apply Hrecn0.
Apply Rle_compatibility; Apply H1.
Qed.

(**********)
Lemma sum_maj1 : (fn:nat->R->R;An:nat->R;x,l1,l2:R;N:nat) (Un_cv [n:nat](SP fn n x) l1) -> (Un_cv [n:nat](sum_f_R0 An n) l2) -> ((n:nat)``(Rabsolu (fn n x))<=(An n)``) -> ``(Rabsolu (l1-(SP fn N x)))<=l2-(sum_f_R0 An N)``.
Intros; Cut (sigTT R [l:R](Un_cv [n:nat](sum_f_R0 [l:nat](fn (plus (S N) l) x) n) l)).
Intro; Cut (sigTT R [l:R](Un_cv [n:nat](sum_f_R0 [l:nat](An (plus (S N) l)) n) l)).
Intro; Elim X; Intros l1N H2.
Elim X0; Intros l2N H3.
Cut ``l1-(SP fn N x)==l1N``.
Intro; Cut ``l2-(sum_f_R0 An N)==l2N``.
Intro; Rewrite H4; Rewrite H5.
Apply sum_cv_maj with [l:nat](An (plus (S N) l)) [l:nat][x:R](fn (plus (S N) l) x) x.
Unfold SP; Apply H2.
Apply H3.
Intros; Apply H1.
Symmetry; EApply UL_suite.
Apply H3.
Unfold Un_cv in H0; Unfold Un_cv; Intros; Elim (H0 eps H5); Intros N0 H6.
Unfold R_dist in H6; Exists N0; Intros.
Unfold R_dist; Replace (Rminus (sum_f_R0 [l:nat](An (plus (S N) l)) n) (Rminus l2 (sum_f_R0 An N))) with (Rminus (Rplus (sum_f_R0 An N) (sum_f_R0 [l:nat](An (plus (S N) l)) n)) l2); [Idtac | Ring].
Replace (Rplus (sum_f_R0 An N) (sum_f_R0 [l:nat](An (plus (S N) l)) n)) with (sum_f_R0 An (S (plus N n))).
Apply H6; Unfold ge; Apply le_trans with n.
Apply H7.
Apply le_trans with (plus N n).
Apply le_plus_r.
Apply le_n_Sn.
Cut (le O N).
Cut (lt N (S (plus N n))).
Intros; Assert H10 := (sigma_split An H9 H8).
Unfold sigma in H10.
Do 2 Rewrite <- minus_n_O in H10.
Replace (sum_f_R0 An (S (plus N n))) with (sum_f_R0 [k:nat](An (plus (0) k)) (S (plus N n))).
Replace (sum_f_R0 An N) with (sum_f_R0 [k:nat](An (plus (0) k)) N).
Cut (minus (S (plus N n)) (S N))=n.
Intro; Rewrite H11 in H10.
Apply H10.
Apply INR_eq; Rewrite minus_INR.
Do 2 Rewrite S_INR; Rewrite plus_INR; Ring.
Apply le_n_S; Apply le_plus_l.
Apply sum_eq; Intros.
Reflexivity.
Apply sum_eq; Intros.
Reflexivity.
Apply le_lt_n_Sm; Apply le_plus_l.
Apply le_O_n.
Symmetry; EApply UL_suite.
Apply H2.
Unfold Un_cv in H; Unfold Un_cv; Intros.
Elim (H eps H4); Intros N0 H5.
Unfold R_dist in H5; Exists N0; Intros.
Unfold R_dist SP; Replace (Rminus (sum_f_R0 [l:nat](fn (plus (S N) l) x) n) (Rminus l1 (sum_f_R0 [k:nat](fn k x) N))) with (Rminus (Rplus (sum_f_R0 [k:nat](fn k x) N) (sum_f_R0 [l:nat](fn (plus (S N) l) x) n)) l1); [Idtac | Ring].
Replace (Rplus (sum_f_R0 [k:nat](fn k x) N) (sum_f_R0 [l:nat](fn (plus (S N) l) x) n)) with (sum_f_R0 [k:nat](fn k x) (S (plus N n))).
Unfold SP in H5; Apply H5; Unfold ge; Apply le_trans with n.
Apply H6.
Apply le_trans with (plus N n).
Apply le_plus_r.
Apply le_n_Sn.
Cut (le O N).
Cut (lt N (S (plus N n))).
Intros; Assert H9 := (sigma_split [k:nat](fn k x) H8 H7).
Unfold sigma in H9.
Do 2 Rewrite <- minus_n_O in H9.
Replace (sum_f_R0 [k:nat](fn k x) (S (plus N n))) with (sum_f_R0 [k:nat](fn (plus (0) k) x) (S (plus N n))).
Replace (sum_f_R0 [k:nat](fn k x) N) with (sum_f_R0 [k:nat](fn (plus (0) k) x) N).
Cut (minus (S (plus N n)) (S N))=n.
Intro; Rewrite H10 in H9.
Apply H9.
Apply INR_eq; Rewrite minus_INR.
Do 2 Rewrite S_INR; Rewrite plus_INR; Ring.
Apply le_n_S; Apply le_plus_l.
Apply sum_eq; Intros.
Reflexivity.
Apply sum_eq; Intros.
Reflexivity.
Apply le_lt_n_Sm.
Apply le_plus_l.
Apply le_O_n.
Apply existTT with ``l2-(sum_f_R0 An N)``.
Unfold Un_cv in H0; Unfold Un_cv; Intros.
Elim (H0 eps H2); Intros N0 H3.
Unfold R_dist in H3; Exists N0; Intros.
Unfold R_dist; Replace (Rminus (sum_f_R0 [l:nat](An (plus (S N) l)) n) (Rminus l2 (sum_f_R0 An N))) with (Rminus (Rplus (sum_f_R0 An N) (sum_f_R0 [l:nat](An (plus (S N) l)) n)) l2); [Idtac | Ring].
Replace (Rplus (sum_f_R0 An N) (sum_f_R0 [l:nat](An (plus (S N) l)) n)) with (sum_f_R0 An (S (plus N n))).
Apply H3; Unfold ge; Apply le_trans with n.
Apply H4.
Apply le_trans with (plus N n).
Apply le_plus_r.
Apply le_n_Sn.
Cut (le O N).
Cut (lt N (S (plus N n))).
Intros; Assert H7 := (sigma_split An H6 H5).
Unfold sigma in H7.
Do 2 Rewrite <- minus_n_O in H7.
Replace (sum_f_R0 An (S (plus N n))) with (sum_f_R0 [k:nat](An (plus (0) k)) (S (plus N n))).
Replace (sum_f_R0 An N) with (sum_f_R0 [k:nat](An (plus (0) k)) N).
Cut (minus (S (plus N n)) (S N))=n.
Intro; Rewrite H8 in H7.
Apply H7.
Apply INR_eq; Rewrite minus_INR.
Do 2 Rewrite S_INR; Rewrite plus_INR; Ring.
Apply le_n_S; Apply le_plus_l.
Apply sum_eq; Intros.
Reflexivity.
Apply sum_eq; Intros.
Reflexivity.
Apply le_lt_n_Sm.
Apply le_plus_l.
Apply le_O_n.
Apply existTT with ``l1-(SP fn N x)``.
Unfold Un_cv in H; Unfold Un_cv; Intros.
Elim (H eps H2); Intros N0 H3.
Unfold R_dist in H3; Exists N0; Intros.
Unfold R_dist SP.
Replace (Rminus (sum_f_R0 [l:nat](fn (plus (S N) l) x) n) (Rminus l1 (sum_f_R0 [k:nat](fn k x) N))) with (Rminus (Rplus (sum_f_R0 [k:nat](fn k x) N) (sum_f_R0 [l:nat](fn (plus (S N) l) x) n)) l1); [Idtac | Ring].
Replace (Rplus (sum_f_R0 [k:nat](fn k x) N) (sum_f_R0 [l:nat](fn (plus (S N) l) x) n)) with (sum_f_R0 [k:nat](fn k x) (S (plus N n))).
Unfold SP in H3; Apply H3.
Unfold ge; Apply le_trans with n.
Apply H4.
Apply le_trans with (plus N n).
Apply le_plus_r.
Apply le_n_Sn.
Cut (le O N).
Cut (lt N (S (plus N n))).
Intros; Assert H7 := (sigma_split [k:nat](fn k x) H6 H5).
Unfold sigma in H7.
Do 2 Rewrite <- minus_n_O in H7.
Replace (sum_f_R0 [k:nat](fn k x) (S (plus N n))) with (sum_f_R0 [k:nat](fn (plus (0) k) x) (S (plus N n))).
Replace (sum_f_R0 [k:nat](fn k x) N) with (sum_f_R0 [k:nat](fn (plus (0) k) x) N).
Cut (minus (S (plus N n)) (S N))=n.
Intro; Rewrite H8 in H7.
Apply H7.
Apply INR_eq; Rewrite minus_INR.
Do 2 Rewrite S_INR; Rewrite plus_INR; Ring.
Apply le_n_S; Apply le_plus_l.
Apply sum_eq; Intros.
Reflexivity.
Apply sum_eq; Intros.
Reflexivity.
Apply le_lt_n_Sm.
Apply le_plus_l.
Apply le_O_n.
Qed.

Lemma pow1 : (n:nat) (pow R1 n)==R1.
Intro; Induction n.
Reflexivity.
Simpl; Rewrite Hrecn; Rewrite Rmult_1r; Reflexivity.
Qed.

Lemma pow_Rabs : (x:R;n:nat) ``(pow x n)<=(pow (Rabsolu x) n)``.
Intros; Induction n.
Right; Reflexivity.
Simpl; Case (case_Rabsolu x); Intro.
Apply Rle_trans with (Rabsolu ``x*(pow x n)``).
Apply Rle_Rabsolu.
Rewrite Rabsolu_mult.
Apply Rle_monotony.
Apply Rabsolu_pos.
Right; Symmetry; Apply Pow_Rabsolu.
Pattern 1 (Rabsolu x); Rewrite (Rabsolu_right x r); Apply Rle_monotony.
Apply Rle_sym2; Exact r.
Apply Hrecn.
Qed.

Lemma pow_maj_Rabs : (x,y:R;n:nat) ``(Rabsolu y)<=x`` -> ``(pow y n)<=(pow x n)``.
Intros; Cut ``0<=x``.
Intro; Apply Rle_trans with (pow (Rabsolu y) n).
Apply pow_Rabs.
Induction n.
Right; Reflexivity.
Simpl; Apply Rle_trans with ``x*(pow (Rabsolu y) n)``.
Do 2 Rewrite <- (Rmult_sym (pow (Rabsolu y) n)).
Apply Rle_monotony.
Apply pow_le; Apply Rabsolu_pos.
Assumption.
Apply Rle_monotony.
Apply H0.
Apply Hrecn.
Apply Rle_trans with (Rabsolu y); [Apply Rabsolu_pos | Exact H].
Qed.

(* Dans un espace complet, la convergence normale implique la 
   convergence uniforme *)
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

(* La limite d'une suite de fonctions continues convergeant uniformement
   est continue *)
Lemma CVU_continuity : (fn:nat->R->R;f:R->R;x:R;r:posreal) (CVU fn f x r) -> ((n:nat)(y:R) (Boule x r y)->(continuity_pt (fn n) y)) -> ((y:R) (Boule x r y) -> (continuity_pt f y)).
Intros; Unfold continuity_pt; Unfold continue_in; Unfold limit1_in; Unfold limit_in; Simpl; Unfold R_dist; Intros.
Unfold CVU in H.
Cut ``0<eps/3``; [Intro | Unfold Rdiv; Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Apply Rgt_3_0]].
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

(* Continuite d'une série de fonctions normalement convergeante *)
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

(* Théorème de comparaison de convergence pour les séries *)
Lemma Rseries_CV_comp : (An,Bn:nat->R) ((n:nat)``0<=(An n)<=(Bn n)``) -> (sigTT ? [l:R](Un_cv [N:nat](sum_f_R0 Bn N) l)) -> (sigTT ? [l:R](Un_cv [N:nat](sum_f_R0 An N) l)).
Intros; Apply cv_cauchy_2.
Assert H0 := (cv_cauchy_1 ? X).
Unfold Cauchy_crit_series; Unfold Cauchy_crit.
Intros; Elim (H0 eps H1); Intros.
Exists x; Intros.
Cut (Rle (R_dist (sum_f_R0 An n) (sum_f_R0 An m)) (R_dist (sum_f_R0 Bn n) (sum_f_R0 Bn m))).
Intro; Apply Rle_lt_trans with (R_dist (sum_f_R0 Bn n) (sum_f_R0 Bn m)).
Assumption.
Apply H2; Assumption.
Assert H5 := (lt_eq_lt_dec n m).
Elim H5; Intro.
Elim a; Intro.
Rewrite (tech2 An n m); [Idtac | Assumption].
Rewrite (tech2 Bn n m); [Idtac | Assumption].
Unfold R_dist; Unfold Rminus; Do 2 Rewrite Ropp_distr1; Do 2 Rewrite <- Rplus_assoc; Do 2 Rewrite Rplus_Ropp_r; Do 2 Rewrite Rplus_Ol; Do 2 Rewrite Rabsolu_Ropp; Repeat Rewrite Rabsolu_right.
Apply sum_Rle; Intros.
Elim (H (plus (S n) n0)); Intros.
Apply H8.
Apply Rle_sym1; Apply cond_pos_sum; Intro.
Elim (H (plus (S n) n0)); Intros.
Apply Rle_trans with (An (plus (S n) n0)); Assumption.
Apply Rle_sym1; Apply cond_pos_sum; Intro.
Elim (H (plus (S n) n0)); Intros; Assumption.
Rewrite b; Unfold R_dist; Unfold Rminus; Do 2 Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Right; Reflexivity.
Rewrite (tech2 An m n); [Idtac | Assumption].
Rewrite (tech2 Bn m n); [Idtac | Assumption].
Unfold R_dist; Unfold Rminus; Do 2 Rewrite Rplus_assoc; Rewrite (Rplus_sym (sum_f_R0 An m)); Rewrite (Rplus_sym (sum_f_R0 Bn m)); Do 2 Rewrite Rplus_assoc; Do 2 Rewrite Rplus_Ropp_l; Do 2 Rewrite Rplus_Or; Repeat Rewrite Rabsolu_right.
Apply sum_Rle; Intros.
Elim (H (plus (S m) n0)); Intros; Apply H8.
Apply Rle_sym1; Apply cond_pos_sum; Intro.
Elim (H (plus (S m) n0)); Intros.
Apply Rle_trans with (An (plus (S m) n0)); Assumption.
Apply Rle_sym1.
Apply cond_pos_sum; Intro.
Elim (H (plus (S m) n0)); Intros; Assumption.
Qed.

(* Grace a la completude de R, on a le lemme suivant *)
Lemma CVN_R_CVS : (fn:nat->R->R) (CVN_R fn) -> ((x:R)(sigTT ? [l:R](Un_cv [N:nat](SP fn N x) l))).
Intros; Apply R_complet.
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
