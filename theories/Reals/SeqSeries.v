(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)
 
(*i $Id$ i*)

Require Rbase.
Require Rfunctions.
Require Export Rseries.
Require Export SeqProp.
Require Export Rcomplet.
Require Export PartSum.
Require Export AltSeries.
Require Export Binome.
Require Export Rsigma.
Require Export Rprod.
Require Export Cauchy_prod.
Require Export Alembert.

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
