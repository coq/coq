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
Require Max.
Require Export Rseries.
Require Export SeqProp.
Require Export Rcomplete.
Require Export PartSum.
Require Export AltSeries.
Require Export Binomial.
Require Export Rsigma.
Require Export Rprod.
Require Export Cauchy_prod.
Require Export Alembert.
V7only [ Import nat_scope. Import Z_scope. Import R_scope. ].
Open Local Scope R_scope.

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
Symmetry; EApply UL_sequence.
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
Symmetry; EApply UL_sequence.
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

(* Comparaison of convergence for series *)
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

(* Cesaro's theorem *)
Lemma Cesaro : (An,Bn:nat->R;l:R) (Un_cv Bn l) -> ((n:nat)``0<(An n)``) -> (cv_infty [n:nat](sum_f_R0 An n)) -> (Un_cv [n:nat](Rdiv (sum_f_R0 [k:nat]``(An k)*(Bn k)`` n) (sum_f_R0 An n)) l).
Proof with Trivial.
Unfold Un_cv; Intros; Assert H3 : (n:nat)``0<(sum_f_R0 An n)``.
Intro; Apply tech1.
Assert H4 : (n:nat) ``(sum_f_R0 An n)<>0``.
Intro; Red; Intro; Assert H5 := (H3 n); Rewrite H4 in H5; Elim (Rlt_antirefl ? H5).
Assert H5 := (cv_infty_cv_R0 ? H4 H1); Assert H6 : ``0<eps/2``.
Unfold Rdiv; Apply Rmult_lt_pos.
Apply Rlt_Rinv; Sup.
Elim (H ? H6); Clear H; Intros N1 H; Pose C := (Rabsolu (sum_f_R0 [k:nat]``(An k)*((Bn k)-l)`` N1)); Assert H7 : (EX N:nat | (n:nat) (le N n) -> ``C/(sum_f_R0 An n)<eps/2``).
Case (Req_EM C R0); Intro.
Exists O; Intros.
Rewrite H7; Unfold Rdiv; Rewrite Rmult_Ol; Apply Rmult_lt_pos.
Apply Rlt_Rinv; Sup.
Assert H8 : ``0<eps/(2*(Rabsolu C))``.
Unfold Rdiv; Apply Rmult_lt_pos.
Apply Rlt_Rinv; Apply Rmult_lt_pos.
Sup.
Apply Rabsolu_pos_lt.
Elim (H5 ? H8); Intros; Exists x; Intros; Assert H11 := (H9 ? H10); Unfold R_dist in H11; Unfold Rminus in H11; Rewrite Ropp_O in H11; Rewrite Rplus_Or in H11.
Apply Rle_lt_trans with (Rabsolu ``C/(sum_f_R0 An n)``).
Apply Rle_Rabsolu.
Unfold Rdiv; Rewrite Rabsolu_mult; Apply Rlt_monotony_contra with ``/(Rabsolu C)``.
Apply Rlt_Rinv; Apply Rabsolu_pos_lt.
Rewrite <- Rmult_assoc; Rewrite <- Rinv_l_sym.
Rewrite Rmult_1l; Replace ``/(Rabsolu C)*(eps*/2)`` with ``eps/(2*(Rabsolu C))``.
Unfold Rdiv; Rewrite Rinv_Rmult.
Ring.
DiscrR.
Apply Rabsolu_no_R0.
Apply Rabsolu_no_R0.
Elim H7; Clear H7; Intros N2 H7; Pose N := (max N1 N2); Exists (S N); Intros; Unfold R_dist; Replace (Rminus (Rdiv (sum_f_R0 [k:nat]``(An k)*(Bn k)`` n) (sum_f_R0 An n)) l) with (Rdiv (sum_f_R0 [k:nat]``(An k)*((Bn k)-l)`` n) (sum_f_R0 An n)).
Assert H9 : (lt N1 n).
Apply lt_le_trans with (S N).
Apply le_lt_n_Sm; Unfold N; Apply le_max_l.
Rewrite (tech2 [k:nat]``(An k)*((Bn k)-l)`` ? ? H9); Unfold Rdiv; Rewrite Rmult_Rplus_distrl; Apply Rle_lt_trans with (Rplus (Rabsolu (Rdiv (sum_f_R0 [k:nat]``(An k)*((Bn k)-l)`` N1) (sum_f_R0 An n))) (Rabsolu (Rdiv (sum_f_R0 [i:nat]``(An (plus (S N1) i))*((Bn (plus (S N1) i))-l)`` (minus n (S N1))) (sum_f_R0 An n)))).
Apply Rabsolu_triang.
Rewrite (double_var eps); Apply Rplus_lt.
Unfold Rdiv; Rewrite Rabsolu_mult; Fold C; Rewrite Rabsolu_right.
Apply (H7 n); Apply le_trans with (S N).
Apply le_trans with N; [Unfold N; Apply le_max_r | Apply le_n_Sn].
Apply Rle_sym1; Left; Apply Rlt_Rinv.

Unfold R_dist in H; Unfold Rdiv; Rewrite Rabsolu_mult; Rewrite (Rabsolu_right ``/(sum_f_R0 An n)``).
Apply Rle_lt_trans with (Rmult (sum_f_R0 [i:nat](Rabsolu ``(An (plus (S N1) i))*((Bn (plus (S N1) i))-l)``) (minus n (S N1))) ``/(sum_f_R0 An n)``).
Do 2 Rewrite <- (Rmult_sym ``/(sum_f_R0 An n)``); Apply Rle_monotony.
Left; Apply Rlt_Rinv.
Apply (sum_Rabsolu [i:nat]``(An (plus (S N1) i))*((Bn (plus (S N1) i))-l)`` (minus n (S N1))).
Apply Rle_lt_trans with (Rmult (sum_f_R0 [i:nat]``(An (plus (S N1) i))*eps/2`` (minus n (S N1))) ``/(sum_f_R0 An n)``).
Do 2 Rewrite <- (Rmult_sym ``/(sum_f_R0 An n)``); Apply Rle_monotony.
Left; Apply Rlt_Rinv.
Apply sum_Rle; Intros; Rewrite Rabsolu_mult; Pattern 2 (An (plus (S N1) n0)); Rewrite <- (Rabsolu_right (An (plus (S N1) n0))).
Apply Rle_monotony.
Apply Rabsolu_pos.
Left; Apply H; Unfold ge; Apply le_trans with (S N1); [Apply le_n_Sn | Apply le_plus_l].
Apply Rle_sym1; Left.
Rewrite <- (scal_sum [i:nat](An (plus (S N1) i)) (minus n (S N1)) ``eps/2``); Unfold Rdiv; Repeat Rewrite Rmult_assoc; Apply Rlt_monotony.
Pattern 2 ``/2``; Rewrite <- Rmult_1r; Apply Rlt_monotony.
Apply Rlt_Rinv; Sup.
Rewrite Rmult_sym; Apply Rlt_monotony_contra with (sum_f_R0 An n).
Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym.
Rewrite Rmult_1l; Rewrite Rmult_1r; Rewrite (tech2 An N1 n).
Rewrite Rplus_sym; Pattern 1 (sum_f_R0 [i:nat](An (plus (S N1) i)) (minus n (S N1))); Rewrite <- Rplus_Or; Apply Rlt_compatibility.
Apply Rle_sym1; Left; Apply Rlt_Rinv.
Replace (sum_f_R0 [k:nat]``(An k)*((Bn k)-l)`` n) with (Rplus (sum_f_R0 [k:nat]``(An k)*(Bn k)`` n) (sum_f_R0 [k:nat]``(An k)*-l`` n)).
Rewrite <- (scal_sum An n ``-l``); Field.
Rewrite <- plus_sum; Apply sum_eq; Intros; Ring.
Qed.

Lemma Cesaro_1 : (An:nat->R;l:R) (Un_cv An l) -> (Un_cv [n:nat]``(sum_f_R0 An (pred n))/(INR n)`` l).
Proof with Trivial.
Intros Bn l H; Pose An := [_:nat]R1.
Assert H0 : (n:nat) ``0<(An n)``.
Intro; Unfold An; Apply Rlt_R0_R1.
Assert H1 : (n:nat)``0<(sum_f_R0 An n)``.
Intro; Apply tech1.
Assert H2 : (cv_infty [n:nat](sum_f_R0 An n)).
Unfold cv_infty; Intro; Case (total_order_Rle M R0); Intro.
Exists O; Intros; Apply Rle_lt_trans with R0.
Assert H2 : ``0<M``.
Auto with real.
Clear n; Pose m := (up M); Elim (archimed M); Intros; Assert H5 : `0<=m`.
Apply le_IZR; Unfold m; Simpl; Left; Apply Rlt_trans with M.
Elim (IZN ? H5); Intros; Exists x; Intros; Unfold An; Rewrite sum_cte; Rewrite Rmult_1l; Apply Rlt_trans with (IZR (up M)).
Apply Rle_lt_trans with (INR x).
Rewrite INR_IZR_INZ; Fold m; Rewrite <- H6; Right.
Apply lt_INR; Apply le_lt_n_Sm.
Assert H3 := (Cesaro ? ? ? H H0 H2).
Unfold Un_cv; Unfold Un_cv in H3; Intros; Elim (H3 ? H4); Intros; Exists (S x); Intros; Unfold R_dist; Unfold R_dist in H5; Apply Rle_lt_trans with (Rabsolu (Rminus (Rdiv (sum_f_R0 [k:nat]``(An k)*(Bn k)`` (pred n)) (sum_f_R0 An (pred n))) l)).
Right; Replace ``(sum_f_R0 Bn (pred n))/(INR n)-l`` with (Rminus (Rdiv (sum_f_R0 [k:nat]``(An k)*(Bn k)`` (pred n)) (sum_f_R0 An (pred n))) l).
Unfold Rminus; Do 2 Rewrite <- (Rplus_sym ``-l``); Apply Rplus_plus_r.
Unfold An; Replace (sum_f_R0 [k:nat]``1*(Bn k)`` (pred n)) with (sum_f_R0 Bn (pred n)).
Rewrite sum_cte; Rewrite Rmult_1l; Replace (S (pred n)) with n.
Apply S_pred with O; Apply lt_le_trans with (S x).
Apply lt_O_Sn.
Apply sum_eq; Intros; Ring.
Apply H5; Unfold ge; Apply le_S_n; Replace (S (pred n)) with n.
Apply S_pred with O; Apply lt_le_trans with (S x).
Apply lt_O_Sn.
Qed.
