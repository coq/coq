(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)
 
(*i $Id$ i*)

Require Max.
Require Raxioms.
Require DiscrR.
Require Rbase.
Require Rseries.
Require Rcomplet.
Require Alembert.

(* Le critère de Cauchy pour les séries *)
Definition Cauchy_crit_series [An:nat->R] : Prop := (Cauchy_crit [N:nat](sum_f_R0 An N)).

(**********)
Lemma sum_growing : (An,Bn:nat->R;N:nat) ((n:nat)``(An n)<=(Bn n)``)->``(sum_f_R0 An N)<=(sum_f_R0 Bn N)``.
Intros.
Induction N.
Simpl; Apply H.
Do 2 Rewrite tech5.
Apply Rle_trans with ``(sum_f_R0 An N)+(Bn (S N))``.
Apply Rle_compatibility; Apply H.
Do 2 Rewrite <- (Rplus_sym (Bn (S N))).
Apply Rle_compatibility; Apply HrecN.
Qed.

(**********)
Lemma Rabsolu_triang_gen : (An:nat->R;N:nat) (Rle (Rabsolu (sum_f_R0 An N)) (sum_f_R0 [i:nat](Rabsolu (An i)) N)). 
Intros.
Induction N.
Simpl.
Right; Reflexivity.
Do 2 Rewrite tech5.
Apply Rle_trans with ``(Rabsolu ((sum_f_R0 An N)))+(Rabsolu (An (S N)))``.
Apply Rabsolu_triang.
Do 2 Rewrite <- (Rplus_sym (Rabsolu (An (S N)))).
Apply Rle_compatibility; Apply HrecN.
Qed.

(**********)
Lemma cond_pos_sum : (An:nat->R;N:nat) ((n:nat)``0<=(An n)``) -> ``0<=(sum_f_R0 An N)``.
Intros.
Induction N.
Simpl; Apply H.
Rewrite tech5.
Apply ge0_plus_ge0_is_ge0.
Apply HrecN.
Apply H.
Qed.

(* Si (|An|) verifie le critere de Cauchy pour les séries , alors (An) aussi *)
Lemma cauchy_abs : (An:nat->R) (Cauchy_crit_series [i:nat](Rabsolu (An i))) -> (Cauchy_crit_series An).
Unfold Cauchy_crit_series; Unfold Cauchy_crit.
Intros.
Elim (H eps H0); Intros.
Exists x.
Intros.
Cut (Rle (R_dist (sum_f_R0 An n) (sum_f_R0 An m)) (R_dist (sum_f_R0 [i:nat](Rabsolu (An i)) n) (sum_f_R0 [i:nat](Rabsolu (An i)) m))).
Intro.
Apply Rle_lt_trans with (R_dist (sum_f_R0 [i:nat](Rabsolu (An i)) n) (sum_f_R0 [i:nat](Rabsolu (An i)) m)).
Assumption.
Apply H1; Assumption.
Assert H4 := (lt_eq_lt_dec n m).
Elim H4; Intro.
Elim a; Intro.
Rewrite (tech2 An n m); [Idtac | Assumption].
Rewrite (tech2 [i:nat](Rabsolu (An i)) n m); [Idtac | Assumption].
Unfold R_dist.
Unfold Rminus.
Do 2 Rewrite Ropp_distr1.
Do 2 Rewrite <- Rplus_assoc.
Do 2 Rewrite Rplus_Ropp_r.
Do 2 Rewrite Rplus_Ol.
Do 2 Rewrite Rabsolu_Ropp.
Rewrite (Rabsolu_right (sum_f_R0 [i:nat](Rabsolu (An (plus (S n) i))) (minus m (S n)))).
Pose Bn:=[i:nat](An (plus (S n) i)).
Replace [i:nat](Rabsolu (An (plus (S n) i))) with [i:nat](Rabsolu (Bn i)).
Apply Rabsolu_triang_gen.
Unfold Bn; Reflexivity.
Apply Rle_sym1.
Apply cond_pos_sum.
Intro; Apply Rabsolu_pos.
Rewrite b.
Unfold R_dist.
Unfold Rminus; Do 2 Rewrite Rplus_Ropp_r.
Rewrite Rabsolu_R0; Right; Reflexivity.
Rewrite (tech2 An m n); [Idtac | Assumption].
Rewrite (tech2 [i:nat](Rabsolu (An i)) m n); [Idtac | Assumption].
Unfold R_dist.
Unfold Rminus.
Do 2 Rewrite Rplus_assoc.
Rewrite (Rplus_sym (sum_f_R0 An m)).
Rewrite (Rplus_sym (sum_f_R0 [i:nat](Rabsolu (An i)) m)).
Do 2 Rewrite Rplus_assoc.
Do 2 Rewrite Rplus_Ropp_l.
Do 2 Rewrite Rplus_Or.
Rewrite (Rabsolu_right (sum_f_R0 [i:nat](Rabsolu (An (plus (S m) i))) (minus n (S m)))).
Pose Bn:=[i:nat](An (plus (S m) i)).
Replace [i:nat](Rabsolu (An (plus (S m) i))) with [i:nat](Rabsolu (Bn i)).
Apply Rabsolu_triang_gen.
Unfold Bn; Reflexivity.
Apply Rle_sym1.
Apply cond_pos_sum.
Intro; Apply Rabsolu_pos.
Qed.

(**********)
Lemma cv_cauchy_1 : (An:nat->R) (sigTT R [l:R](Un_cv [N:nat](sum_f_R0 An N) l)) -> (Cauchy_crit_series An).
Intros.
Elim X; Intros.
Unfold Un_cv in p.
Unfold Cauchy_crit_series; Unfold Cauchy_crit.
Intros.
Cut ``0<eps/2``.
Intro.
Elim (p ``eps/2`` H0); Intros.
Exists x0.
Intros.
Apply Rle_lt_trans with ``(R_dist (sum_f_R0 An n) x)+(R_dist (sum_f_R0 An m) x)``.
Unfold R_dist.
Replace ``(sum_f_R0 An n)-(sum_f_R0 An m)`` with ``((sum_f_R0 An n)-x)+ -((sum_f_R0 An m)-x)``; [Idtac | Ring].
Rewrite <- (Rabsolu_Ropp ``(sum_f_R0 An m)-x``).
Apply Rabsolu_triang.
Apply Rlt_le_trans with ``eps/2+eps/2``.
Apply Rplus_lt.
Apply H1; Assumption.
Apply H1; Assumption.
Right; Symmetry; Apply double_var.
Unfold Rdiv; Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Apply Rgt_2_0].
Qed.

Lemma cv_cauchy_2 : (An:nat->R) (Cauchy_crit_series An) -> (sigTT R [l:R](Un_cv [N:nat](sum_f_R0 An N) l)).
Intros.
Apply R_complet.
Unfold Cauchy_crit_series in H.
Exact H.
Qed.

Lemma Alembert_strong_general : (An:nat->R;k:R) ``0<=k<1`` -> ((n:nat)``(An n)<>0``) -> (Un_cv [n:nat](Rabsolu ``(An (S n))/(An n)``) k) -> (SigT R [l:R](Un_cv [N:nat](sum_f_R0 An N) l)).
Intros.
Cut (sigTT R [l:R](Un_cv [N:nat](sum_f_R0 An N) l)) -> (SigT R [l:R](Un_cv [N:nat](sum_f_R0 An N) l)).
Intro Hyp0; Apply Hyp0.
Apply cv_cauchy_2.
Apply cauchy_abs.
Apply cv_cauchy_1.
Cut (SigT R [l:R](Un_cv [N:nat](sum_f_R0 [i:nat](Rabsolu (An i)) N) l)) -> (sigTT R [l:R](Un_cv [N:nat](sum_f_R0 [i:nat](Rabsolu (An i)) N) l)).
Intro Hyp; Apply Hyp.
Apply (Alembert_strong_positive [i:nat](Rabsolu (An i)) k).
Assumption.
Intro; Apply Rabsolu_pos_lt; Apply H0.
Unfold Un_cv.
Unfold Un_cv in H1.
Unfold Rdiv.
Intros.
Elim (H1 eps H2); Intros.
Exists x; Intros.
Rewrite <- Rabsolu_Rinv.
Rewrite <- Rabsolu_mult.
Rewrite Rabsolu_Rabsolu.
Unfold Rdiv in H3; Apply H3; Assumption.
Apply H0.
Intro.
Elim X; Intros.
Apply existTT with x.
Assumption.
Intro.
Elim X; Intros.
Apply Specif.existT with x.
Assumption.
Qed.

(* Convergence de la SE dans le disque D(O,1/k) *)
(* le cas k=0 est decrit par le theoreme "Alembert" *)
Lemma Alembert_strong : (An:nat->R;x,k:R) ``0<k`` -> ((n:nat)``(An n)<>0``) -> (Un_cv [n:nat](Rabsolu ``(An (S n))/(An n)``) k) -> ``(Rabsolu x)</k`` -> (SigT R [l:R](Pser An x l)).
Intros.
Cut (SigT R [l:R](Un_cv [N:nat](sum_f_R0 [i:nat]``(An i)*(pow x i)`` N) l)).
Intro.
Elim X; Intros.
Apply Specif.existT with x0.
Apply tech12; Assumption.
Case (total_order_T x R0); Intro.
Elim s; Intro.
EApply Alembert_strong_general with ``k*(Rabsolu x)``.
Split.
Unfold Rdiv; Apply Rmult_le_pos.
Left; Assumption.
Left; Apply Rabsolu_pos_lt.
Red; Intro; Rewrite H3 in a; Elim (Rlt_antirefl ? a).
Apply Rlt_monotony_contra with ``/k``.
Apply Rlt_Rinv; Assumption.
Rewrite <- Rmult_assoc.
Rewrite <- Rinv_l_sym.
Rewrite Rmult_1l.
Rewrite Rmult_1r; Assumption.
Red; Intro; Rewrite H3 in H; Elim (Rlt_antirefl ? H).
Intro; Apply prod_neq_R0.
Apply H0.
Apply pow_nonzero.
Red; Intro; Rewrite H3 in a; Elim (Rlt_antirefl ? a).
Unfold Un_cv; Unfold Un_cv in H1.
Intros.
Cut ``0<eps/(Rabsolu x)``.
Intro.
Elim (H1 ``eps/(Rabsolu x)`` H4); Intros.
Exists x0.
Intros.
Replace ``((An (S n))*(pow x (S n)))/((An n)*(pow x n))`` with ``(An (S n))/(An n)*x``.
Unfold R_dist.
Rewrite Rabsolu_mult.
Replace ``(Rabsolu ((An (S n))/(An n)))*(Rabsolu x)-k*(Rabsolu x)`` with ``(Rabsolu x)*((Rabsolu ((An (S n))/(An n)))-k)``; [Idtac | Ring].
Rewrite Rabsolu_mult.
Rewrite Rabsolu_Rabsolu.
Apply Rlt_monotony_contra with ``/(Rabsolu x)``.
Apply Rlt_Rinv; Apply Rabsolu_pos_lt.
Red; Intro; Rewrite H7 in a; Elim (Rlt_antirefl ? a).
Rewrite <- Rmult_assoc.
Rewrite <- Rinv_l_sym.
Rewrite Rmult_1l.
Rewrite <- (Rmult_sym eps).
Unfold R_dist in H5.
Unfold Rdiv; Unfold Rdiv in H5; Apply H5; Assumption.
Apply Rabsolu_no_R0.
Red; Intro; Rewrite H7 in a; Elim (Rlt_antirefl ? a).
Unfold Rdiv; Replace (S n) with (plus n (1)); [Idtac | Ring].
Rewrite pow_add.
Simpl.
Rewrite Rmult_1r.
Rewrite Rinv_Rmult.
Replace ``(An (plus n (S O)))*((pow x n)*x)*(/(An n)*/(pow x n))`` with ``(An (plus n (S O)))*/(An n)*x*((pow x n)*/(pow x n))``; [Idtac | Ring].
Rewrite <- Rinv_r_sym.
Rewrite Rmult_1r; Reflexivity.
Apply pow_nonzero.
Red; Intro; Rewrite H7 in a; Elim (Rlt_antirefl ? a).
Apply H0.
Apply pow_nonzero.
Red; Intro; Rewrite H7 in a; Elim (Rlt_antirefl ? a).
Unfold Rdiv; Apply Rmult_lt_pos.
Assumption.
Apply Rlt_Rinv; Apply Rabsolu_pos_lt.
Red; Intro H7; Rewrite H7 in a; Elim (Rlt_antirefl ? a).
Apply Specif.existT with (An O).
Unfold Un_cv.
Intros.
Exists O.
Intros.
Unfold R_dist.
Replace (sum_f_R0 [i:nat]``(An i)*(pow x i)`` n) with (An O).
Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Assumption.
Induction n.
Simpl; Ring.
Rewrite tech5.
Rewrite <- Hrecn.
Rewrite b; Simpl; Ring.
Unfold ge; Apply le_O_n.
EApply Alembert_strong_general with ``k*(Rabsolu x)``.
Split.
Unfold Rdiv; Apply Rmult_le_pos.
Left; Assumption.
Left; Apply Rabsolu_pos_lt.
Red; Intro; Rewrite H3 in r; Elim (Rlt_antirefl ? r).
Apply Rlt_monotony_contra with ``/k``.
Apply Rlt_Rinv; Assumption.
Rewrite <- Rmult_assoc.
Rewrite <- Rinv_l_sym.
Rewrite Rmult_1l.
Rewrite Rmult_1r; Assumption.
Red; Intro; Rewrite H3 in H; Elim (Rlt_antirefl ? H).
Intro; Apply prod_neq_R0.
Apply H0.
Apply pow_nonzero.
Red; Intro; Rewrite H3 in r; Elim (Rlt_antirefl ? r).
Unfold Un_cv; Unfold Un_cv in H1.
Intros.
Cut ``0<eps/(Rabsolu x)``.
Intro.
Elim (H1 ``eps/(Rabsolu x)`` H4); Intros.
Exists x0.
Intros.
Replace ``((An (S n))*(pow x (S n)))/((An n)*(pow x n))`` with ``(An (S n))/(An n)*x``.
Unfold R_dist.
Rewrite Rabsolu_mult.
Replace ``(Rabsolu ((An (S n))/(An n)))*(Rabsolu x)-k*(Rabsolu x)`` with ``(Rabsolu x)*((Rabsolu ((An (S n))/(An n)))-k)``; [Idtac | Ring].
Rewrite Rabsolu_mult.
Rewrite Rabsolu_Rabsolu.
Apply Rlt_monotony_contra with ``/(Rabsolu x)``.
Apply Rlt_Rinv; Apply Rabsolu_pos_lt.
Red; Intro; Rewrite H7 in r; Elim (Rlt_antirefl ? r).
Rewrite <- Rmult_assoc.
Rewrite <- Rinv_l_sym.
Rewrite Rmult_1l.
Rewrite <- (Rmult_sym eps).
Unfold R_dist in H5.
Unfold Rdiv; Unfold Rdiv in H5; Apply H5; Assumption.
Apply Rabsolu_no_R0.
Red; Intro; Rewrite H7 in r; Elim (Rlt_antirefl ? r).
Unfold Rdiv; Replace (S n) with (plus n (1)); [Idtac | Ring].
Rewrite pow_add.
Simpl.
Rewrite Rmult_1r.
Rewrite Rinv_Rmult.
Replace ``(An (plus n (S O)))*((pow x n)*x)*(/(An n)*/(pow x n))`` with ``(An (plus n (S O)))*/(An n)*x*((pow x n)*/(pow x n))``; [Idtac | Ring].
Rewrite <- Rinv_r_sym.
Rewrite Rmult_1r; Reflexivity.
Apply pow_nonzero.
Red; Intro; Rewrite H7 in r; Elim (Rlt_antirefl ? r).
Apply H0.
Apply pow_nonzero.
Red; Intro; Rewrite H7 in r; Elim (Rlt_antirefl ? r).
Unfold Rdiv; Apply Rmult_lt_pos.
Assumption.
Apply Rlt_Rinv; Apply Rabsolu_pos_lt.
Red; Intro H7; Rewrite H7 in r; Elim (Rlt_antirefl ? r).
Qed.