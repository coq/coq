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
Require Rtrigo_fun.
Require Export Alembert.

(*****************************)
(* Definition of exponential *)
(*****************************)
Definition exp_in:R->R->Prop := [x,l:R](infinit_sum [i:nat]``/(INR (fact i))*(pow x i)`` l).

Lemma exp_cof_no_R0 : (n:nat) ``/(INR (fact n))<>0``.
Intro.
Apply Rinv_neq_R0.
Apply INR_fact_neq_0.
Qed.

Lemma exist_exp : (x:R)(SigT R [l:R](exp_in x l)).
Intro; Generalize (Alembert [n:nat](Rinv (INR (fact n))) x exp_cof_no_R0 Alembert_exp).
Unfold Pser exp_in.
Trivial.
Defined.

Definition exp : R -> R := [x:R](projT1 ? ? (exist_exp x)).

Lemma pow_i : (i:nat) (lt O i) -> (pow R0 i)==R0.
Intros; Apply pow_ne_zero.
Red; Intro; Rewrite H0 in H; Elim (lt_n_n ? H).
Qed.

(* Unicité de la limite d'une série convergente *)
Lemma unicite_sum : (An:nat->R;l1,l2:R) (infinit_sum An l1) -> (infinit_sum An l2) -> l1 == l2.
Unfold infinit_sum; Intros.
Case (Req_EM l1 l2); Intro.
Assumption.
Cut ``0<(Rabsolu ((l1-l2)/2))``; [Intro | Apply Rabsolu_pos_lt].
Elim (H ``(Rabsolu ((l1-l2)/2))`` H2); Intros.
Elim (H0 ``(Rabsolu ((l1-l2)/2))`` H2); Intros.
Pose N := (max x0 x); Cut (ge N x0).
Cut (ge N x).
Intros; Assert H7 := (H3 N H5); Assert H8 := (H4 N H6).
Cut ``(Rabsolu (l1-l2)) <= (R_dist (sum_f_R0 An N) l1) + (R_dist (sum_f_R0 An N) l2)``.
Intro; Assert H10 := (Rplus_lt ? ? ? ? H7 H8); Assert H11 := (Rle_lt_trans ? ? ? H9 H10); Unfold Rdiv in H11; Rewrite Rabsolu_mult in H11.
Cut ``(Rabsolu (/2))==/2``.
Intro; Rewrite H12 in H11; Assert H13 := double_var; Unfold Rdiv in H13; Rewrite <- H13 in H11.
Elim (Rlt_antirefl ? H11).
Apply Rabsolu_right; Left; Change ``0</2``; Apply Rlt_Rinv; Cut ~(O=(2)); [Intro H20; Generalize (lt_INR_0 (2) (neq_O_lt (2) H20)); Unfold INR; Intro; Assumption | Discriminate].
Unfold R_dist; Rewrite <- (Rabsolu_Ropp ``(sum_f_R0 An N)-l1``); Rewrite Ropp_distr3.
Replace ``l1-l2`` with ``((l1-(sum_f_R0 An N)))+((sum_f_R0 An N)-l2)``; [Idtac | Ring].
Apply Rabsolu_triang.
Unfold ge; Unfold N; Apply le_max_r.
Unfold ge; Unfold N; Apply le_max_l.
Unfold Rdiv; Apply prod_neq_R0.
Apply Rminus_eq_contra; Assumption.
Apply Rinv_neq_R0; DiscrR.
Qed.

(*i Calcul de $e^0$ *)
Lemma exist_exp0 : (SigT R [l:R](exp_in R0 l)).
Apply Specif.existT with R1.
Unfold exp_in; Unfold infinit_sum; Intros.
Exists O.
Intros; Replace (sum_f_R0 ([i:nat]``/(INR (fact i))*(pow R0 i)``) n) with R1.
Unfold R_dist; Replace ``1-1`` with R0; [Rewrite Rabsolu_R0; Assumption | Ring].
Induction n.
Simpl; Rewrite Rinv_R1; Ring.
Rewrite tech5.
Rewrite <- Hrecn.
Simpl.
Ring.
Unfold ge; Apply le_O_n.
Defined.

Lemma exp_0 : ``(exp 0)==1``. 
Cut (exp_in R0 (exp R0)).
Cut (exp_in R0 R1).
Unfold exp_in; Intros; EApply unicite_sum.
Apply H0.
Apply H.
Exact (projT2 ? ? exist_exp0).
Exact (projT2 ? ? (exist_exp R0)).
Qed.

(**************************************)
(* Definition of hyperbolic functions *)
(**************************************)
Definition cosh : R->R := [x:R]``((exp x)+(exp (-x)))/2``.
Definition sinh : R->R := [x:R]``((exp x)-(exp (-x)))/2``.
Definition tanh : R->R := [x:R]``(sinh x)/(cosh x)``.

Lemma cosh_0 : ``(cosh 0)==1``.
Unfold cosh; Rewrite Ropp_O; Rewrite exp_0.
Unfold Rdiv; Rewrite <- Rinv_r_sym; [Reflexivity | DiscrR].
Qed.

Lemma sinh_0 : ``(sinh 0)==0``.
Unfold sinh; Rewrite Ropp_O; Rewrite exp_0.
Unfold Rminus Rdiv; Rewrite Rplus_Ropp_r; Apply Rmult_Ol.
Qed.

(* TG de la série entière définissant COS *)
Definition cos_n [n:nat] : R := ``(pow (-1) n)/(INR (fact (mult (S (S O)) n)))``.


Lemma fact_simpl : (n:nat) (fact (S n))=(mult (S n) (fact n)).
Intro; Reflexivity.
Qed.

Lemma simpl_cos_n : (n:nat) (Rdiv (cos_n (S n)) (cos_n n))==(Ropp (Rinv (INR (mult (mult (2) (S n)) (plus (mult (2) n) (1)))))). 
Intro; Unfold cos_n; Replace (S n) with (plus n (1)); [Idtac | Ring].
Rewrite pow_add; Unfold Rdiv; Rewrite Rinv_Rmult.
Rewrite Rinv_Rinv.
Replace ``(pow ( -1) n)*(pow ( -1) (S O))*/(INR (fact (mult (S (S O)) (plus n (S O)))))*(/(pow ( -1) n)*(INR (fact (mult (S (S O)) n))))`` with ``((pow ( -1) n)*/(pow ( -1) n))*/(INR (fact (mult (S (S O)) (plus n (S O)))))*(INR (fact (mult (S (S O)) n)))*(pow (-1) (S O))``; [Idtac | Ring].
Rewrite <- Rinv_r_sym.
Rewrite Rmult_1l; Unfold pow; Rewrite Rmult_1r.
Replace (mult (S (S O)) (plus n (S O))) with (S (S (mult (S (S O)) n))); [Idtac | Ring].
Do 2 Rewrite fact_simpl; Do 2  Rewrite mult_INR; Repeat Rewrite Rinv_Rmult; Try (Apply not_O_INR; Discriminate).
Rewrite <- (Rmult_sym ``-1``).
Repeat Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r.
Replace (S (mult (S (S O)) n)) with (plus (mult (S (S O)) n) (S O)); [Idtac | Ring].
Rewrite mult_INR; Rewrite Rinv_Rmult.
Ring.
Apply not_O_INR; Discriminate.
Replace (plus (mult (S (S O)) n) (S O)) with (S (mult (S (S O)) n)); [Apply not_O_INR; Discriminate | Ring].
Apply INR_fact_neq_0.
Apply INR_fact_neq_0.
Apply prod_neq_R0; [Apply not_O_INR; Discriminate | Apply INR_fact_neq_0].
Apply pow_nonzero; DiscrR.
Apply INR_fact_neq_0.
Apply pow_nonzero; DiscrR.
Apply Rinv_neq_R0; Apply INR_fact_neq_0.
Qed.

Lemma le_n_2n : (n:nat) (le n (mult (2) n)).
Induction n.
Replace (mult (2) (O)) with O; [Apply le_n | Ring].
Intros; Replace (mult (2) (S n0)) with (S (S (mult (2) n0))).
Apply le_n_S; Apply le_S; Assumption.
Replace (S (S (mult (2) n0))) with (plus (mult (2) n0) (2)); [Idtac | Ring].
Replace (S n0) with (plus n0 (1)); [Idtac | Ring].
Ring.
Qed.

Lemma archimed_cor1 : (eps:R) ``0<eps`` -> (EX N : nat | ``/(INR N) < eps``/\(lt O N)).
Intros; Cut ``/eps < (IZR (up (/eps)))``.
Intro; Cut `0<=(up (Rinv eps))`.
Intro; Assert H2 := (IZN ? H1); Elim H2; Intros; Exists (max x (1)).
Split.
Cut ``0<(IZR (INZ x))``.
Intro; Rewrite INR_IZR_INZ; Apply Rle_lt_trans with ``/(IZR (INZ x))``.
Apply Rle_monotony_contra with (IZR (INZ x)).
Assumption.
Rewrite <- Rinv_r_sym; [Idtac | Red; Intro; Rewrite H5 in H4; Elim (Rlt_antirefl ? H4)].
Apply Rle_monotony_contra with (IZR (INZ (max x (1)))).
Apply Rlt_le_trans with (IZR (INZ x)).
Assumption.
Repeat Rewrite <- INR_IZR_INZ; Apply le_INR; Apply le_max_l.
Rewrite Rmult_1r; Rewrite (Rmult_sym (IZR (INZ (max x (S O))))); Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r; Repeat Rewrite <- INR_IZR_INZ; Apply le_INR; Apply le_max_l.
Rewrite <- INR_IZR_INZ; Apply not_O_INR.
Red; Intro;Assert H6 := (le_max_r x (1)); Cut (lt O (1)); [Intro | Apply lt_O_Sn]; Assert H8 := (lt_le_trans ? ? ? H7 H6); Rewrite H5 in H8; Elim (lt_n_n ? H8).
Pattern 1 eps; Rewrite <- Rinv_Rinv.
Apply Rinv_lt.
Apply Rmult_lt_pos; [Apply Rlt_Rinv; Assumption | Assumption].
Rewrite H3 in H0; Assumption.
Red; Intro; Rewrite H5 in H; Elim (Rlt_antirefl ? H).
Apply Rlt_trans with ``/eps``.
Apply Rlt_Rinv; Assumption.
Rewrite H3 in H0; Assumption.
Apply lt_le_trans with (1); [Apply lt_O_Sn | Apply le_max_r].
Apply le_IZR; Replace (IZR `0`) with R0; [Idtac | Reflexivity]; Left; Apply Rlt_trans with ``/eps``; [Apply Rlt_Rinv; Assumption | Assumption].
Assert H0 := (archimed ``/eps``).
Elim H0; Intros; Assumption.
Qed.

(* Convergence de la SE de TG cos_n *)
Lemma Alembert_cos : (Un_cv [n:nat]``(Rabsolu (cos_n (S n))/(cos_n n))`` R0).
Unfold Un_cv; Intros.
Assert H0 := (archimed_cor1 eps H).
Elim H0; Intros; Exists x.
Intros; Rewrite simpl_cos_n; Unfold R_dist; Unfold Rminus; Rewrite Ropp_O; Rewrite Rplus_Or; Rewrite Rabsolu_Rabsolu; Rewrite Rabsolu_Ropp; Rewrite Rabsolu_right.
Rewrite mult_INR; Rewrite Rinv_Rmult.
Cut ``/(INR (mult (S (S O)) (S n)))<1``.
Intro; Cut ``/(INR (plus (mult (S (S O)) n) (S O)))<eps``.
Intro; Rewrite <- (Rmult_1l eps).
Apply Rmult_lt; Try Assumption.
Change ``0</(INR (plus (mult (S (S O)) n) (S O)))``; Apply Rlt_Rinv; Apply lt_INR_0.
Replace (plus (mult (2) n) (1)) with (S (mult (2) n)); [Apply lt_O_Sn | Ring].
Apply Rlt_R0_R1.
Cut (lt x (plus (mult (2) n) (1))).
Intro; Assert H5 := (lt_INR ? ? H4).
Apply Rlt_trans with ``/(INR x)``.
Apply Rinv_lt.
Apply Rmult_lt_pos.
Apply lt_INR_0.
Elim H1; Intros; Assumption.
Apply lt_INR_0; Replace (plus (mult (2) n) (1)) with (S (mult (2) n)); [Apply lt_O_Sn | Ring].
Assumption.
Elim H1; Intros; Assumption.
Apply lt_le_trans with (S n).
Unfold ge in H2; Apply le_lt_n_Sm; Assumption.
Replace (plus (mult (2) n) (1)) with (S (mult (2) n)); [Idtac | Ring].
Apply le_n_S; Apply le_n_2n.
Apply Rlt_monotony_contra with (INR (mult (S (S O)) (S n))).
Apply lt_INR_0; Replace (mult (2) (S n)) with (S (S (mult (2) n))).
Apply lt_O_Sn.
Replace (S n) with (plus n (1)); [Idtac | Ring].
Ring.
Rewrite <- Rinv_r_sym.
Rewrite Rmult_1r; Replace R1 with (INR (1)); [Apply lt_INR | Reflexivity].
Replace (mult (2) (S n)) with (S (S (mult (2) n))).
Apply lt_n_S; Apply lt_O_Sn.
Replace (S n) with (plus n (1)); [Ring | Ring].
Apply not_O_INR; Discriminate.
Apply not_O_INR; Discriminate.
Replace (plus (mult (S (S O)) n) (S O)) with (S (mult (2) n)); [Apply not_O_INR; Discriminate | Ring].
Apply Rle_sym1; Left; Apply Rlt_Rinv.
Apply lt_INR_0.
Replace (mult (mult (2) (S n)) (plus (mult (2) n) (1))) with (S (S (plus (mult (4) (mult n n)) (mult (6) n)))).
Apply lt_O_Sn.
Apply INR_eq.
Repeat Rewrite S_INR; Rewrite plus_INR; Repeat Rewrite mult_INR; Rewrite plus_INR; Rewrite mult_INR; Repeat Rewrite S_INR; Replace (INR O) with R0; [Ring | Reflexivity].
Qed.

Lemma cosn_no_R0 : (n:nat)``(cos_n n)<>0``.
Intro; Unfold cos_n; Unfold Rdiv; Apply prod_neq_R0.
Apply pow_nonzero; DiscrR.
Apply Rinv_neq_R0.
Apply INR_fact_neq_0.
Qed.

(**********)
Definition cos_in:R->R->Prop := [x,l:R](infinit_sum [i:nat]``(cos_n i)*(pow x i)`` l).

(**********)
Lemma exist_cos : (x:R)(SigT R [l:R](cos_in x l)).
Intro; Generalize (Alembert cos_n x cosn_no_R0 Alembert_cos).
Unfold Pser cos_in; Trivial.
Qed.

(* Définition du cosinus *)
(*************************)
Definition cos : R -> R := [x:R](Cases (exist_cos (Rsqr x)) of (Specif.existT a b) => a end).

(* TG de la série entière définissant SIN *)
Definition sin_n [n:nat] : R := ``(pow (-1) n)/(INR (fact (plus (mult (S (S O)) n) (S O))))``.

Lemma simpl_sin_n : (n:nat) (Rdiv (sin_n (S n)) (sin_n n))==(Ropp (Rinv (INR (mult (plus (mult (2) (S n)) (1)) (mult (2) (S n)))))). 
Intro; Unfold sin_n; Replace (S n) with (plus n (1)); [Idtac | Ring].
Rewrite pow_add; Unfold Rdiv; Rewrite Rinv_Rmult.
Rewrite Rinv_Rinv.
Replace ``(pow ( -1) n)*(pow ( -1) (S O))*/(INR (fact (plus (mult (S (S O)) (plus n (S O))) (S O))))*(/(pow ( -1) n)*(INR (fact (plus (mult (S (S O)) n) (S O)))))`` with ``((pow ( -1) n)*/(pow ( -1) n))*/(INR (fact (plus (mult (S (S O)) (plus n (S O))) (S O))))*(INR (fact (plus (mult (S (S O)) n) (S O))))*(pow (-1) (S O))``; [Idtac | Ring].
Rewrite <- Rinv_r_sym.
Rewrite Rmult_1l; Unfold pow; Rewrite Rmult_1r; Replace (plus (mult (S (S O)) (plus n (S O))) (S O)) with (S (S (plus (mult (S (S O)) n) (S O)))).
Do 2 Rewrite fact_simpl; Do 2  Rewrite mult_INR; Repeat Rewrite Rinv_Rmult.
Rewrite <- (Rmult_sym ``-1``); Repeat Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r; Replace (S (plus (mult (S (S O)) n) (S O))) with (mult (S (S O)) (plus n (S O))).
Repeat Rewrite mult_INR; Repeat Rewrite Rinv_Rmult.
Ring.
Apply not_O_INR; Discriminate.
Replace (plus n (S O)) with (S n); [Apply not_O_INR; Discriminate | Ring].
Apply not_O_INR; Discriminate.
Apply prod_neq_R0.
Apply not_O_INR; Discriminate.
Replace (plus n (S O)) with (S n); [Apply not_O_INR; Discriminate | Ring].
Apply not_O_INR; Discriminate.
Replace (plus n (S O)) with (S n); [Apply not_O_INR; Discriminate | Ring].
Rewrite mult_plus_distr_r; Cut (n:nat) (S n)=(plus n (1)).
Intros; Rewrite (H (plus (mult (2) n) (1))).
Ring.
Intros; Ring.
Apply INR_fact_neq_0.
Apply not_O_INR; Discriminate.
Apply INR_fact_neq_0.
Apply not_O_INR; Discriminate.
Apply prod_neq_R0; [Apply not_O_INR; Discriminate | Apply INR_fact_neq_0].
Cut (n:nat) (S (S n))=(plus n (2)); [Intros; Rewrite (H (plus (mult (2) n) (1))); Ring | Intros; Ring].
Apply pow_nonzero; DiscrR.
Apply INR_fact_neq_0.
Apply pow_nonzero; DiscrR.
Apply Rinv_neq_R0; Apply INR_fact_neq_0.
Qed.

(* Convergence de la SE de TG sin_n *)
Lemma Alembert_sin : (Un_cv [n:nat]``(Rabsolu (sin_n (S n))/(sin_n n))`` R0).
Unfold Un_cv; Intros; Assert H0 := (archimed_cor1 eps H).
Elim H0; Intros; Exists x.
Intros; Rewrite simpl_sin_n; Unfold R_dist; Unfold Rminus; Rewrite Ropp_O; Rewrite Rplus_Or; Rewrite Rabsolu_Rabsolu; Rewrite Rabsolu_Ropp; Rewrite Rabsolu_right.
Rewrite mult_INR; Rewrite Rinv_Rmult.
Cut ``/(INR (mult (S (S O)) (S n)))<1``.
Intro; Cut ``/(INR (plus (mult (S (S O)) (S n)) (S O)))<eps``.
Intro; Rewrite <- (Rmult_1l eps); Rewrite (Rmult_sym ``/(INR (plus (mult (S (S O)) (S n)) (S O)))``); Apply Rmult_lt; Try Assumption.
Change ``0</(INR (plus (mult (S (S O)) (S n)) (S O)))``; Apply Rlt_Rinv; Apply lt_INR_0; Replace (plus (mult (2) (S n)) (1)) with (S (mult (2) (S n))); [Apply lt_O_Sn | Ring].
Apply Rlt_R0_R1.
Cut (lt x (plus (mult (2) (S n)) (1))).
Intro; Assert H5 := (lt_INR ? ? H4); Apply Rlt_trans with ``/(INR x)``.
Apply Rinv_lt.
Apply Rmult_lt_pos.
Apply lt_INR_0; Elim H1; Intros; Assumption.
Apply lt_INR_0; Replace (plus (mult (2) (S n)) (1)) with (S (mult (2) (S n))); [Apply lt_O_Sn | Ring].
Assumption.
Elim H1; Intros; Assumption.
Apply lt_le_trans with (S n).
Unfold ge in H2; Apply le_lt_n_Sm; Assumption.
Replace (plus (mult (2) (S n)) (1)) with (S (mult (2) (S n))); [Idtac | Ring].
Apply le_S; Apply le_n_2n.
Apply Rlt_monotony_contra with (INR (mult (S (S O)) (S n))).
Apply lt_INR_0; Replace (mult (2) (S n)) with (S (S (mult (2) n))); [Apply lt_O_Sn | Replace (S n) with (plus n (1)); [Idtac | Ring]; Ring].
Rewrite <- Rinv_r_sym.
Rewrite Rmult_1r; Replace R1 with (INR (1)); [Apply lt_INR | Reflexivity].
Replace (mult (2) (S n)) with (S (S (mult (2) n))).
Apply lt_n_S; Apply lt_O_Sn.
Replace (S n) with (plus n (1)); [Ring | Ring].
Apply not_O_INR; Discriminate.
Apply not_O_INR; Discriminate.
Apply not_O_INR; Discriminate.
Left; Change ``0</(INR (mult (plus (mult (S (S O)) (S n)) (S O)) (mult (S (S O)) (S n))))``; Apply Rlt_Rinv.
Apply lt_INR_0.
Replace (mult (plus (mult (2) (S n)) (1)) (mult (2) (S n))) with (S (S (S (S (S (S (plus (mult (4) (mult n n)) (mult (10) n)))))))).
Apply lt_O_Sn.
Apply INR_eq; Repeat Rewrite S_INR; Rewrite plus_INR; Repeat Rewrite mult_INR; Rewrite plus_INR; Rewrite mult_INR; Repeat Rewrite S_INR; Replace (INR O) with R0; [Ring | Reflexivity].
Qed.

Lemma sin_no_R0 : (n:nat)``(sin_n n)<>0``.
Intro; Unfold sin_n; Unfold Rdiv; Apply prod_neq_R0.
Apply pow_nonzero; DiscrR.
Apply Rinv_neq_R0; Apply INR_fact_neq_0.
Qed.

(**********)
Definition sin_in:R->R->Prop := [x,l:R](infinit_sum [i:nat]``(sin_n i)*(pow x i)`` l).

(**********)
Lemma exist_sin : (x:R)(SigT R [l:R](sin_in x l)).
Intro; Generalize (Alembert sin_n x sin_no_R0 Alembert_sin).
Unfold Pser sin_n; Trivial.
Qed.

(***********************)
(* Définition du sinus *)
Definition sin : R -> R := [x:R](Cases (exist_sin (Rsqr x)) of (Specif.existT a b) => ``x*a`` end).

(*********************************************)
(*                 PROPRIETES                *)
(*********************************************)

Lemma cos_paire : (x:R) ``(cos x)==(cos (-x))``.
Intros; Unfold cos; Replace ``(Rsqr (-x))`` with (Rsqr x).
Reflexivity.
Apply Rsqr_neg.
Qed.

Lemma sin_impaire : (x:R)``(sin (-x))==-(sin x)``.
Intro; Unfold sin; Replace ``(Rsqr (-x))`` with (Rsqr x); [Idtac | Apply Rsqr_neg]. 
Case (exist_sin (Rsqr x)); Intros; Ring.
Qed.

Axiom PI_ax : (SigT R [l:R]``0<l``/\``(sin (l/2))==1``/\((l1:R)``0<l1``->``(sin (l1/2))==1``->``l<=l1``)).

(**********)
Definition PI : R := (projT1 ? ? PI_ax).

(**********)
Lemma PI_RGT_0 : ``0<PI``.
Assert X := (projT2 ? ? PI_ax).
Elim X; Intros; Unfold PI; Exact H.
Qed.

Axiom sin_plus : (x,y:R) ``(sin (x+y))==(sin x)*(cos y)+(cos x)*(sin y)``.
Axiom  cos_plus : (x,y:R) ``(cos (x+y))==(cos x)*(cos y)-(sin x)*(sin y)``.

Lemma sin_minus : (x,y:R) ``(sin (x-y))==(sin x)*(cos y)-(cos x)*(sin y)``.
Intros; Unfold Rminus; Rewrite sin_plus.
Rewrite <- cos_paire; Rewrite sin_impaire; Ring.
Qed.
 
Lemma cos_minus : (x,y:R) ``(cos (x-y))==(cos x)*(cos y)+(sin x)*(sin y)``.
Intros; Unfold Rminus; Rewrite cos_plus.
Rewrite <- cos_paire; Rewrite sin_impaire; Ring.
Qed.

Lemma sin_0 : ``(sin 0)==0``.
Unfold sin; Case (exist_sin (Rsqr R0)).
Intros; Ring.
Qed.

Lemma exist_cos0 : (SigT R [l:R](cos_in R0 l)).
Apply Specif.existT with R1.
Unfold cos_in; Unfold infinit_sum; Intros; Exists O.
Intros.
Unfold R_dist.
Induction n.
Unfold cos_n; Simpl.
Unfold Rdiv; Rewrite Rinv_R1.
Do 2 Rewrite Rmult_1r.
Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Assumption.
Rewrite tech5.
Replace ``(cos_n (S n))*(pow 0 (S n))`` with R0.
Rewrite Rplus_Or.
Apply Hrecn; Unfold ge; Apply le_O_n.
Simpl; Ring.
Defined.

(* Calcul de (cos 0) *)
Lemma cos_0 : ``(cos 0)==1``.
Cut (cos_in R0 (cos R0)).
Cut (cos_in R0 R1).
Unfold cos_in; Intros; EApply unicite_sum.
Apply H0.
Apply H.
Exact (projT2 ? ? exist_cos0).
Assert H := (projT2 ? ? (exist_cos (Rsqr R0))); Unfold cos; Pattern 1 R0; Replace R0 with (Rsqr R0); [Exact H | Apply Rsqr_O].
Qed.

Lemma sin_PI2 : ``(sin (PI/2))==1``.
Assert H := (projT2 ? ? PI_ax); Elim H; Intros; Elim H1; Intros; Unfold PI; Exact H2.
Qed.
