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
Require PartSum.
V7only [ Import nat_scope. Import Z_scope. Import R_scope. ].
Open Local Scope R_scope.

Definition C [n,p:nat] : R := ``(INR (fact n))/((INR (fact p))*(INR (fact (minus n p))))``.

Lemma pascal_step1 : (n,i:nat) (le i n) -> (C n i) == (C n (minus n i)).
Intros; Unfold C; Replace (minus n (minus n i)) with i.
Rewrite Rmult_sym.
Reflexivity.
Apply plus_minus; Rewrite plus_sym; Apply le_plus_minus; Assumption.
Qed.

Lemma pascal_step2 : (n,i:nat) (le i n) -> (C (S n) i) == ``(INR (S n))/(INR (minus (S n) i))*(C n i)``.
Intros; Unfold C; Replace (minus (S n) i) with (S (minus n i)).
Cut (n:nat) (fact (S n))=(mult (S n) (fact n)).
Intro; Repeat Rewrite H0.
Unfold Rdiv; Repeat Rewrite mult_INR; Repeat Rewrite Rinv_Rmult.
Ring.
Apply INR_fact_neq_0.
Apply INR_fact_neq_0.
Apply not_O_INR; Discriminate.
Apply INR_fact_neq_0.
Apply INR_fact_neq_0.
Apply prod_neq_R0.
Apply not_O_INR; Discriminate.
Apply INR_fact_neq_0.
Intro; Reflexivity.
Apply minus_Sn_m; Assumption.
Qed.

Lemma pascal_step3 : (n,i:nat) (lt i n) -> (C n (S i)) == ``(INR (minus n i))/(INR (S i))*(C n i)``.
Intros; Unfold C.
Cut (n:nat) (fact (S n))=(mult (S n) (fact n)).
Intro.
Cut (minus n i) = (S (minus n (S i))).
Intro.
Pattern 2 (minus n i); Rewrite H1.
Repeat Rewrite H0; Unfold Rdiv; Repeat Rewrite mult_INR; Repeat Rewrite Rinv_Rmult.
Rewrite <- H1; Rewrite (Rmult_sym ``/(INR (minus n i))``); Repeat Rewrite Rmult_assoc; Rewrite (Rmult_sym (INR (minus n i))); Repeat Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym.
Ring.
Apply not_O_INR; Apply minus_neq_O; Assumption.
Apply not_O_INR; Discriminate.
Apply INR_fact_neq_0.
Apply INR_fact_neq_0.
Apply prod_neq_R0; [Apply not_O_INR; Discriminate | Apply INR_fact_neq_0].
Apply not_O_INR; Discriminate.
Apply INR_fact_neq_0.
Apply prod_neq_R0; [Apply not_O_INR; Discriminate | Apply INR_fact_neq_0].
Apply INR_fact_neq_0.
Rewrite minus_Sn_m.
Simpl; Reflexivity.
Apply lt_le_S; Assumption.
Intro; Reflexivity.
Qed.

(**********)
Lemma pascal : (n,i:nat) (lt i n) -> ``(C n i)+(C n (S i))==(C (S n) (S i))``.
Intros.
Rewrite pascal_step3; [Idtac | Assumption].
Replace ``(C n i)+(INR (minus n i))/(INR (S i))*(C n i)`` with ``(C n i)*(1+(INR (minus n i))/(INR (S i)))``; [Idtac | Ring].
Replace ``1+(INR (minus n i))/(INR (S i))`` with ``(INR (S n))/(INR (S i))``.
Rewrite pascal_step1.
Rewrite Rmult_sym; Replace (S i) with (minus (S n) (minus n i)).
Rewrite <- pascal_step2.
Apply pascal_step1.
Apply le_trans with n.
Apply le_minusni_n.
Apply lt_le_weak; Assumption.
Apply le_n_Sn.
Apply le_minusni_n.
Apply lt_le_weak; Assumption.
Rewrite <- minus_Sn_m.
Cut (minus n (minus n i))=i.
Intro; Rewrite H0; Reflexivity.
Symmetry; Apply plus_minus.
Rewrite plus_sym; Rewrite le_plus_minus_r.
Reflexivity.
Apply lt_le_weak; Assumption.
Apply le_minusni_n; Apply lt_le_weak; Assumption.
Apply lt_le_weak; Assumption.
Unfold Rdiv.
Repeat Rewrite S_INR.
Rewrite minus_INR.
Cut ``((INR i)+1)<>0``.
Intro.
Apply r_Rmult_mult with ``(INR i)+1``; [Idtac | Assumption].
Rewrite Rmult_Rplus_distr.
Rewrite Rmult_1r.
Do 2 Rewrite (Rmult_sym ``(INR i)+1``).
Repeat Rewrite Rmult_assoc.
Rewrite <- Rinv_l_sym; [Idtac | Assumption].
Ring.
Rewrite <- S_INR.
Apply not_O_INR; Discriminate.
Apply lt_le_weak; Assumption.
Qed.

(*********************)
(*********************)
Lemma binomial : (x,y:R;n:nat) ``(pow (x+y) n)``==(sum_f_R0 [i:nat]``(C n i)*(pow x i)*(pow y (minus n i))`` n).
Intros; Induction n.
Unfold C; Simpl; Unfold Rdiv; Repeat Rewrite Rmult_1r; Rewrite Rinv_R1; Ring.
Pattern 1 (S n); Replace (S n) with (plus n (1)); [Idtac | Ring].
Rewrite pow_add; Rewrite Hrecn.
Replace ``(pow (x+y) (S O))`` with ``x+y``; [Idtac | Simpl; Ring].
Rewrite tech5.
Cut (p:nat)(C p p)==R1.
Cut (p:nat)(C p O)==R1.
Intros; Rewrite H0; Rewrite <- minus_n_n; Rewrite Rmult_1l.
Replace (pow y O) with R1; [Rewrite Rmult_1r | Simpl; Reflexivity].
Induction n.
Simpl; Do 2 Rewrite H; Ring.
(* N >= 1 *)
Pose N := (S n).
Rewrite Rmult_Rplus_distr.
Replace (Rmult (sum_f_R0 ([i:nat]``(C N i)*(pow x i)*(pow y (minus N i))``) N) x) with (sum_f_R0 [i:nat]``(C N i)*(pow x (S i))*(pow y (minus N i))`` N).
Replace (Rmult (sum_f_R0 ([i:nat]``(C N i)*(pow x i)*(pow y (minus N i))``) N) y) with (sum_f_R0 [i:nat]``(C N i)*(pow x i)*(pow y (minus (S N) i))`` N).
Rewrite (decomp_sum [i:nat]``(C (S N) i)*(pow x i)*(pow y (minus (S N) i))`` N).
Rewrite H; Replace (pow x O) with R1; [Idtac | Reflexivity].
Do 2 Rewrite Rmult_1l.
Replace (minus (S N) O) with (S N); [Idtac | Reflexivity].
Pose An := [i:nat]``(C N i)*(pow x (S i))*(pow y (minus N i))``.
Pose Bn := [i:nat]``(C N (S i))*(pow x (S i))*(pow y (minus N i))``.
Replace (pred N) with n.
Replace (sum_f_R0 ([i:nat]``(C (S N) (S i))*(pow x (S i))*(pow y (minus (S N) (S i)))``) n) with (sum_f_R0 [i:nat]``(An i)+(Bn i)`` n).
Rewrite plus_sum.
Replace (pow x (S N)) with (An (S n)).
Rewrite (Rplus_sym (sum_f_R0 An n)).
Repeat Rewrite Rplus_assoc.
Rewrite <- tech5.
Fold N.
Pose Cn := [i:nat]``(C N i)*(pow x i)*(pow y (minus (S N) i))``.
Cut (i:nat) (lt i N)-> (Cn (S i))==(Bn i).
Intro; Replace (sum_f_R0 Bn n) with (sum_f_R0 [i:nat](Cn (S i)) n).
Replace (pow y (S N)) with (Cn O).
Rewrite <- Rplus_assoc; Rewrite (decomp_sum Cn N).
Replace (pred N) with n.
Ring.
Unfold N; Simpl; Reflexivity.
Unfold N; Apply lt_O_Sn.
Unfold Cn; Rewrite H; Simpl; Ring.
Apply sum_eq.
Intros; Apply H1.
Unfold N; Apply le_lt_trans with n; [Assumption | Apply lt_n_Sn].
Intros; Unfold Bn Cn.
Replace (minus (S N) (S i)) with (minus N i); Reflexivity.
Unfold An; Fold N; Rewrite <- minus_n_n; Rewrite H0; Simpl; Ring.
Apply sum_eq.
Intros; Unfold An Bn; Replace (minus (S N) (S i)) with (minus N i); [Idtac | Reflexivity].
Rewrite <- pascal; [Ring | Apply le_lt_trans with n; [Assumption | Unfold N; Apply lt_n_Sn]].
Unfold N; Reflexivity.
Unfold N; Apply lt_O_Sn.
Rewrite <- (Rmult_sym y); Rewrite scal_sum; Apply sum_eq.
Intros; Replace (minus (S N) i) with (S (minus N i)).
Replace (S (minus N i)) with (plus (minus N i) (1)); [Idtac | Ring].
Rewrite pow_add; Replace (pow y (S O)) with y; [Idtac | Simpl; Ring]; Ring.
Apply minus_Sn_m; Assumption.
Rewrite <- (Rmult_sym x); Rewrite scal_sum; Apply sum_eq.
Intros; Replace (S i) with (plus i (1)); [Idtac | Ring]; Rewrite pow_add; Replace (pow x (S O)) with x; [Idtac | Simpl; Ring]; Ring.
Intro; Unfold C.
Replace (INR (fact O)) with R1; [Idtac | Reflexivity].
Replace (minus p O) with p; [Idtac | Apply minus_n_O].
Rewrite Rmult_1l; Unfold Rdiv; Rewrite <- Rinv_r_sym; [Reflexivity | Apply INR_fact_neq_0].
Intro; Unfold C.
Replace (minus p p) with O; [Idtac | Apply minus_n_n].
Replace (INR (fact O)) with R1; [Idtac | Reflexivity].
Rewrite Rmult_1r; Unfold Rdiv; Rewrite <- Rinv_r_sym; [Reflexivity | Apply INR_fact_neq_0].
Qed.
