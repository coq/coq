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
Require Ranalysis1.
Require PSeries_reg.
Require Div2.
Require Even.
Require Max.
V7only [Import R_scope.].
Open Local Scope nat_scope.
V7only [Import nat_scope.].
Open Local Scope R_scope.

Definition E1 [x:R] : nat->R := [N:nat](sum_f_R0 [k:nat]``/(INR (fact k))*(pow x k)`` N).

Lemma E1_cvg : (x:R) (Un_cv (E1 x) (exp x)).
Intro; Unfold exp; Unfold projT1.
Case (exist_exp x); Intro.
Unfold exp_in Un_cv; Unfold infinit_sum E1; Trivial.
Qed.

Definition Reste_E [x,y:R] : nat->R := [N:nat](sum_f_R0 [k:nat](sum_f_R0 [l:nat]``/(INR (fact (S (plus l k))))*(pow x (S (plus l k)))*(/(INR (fact (minus N l)))*(pow y (minus N l)))`` (pred (minus N k))) (pred N)).

Lemma exp_form : (x,y:R;n:nat) (lt O n) -> ``(E1 x n)*(E1 y n)-(Reste_E x y n)==(E1 (x+y) n)``.
Intros; Unfold E1.
Rewrite cauchy_finite.
Unfold Reste_E; Unfold Rminus; Rewrite Rplus_assoc; Rewrite Rplus_Ropp_r; Rewrite Rplus_Or; Apply sum_eq; Intros.
Rewrite binomial.
Rewrite scal_sum; Apply sum_eq; Intros.
Unfold C; Unfold Rdiv; Repeat Rewrite Rmult_assoc; Rewrite (Rmult_sym (INR (fact i))); Repeat Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r; Rewrite Rinv_Rmult.
Ring.
Apply INR_fact_neq_0.
Apply INR_fact_neq_0.
Apply INR_fact_neq_0.
Apply H.
Qed.

Definition maj_Reste_E [x,y:R] : nat->R := [N:nat]``4*(pow (Rmax R1 (Rmax (Rabsolu x) (Rabsolu y))) (mult (S (S O)) N))/(Rsqr (INR (fact (div2 (pred N)))))``.

Lemma Rle_Rinv : (x,y:R) ``0<x`` -> ``0<y`` -> ``x<=y`` -> ``/y<=/x``.
Intros; Apply Rle_monotony_contra with x.
Apply H.
Rewrite <- Rinv_r_sym.
Apply Rle_monotony_contra with y.
Apply H0.
Rewrite Rmult_1r; Rewrite Rmult_sym; Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r; Apply H1.
Red; Intro; Rewrite H2 in H0; Elim (Rlt_antirefl ? H0).
Red; Intro; Rewrite H2 in H; Elim (Rlt_antirefl ? H).
Qed.

(**********)
Lemma div2_double : (N:nat) (div2 (mult (2) N))=N.
Intro; Induction N.
Reflexivity.
Replace (mult (2) (S N)) with (S (S (mult (2) N))).
Simpl; Simpl in HrecN; Rewrite HrecN; Reflexivity.
Apply INR_eq; Do 2 Rewrite S_INR; Do 2 Rewrite mult_INR; Repeat Rewrite S_INR; Ring.
Qed.

Lemma div2_S_double : (N:nat) (div2 (S (mult (2) N)))=N.
Intro; Induction N.
Reflexivity.
Replace (mult (2) (S N)) with (S (S (mult (2) N))).
Simpl; Simpl in HrecN; Rewrite HrecN; Reflexivity.
Apply INR_eq; Do 2 Rewrite S_INR; Do 2 Rewrite mult_INR; Repeat Rewrite S_INR; Ring.
Qed.

Lemma div2_not_R0 : (N:nat) (lt (1) N) -> (lt O (div2 N)).
Intros; Induction N.
Elim (lt_n_O ? H).
Cut (lt (1) N)\/N=(1).
Intro; Elim H0; Intro.
Assert H2 := (even_odd_dec N).
Elim H2; Intro.
Rewrite <- (even_div2 ? a); Apply HrecN; Assumption.
Rewrite <- (odd_div2 ? b); Apply lt_O_Sn.
Rewrite H1; Simpl; Apply lt_O_Sn.
Inversion H.
Right; Reflexivity.
Left; Apply lt_le_trans with (2); [Apply lt_n_Sn | Apply H1].
Qed.

Lemma Reste_E_maj : (x,y:R;N:nat) (lt O N) -> ``(Rabsolu (Reste_E x y N))<=(maj_Reste_E x y N)``.
Intros; Pose M := (Rmax R1 (Rmax (Rabsolu x) (Rabsolu y))).
Apply Rle_trans with (Rmult (pow M (mult (2) N)) (sum_f_R0 [k:nat](sum_f_R0 [l:nat]``/(Rsqr (INR (fact (div2 (S N)))))`` (pred (minus N k))) (pred N))). 
Unfold Reste_E.
Apply Rle_trans with (sum_f_R0 [k:nat](Rabsolu (sum_f_R0 [l:nat]``/(INR (fact (S (plus l k))))*(pow x (S (plus l k)))*(/(INR (fact (minus N l)))*(pow y (minus N l)))`` (pred (minus N k)))) (pred N)).
Apply (sum_Rabsolu [k:nat](sum_f_R0 [l:nat]``/(INR (fact (S (plus l k))))*(pow x (S (plus l k)))*(/(INR (fact (minus N l)))*(pow y (minus N l)))`` (pred (minus N k))) (pred N)).
Apply Rle_trans with (sum_f_R0 [k:nat](sum_f_R0 [l:nat]``(Rabsolu (/(INR (fact (S (plus l k))))*(pow x (S (plus l k)))*(/(INR (fact (minus N l)))*(pow y (minus N l)))))`` (pred (minus N k))) (pred N)).
Apply sum_Rle; Intros.
Apply (sum_Rabsolu [l:nat]``/(INR (fact (S (plus l n))))*(pow x (S (plus l n)))*(/(INR (fact (minus N l)))*(pow y (minus N l)))``).
Apply Rle_trans with (sum_f_R0 [k:nat](sum_f_R0 [l:nat]``(pow M (mult (S (S O)) N))*/(INR (fact (S l)))*/(INR (fact (minus N l)))`` (pred (minus N k))) (pred N)).
Apply sum_Rle; Intros.
Apply sum_Rle; Intros.
Repeat Rewrite Rabsolu_mult.
Do 2 Rewrite <- Pow_Rabsolu.
Rewrite (Rabsolu_right ``/(INR (fact (S (plus n0 n))))``).
Rewrite (Rabsolu_right ``/(INR (fact (minus N n0)))``).
Replace ``/(INR (fact (S (plus n0 n))))*(pow (Rabsolu x) (S (plus n0 n)))*
   (/(INR (fact (minus N n0)))*(pow (Rabsolu y) (minus N n0)))`` with ``/(INR (fact (minus N n0)))*/(INR (fact (S (plus n0 n))))*(pow (Rabsolu x) (S (plus n0 n)))*(pow (Rabsolu y) (minus N n0))``; [Idtac | Ring].
Rewrite <- (Rmult_sym ``/(INR (fact (minus N n0)))``).
Repeat Rewrite Rmult_assoc.
Apply Rle_monotony.
Left; Apply Rlt_Rinv; Apply INR_fact_lt_0.
Apply Rle_trans with ``/(INR (fact (S n0)))*(pow (Rabsolu x) (S (plus n0 n)))*(pow (Rabsolu y) (minus N n0))``.
Rewrite (Rmult_sym ``/(INR (fact (S (plus n0 n))))``); Rewrite (Rmult_sym ``/(INR (fact (S n0)))``); Repeat Rewrite Rmult_assoc; Apply Rle_monotony.
Apply pow_le; Apply Rabsolu_pos.
Rewrite (Rmult_sym ``/(INR (fact (S n0)))``); Apply Rle_monotony.
Apply pow_le; Apply Rabsolu_pos.
Apply Rle_Rinv.
Apply INR_fact_lt_0.
Apply INR_fact_lt_0.
Apply le_INR; Apply fact_growing; Apply le_n_S.
Apply le_plus_l.
Rewrite (Rmult_sym ``(pow M (mult (S (S O)) N))``); Rewrite Rmult_assoc; Apply Rle_monotony.
Left; Apply Rlt_Rinv; Apply INR_fact_lt_0.
Apply Rle_trans with ``(pow M (S (plus n0 n)))*(pow (Rabsolu y) (minus N n0))``.
Do 2 Rewrite <- (Rmult_sym ``(pow (Rabsolu y) (minus N n0))``).
Apply Rle_monotony.
Apply pow_le; Apply Rabsolu_pos.
Apply pow_incr; Split.
Apply Rabsolu_pos.
Apply Rle_trans with (Rmax (Rabsolu x) (Rabsolu y)).
Apply RmaxLess1.
Unfold M; Apply RmaxLess2.
Apply Rle_trans with ``(pow M (S (plus n0 n)))*(pow M (minus N n0))``.
Apply Rle_monotony.
Apply pow_le; Apply Rle_trans with R1.
Left; Apply Rlt_R0_R1.
Unfold M; Apply RmaxLess1.
Apply pow_incr; Split.
Apply Rabsolu_pos.
Apply Rle_trans with (Rmax (Rabsolu x) (Rabsolu y)).
Apply RmaxLess2.
Unfold M; Apply RmaxLess2.
Rewrite <- pow_add; Replace (plus (S (plus n0 n)) (minus N n0)) with (plus N (S n)).
Apply Rle_pow.
Unfold M; Apply RmaxLess1.
Replace (mult (2) N) with (plus N N); [Idtac | Ring].
Apply le_reg_l.
Replace N with (S (pred N)).
Apply le_n_S; Apply H0.
Symmetry; Apply S_pred with O; Apply H.
Apply INR_eq; Do 2 Rewrite plus_INR; Do 2 Rewrite S_INR; Rewrite plus_INR; Rewrite minus_INR.
Ring.
Apply le_trans with (pred (minus N n)).
Apply H1.
Apply le_S_n.
Replace (S (pred (minus N n))) with (minus N n).
Apply le_trans with N.
Apply simpl_le_plus_l with n.
Rewrite <- le_plus_minus.
Apply le_plus_r.
Apply le_trans with (pred N).
Apply H0.
Apply le_pred_n.
Apply le_n_Sn.
Apply S_pred with O.
Apply simpl_lt_plus_l with n.
Rewrite <- le_plus_minus.
Replace (plus n (0)) with n; [Idtac | Ring].
Apply le_lt_trans with (pred N).
Apply H0.
Apply lt_pred_n_n.
Apply H.
Apply le_trans with (pred N).
Apply H0.
Apply le_pred_n.
Apply Rle_sym1; Left; Apply Rlt_Rinv; Apply INR_fact_lt_0.
Apply Rle_sym1; Left; Apply Rlt_Rinv; Apply INR_fact_lt_0.
Rewrite scal_sum.
Apply sum_Rle; Intros.
Rewrite <- Rmult_sym.
Rewrite scal_sum.
Apply sum_Rle; Intros.
Rewrite (Rmult_sym ``/(Rsqr (INR (fact (div2 (S N)))))``).
Rewrite Rmult_assoc; Apply Rle_monotony.
Apply pow_le.
Apply Rle_trans with R1.
Left; Apply Rlt_R0_R1.
Unfold M; Apply RmaxLess1.
Assert H2 := (even_odd_cor N).
Elim H2; Intros N0 H3.
Elim H3; Intro.
Apply Rle_trans with ``/(INR (fact n0))*/(INR (fact (minus N n0)))``.
Do 2 Rewrite <- (Rmult_sym ``/(INR (fact (minus N n0)))``).
Apply Rle_monotony.
Left; Apply Rlt_Rinv; Apply INR_fact_lt_0.
Apply Rle_Rinv.
Apply INR_fact_lt_0.
Apply INR_fact_lt_0.
Apply le_INR.
Apply fact_growing.
Apply le_n_Sn.
Replace ``/(INR (fact n0))*/(INR (fact (minus N n0)))`` with ``(C N n0)/(INR (fact N))``.
Pattern 1 N; Rewrite H4.
Apply Rle_trans with ``(C N N0)/(INR (fact N))``.
Unfold Rdiv; Do 2 Rewrite <- (Rmult_sym ``/(INR (fact N))``).
Apply Rle_monotony.
Left; Apply Rlt_Rinv; Apply INR_fact_lt_0.
Rewrite H4.
Apply C_maj.
Rewrite <- H4; Apply le_trans with (pred (minus N n)).
Apply H1.
Apply le_S_n.
Replace (S (pred (minus N n))) with (minus N n).
Apply le_trans with N.
Apply simpl_le_plus_l with n.
Rewrite <- le_plus_minus.
Apply le_plus_r.
Apply le_trans with (pred N).
Apply H0.
Apply le_pred_n.
Apply le_n_Sn.
Apply S_pred with O.
Apply simpl_lt_plus_l with n.
Rewrite <- le_plus_minus.
Replace (plus n (0)) with n; [Idtac | Ring].
Apply le_lt_trans with (pred N).
Apply H0.
Apply lt_pred_n_n.
Apply H.
Apply le_trans with (pred N).
Apply H0.
Apply le_pred_n.
Replace ``(C N N0)/(INR (fact N))`` with ``/(Rsqr (INR (fact N0)))``.
Rewrite H4; Rewrite div2_S_double; Right; Reflexivity.
Unfold Rsqr C Rdiv.
Repeat Rewrite Rinv_Rmult.
Rewrite (Rmult_sym (INR (fact N))).
Repeat Rewrite Rmult_assoc.
Rewrite <- Rinv_r_sym.
Rewrite Rmult_1r; Replace (minus N N0) with N0.
Ring.
Replace N with (plus N0 N0).
Symmetry; Apply minus_plus.
Rewrite H4.
Apply INR_eq; Rewrite plus_INR; Rewrite mult_INR; Do 2 Rewrite S_INR; Ring.
Apply INR_fact_neq_0.
Apply INR_fact_neq_0.
Apply INR_fact_neq_0.
Apply INR_fact_neq_0.
Apply INR_fact_neq_0.
Unfold C Rdiv.
Rewrite (Rmult_sym (INR (fact N))).
Repeat Rewrite Rmult_assoc.
Rewrite <- Rinv_r_sym.
Rewrite Rinv_Rmult.
Rewrite Rmult_1r; Ring.
Apply INR_fact_neq_0.
Apply INR_fact_neq_0.
Apply INR_fact_neq_0.
Replace ``/(INR (fact (S n0)))*/(INR (fact (minus N n0)))`` with ``(C (S N) (S n0))/(INR (fact (S N)))``.
Apply Rle_trans with ``(C (S N) (S N0))/(INR (fact (S N)))``.
Unfold Rdiv; Do 2 Rewrite <- (Rmult_sym ``/(INR (fact (S N)))``).
Apply Rle_monotony.
Left; Apply Rlt_Rinv; Apply INR_fact_lt_0.
Cut (S N) = (mult (2) (S N0)).
Intro; Rewrite H5; Apply C_maj.
Rewrite <- H5; Apply le_n_S.
Apply le_trans with (pred (minus N n)).
Apply H1.
Apply le_S_n.
Replace (S (pred (minus N n))) with (minus N n).
Apply le_trans with N.
Apply simpl_le_plus_l with n.
Rewrite <- le_plus_minus.
Apply le_plus_r.
Apply le_trans with (pred N).
Apply H0.
Apply le_pred_n.
Apply le_n_Sn.
Apply S_pred with O.
Apply simpl_lt_plus_l with n.
Rewrite <- le_plus_minus.
Replace (plus n (0)) with n; [Idtac | Ring].
Apply le_lt_trans with (pred N).
Apply H0.
Apply lt_pred_n_n.
Apply H.
Apply le_trans with (pred N).
Apply H0.
Apply le_pred_n.
Apply INR_eq; Rewrite H4.
Do 2 Rewrite S_INR; Do 2 Rewrite mult_INR; Repeat  Rewrite S_INR; Ring.
Cut (S N) = (mult (2) (S N0)).
Intro.
Replace ``(C (S N) (S N0))/(INR (fact (S N)))`` with ``/(Rsqr (INR (fact (S N0))))``.
Rewrite H5; Rewrite div2_double.
Right; Reflexivity.
Unfold Rsqr C Rdiv.
Repeat Rewrite Rinv_Rmult.
Replace (minus (S N) (S N0)) with (S N0).
Rewrite (Rmult_sym (INR (fact (S N)))).
Repeat Rewrite Rmult_assoc.
Rewrite <- Rinv_r_sym.
Rewrite Rmult_1r; Reflexivity.
Apply INR_fact_neq_0.
Replace (S N) with (plus (S N0) (S N0)).
Symmetry; Apply minus_plus.
Rewrite H5; Ring.
Apply INR_fact_neq_0.
Apply INR_fact_neq_0.
Apply INR_fact_neq_0.
Apply INR_fact_neq_0.
Apply INR_eq; Rewrite H4; Do 2 Rewrite S_INR; Do 2 Rewrite mult_INR; Repeat Rewrite S_INR; Ring.
Unfold C Rdiv.
Rewrite (Rmult_sym (INR (fact (S N)))).
Rewrite Rmult_assoc; Rewrite <- Rinv_r_sym.
Rewrite Rmult_1r; Rewrite Rinv_Rmult.
Reflexivity.
Apply INR_fact_neq_0.
Apply INR_fact_neq_0.
Apply INR_fact_neq_0.
Unfold maj_Reste_E.
Unfold Rdiv; Rewrite (Rmult_sym ``4``).
Rewrite Rmult_assoc.
Apply Rle_monotony.
Apply pow_le.
Apply Rle_trans with R1.
Left; Apply Rlt_R0_R1.
Apply RmaxLess1.
Apply Rle_trans with (sum_f_R0 [k:nat]``(INR (minus N k))*/(Rsqr (INR (fact (div2 (S N)))))`` (pred N)).
Apply sum_Rle; Intros.
Rewrite sum_cte.
Replace (S (pred (minus N n))) with (minus N n).
Right; Apply Rmult_sym.
Apply S_pred with O.
Apply simpl_lt_plus_l with n.
Rewrite <- le_plus_minus.
Replace (plus n (0)) with n; [Idtac | Ring].
Apply le_lt_trans with (pred N).
Apply H0.
Apply lt_pred_n_n.
Apply H.
Apply le_trans with (pred N).
Apply H0.
Apply le_pred_n.
Apply Rle_trans with (sum_f_R0 [k:nat]``(INR N)*/(Rsqr (INR (fact (div2 (S N)))))`` (pred N)).
Apply sum_Rle; Intros.
Do 2 Rewrite <- (Rmult_sym ``/(Rsqr (INR (fact (div2 (S N)))))``).
Apply Rle_monotony.
Left; Apply Rlt_Rinv; Apply Rsqr_pos_lt.
Apply INR_fact_neq_0.
Apply le_INR.
Apply simpl_le_plus_l with n.
Rewrite <- le_plus_minus.
Apply le_plus_r.
Apply le_trans with (pred N).
Apply H0.
Apply le_pred_n.
Rewrite sum_cte; Replace (S (pred N)) with N.
Cut (div2 (S N)) = (S (div2 (pred N))).
Intro; Rewrite H0.
Rewrite fact_simpl; Rewrite mult_sym; Rewrite mult_INR; Rewrite Rsqr_times.
Rewrite Rinv_Rmult.
Rewrite (Rmult_sym (INR N)); Repeat Rewrite Rmult_assoc; Apply Rle_monotony.
Left; Apply Rlt_Rinv; Apply Rsqr_pos_lt; Apply INR_fact_neq_0.
Rewrite <- H0.
Cut ``(INR N)<=(INR (mult (S (S O)) (div2 (S N))))``.
Intro; Apply Rle_monotony_contra with ``(Rsqr (INR (div2 (S N))))``.
Apply Rsqr_pos_lt.
Apply not_O_INR; Red; Intro.
Cut (lt (1) (S N)).
Intro; Assert H4 := (div2_not_R0 ? H3).
Rewrite H2 in H4; Elim (lt_n_O ? H4).
Apply lt_n_S; Apply H.
Repeat Rewrite <- Rmult_assoc.
Rewrite <- Rinv_r_sym.
Rewrite Rmult_1l.
Replace ``(INR N)*(INR N)`` with (Rsqr (INR N)); [Idtac | Reflexivity].
Rewrite Rmult_assoc.
Rewrite Rmult_sym.
Replace ``4`` with (Rsqr ``2``); [Idtac | SqRing].
Rewrite <- Rsqr_times.
Apply Rsqr_incr_1.
Replace ``2`` with (INR (2)).
Rewrite <- mult_INR; Apply H1.
Reflexivity.
Left; Apply lt_INR_0; Apply H.
Left; Apply Rmult_lt_pos.
Sup0.
Apply lt_INR_0; Apply div2_not_R0.
Apply lt_n_S; Apply H.
Cut (lt (1) (S N)).
Intro; Unfold Rsqr; Apply prod_neq_R0; Apply not_O_INR; Intro; Assert H4 := (div2_not_R0 ? H2); Rewrite H3 in H4; Elim (lt_n_O ? H4).
Apply lt_n_S; Apply H.
Assert H1 := (even_odd_cor N).
Elim H1; Intros N0 H2.
Elim H2; Intro.
Pattern 2 N; Rewrite H3.
Rewrite div2_S_double.
Right; Rewrite H3; Reflexivity.
Pattern 2 N; Rewrite H3.
Replace (S (S (mult (2) N0))) with (mult (2) (S N0)).
Rewrite div2_double.
Rewrite H3.
Rewrite S_INR; Do 2 Rewrite mult_INR.
Rewrite (S_INR N0).
Rewrite Rmult_Rplus_distr.
Apply Rle_compatibility.
Rewrite Rmult_1r.
Simpl.
Pattern 1 R1; Rewrite <- Rplus_Or; Apply Rle_compatibility; Left; Apply Rlt_R0_R1.
Apply INR_eq; Do 2 Rewrite S_INR; Do 2 Rewrite mult_INR; Repeat Rewrite S_INR; Ring.
Unfold Rsqr; Apply prod_neq_R0; Apply INR_fact_neq_0.
Unfold Rsqr; Apply prod_neq_R0; Apply not_O_INR; Discriminate.
Assert H0 := (even_odd_cor N).
Elim H0; Intros N0 H1.
Elim H1; Intro.
Cut (lt O N0).
Intro; Rewrite H2.
Rewrite div2_S_double.
Replace (mult (2) N0) with (S (S (mult (2) (pred N0)))).
Replace (pred (S (S (mult (2) (pred N0))))) with (S (mult (2) (pred N0))).
Rewrite div2_S_double.
Apply S_pred with O; Apply H3.
Reflexivity.
Replace N0 with (S (pred N0)).
Apply INR_eq; Do 2 Rewrite S_INR; Do 2 Rewrite mult_INR; Repeat Rewrite S_INR; Ring.
Symmetry; Apply S_pred with O; Apply H3.
Rewrite H2 in H.
Apply neq_O_lt.
Red; Intro.
Rewrite <- H3 in H.
Simpl in H.
Elim (lt_n_O ? H).
Rewrite H2.
Replace (pred (S (mult (2) N0))) with (mult (2) N0); [Idtac | Reflexivity].
Replace (S (S (mult (2) N0))) with (mult (2) (S N0)).
Do 2 Rewrite div2_double.
Reflexivity.
Apply INR_eq; Do 2 Rewrite S_INR; Do 2 Rewrite mult_INR; Repeat Rewrite S_INR; Ring.
Apply S_pred with O; Apply H.
Qed.

Lemma maj_Reste_cv_R0 : (x,y:R) (Un_cv (maj_Reste_E x y) ``0``).
Intros; Assert H := (Majxy_cv_R0 x y).
Unfold Un_cv in H; Unfold Un_cv; Intros.
Cut ``0<eps/4``; [Intro | Unfold Rdiv; Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Sup0]].
Elim (H ? H1); Intros N0 H2.
Exists (max (mult (2) (S N0)) (2)); Intros.
Unfold R_dist in H2; Unfold R_dist; Rewrite minus_R0; Unfold Majxy in H2; Unfold maj_Reste_E.
Rewrite Rabsolu_right.
Apply Rle_lt_trans with ``4*(pow (Rmax 1 (Rmax (Rabsolu x) (Rabsolu y))) (mult (S (S (S (S O)))) (S (div2 (pred n)))))/(INR (fact (div2 (pred n))))``.
Apply Rle_monotony.
Left; Sup0.
Unfold Rdiv Rsqr; Rewrite Rinv_Rmult.
Rewrite (Rmult_sym ``(pow (Rmax 1 (Rmax (Rabsolu x) (Rabsolu y))) (mult (S (S O)) n))``); Rewrite (Rmult_sym ``(pow (Rmax 1 (Rmax (Rabsolu x) (Rabsolu y))) (mult (S (S (S (S O)))) (S (div2 (pred n)))))``); Rewrite Rmult_assoc; Apply Rle_monotony.
Left; Apply Rlt_Rinv; Apply INR_fact_lt_0.
Apply Rle_trans with ``(pow (Rmax 1 (Rmax (Rabsolu x) (Rabsolu y))) (mult (S (S O)) n))``.
Rewrite Rmult_sym; Pattern 2 (pow (Rmax R1 (Rmax (Rabsolu x) (Rabsolu y))) (mult (2) n)); Rewrite <- Rmult_1r; Apply Rle_monotony.
Apply pow_le; Apply Rle_trans with R1.
Left; Apply Rlt_R0_R1.
Apply RmaxLess1.
Apply Rle_monotony_contra with ``(INR (fact (div2 (pred n))))``.
Apply INR_fact_lt_0.
Rewrite Rmult_1r; Rewrite <- Rinv_r_sym.
Replace R1 with (INR (1)); [Apply le_INR | Reflexivity].
Apply lt_le_S.
Apply INR_lt.
Apply INR_fact_lt_0.
Apply INR_fact_neq_0.
Apply Rle_pow.
Apply RmaxLess1.
Assert H4 := (even_odd_cor n).
Elim H4; Intros N1 H5.
Elim H5; Intro.
Cut (lt O N1).
Intro.
Rewrite H6.
Replace (pred (mult (2) N1)) with (S (mult (2) (pred N1))).
Rewrite div2_S_double.
Replace (S (pred N1)) with N1.
Apply INR_le.
Right.
Do 3 Rewrite mult_INR; Repeat Rewrite S_INR; Ring.
Apply S_pred with O; Apply H7.
Replace (mult (2) N1) with (S (S (mult (2) (pred N1)))).
Reflexivity.
Pattern 2 N1; Replace N1 with (S (pred N1)).
Apply INR_eq; Do 2 Rewrite S_INR; Do 2 Rewrite mult_INR; Repeat Rewrite S_INR; Ring.
Symmetry ; Apply S_pred with O; Apply H7.
Apply INR_lt.
Apply Rlt_monotony_contra with (INR (2)).
Simpl; Sup0.
Rewrite Rmult_Or; Rewrite <- mult_INR.
Apply lt_INR_0.
Rewrite <- H6.
Apply lt_le_trans with (2).
Apply lt_O_Sn.
Apply le_trans with (max (mult (2) (S N0)) (2)).
Apply le_max_r.
Apply H3.
Rewrite H6.
Replace (pred (S (mult (2) N1))) with (mult (2) N1).
Rewrite div2_double.
Replace (mult (4) (S N1)) with (mult (2) (mult (2) (S N1))).
Apply mult_le.
Replace (mult (2) (S N1)) with (S (S (mult (2) N1))).
Apply le_n_Sn.
Apply INR_eq; Do 2 Rewrite S_INR; Do 2 Rewrite mult_INR; Repeat Rewrite S_INR; Ring.
Ring.
Reflexivity.
Apply INR_fact_neq_0.
Apply INR_fact_neq_0.
Apply Rlt_monotony_contra with ``/4``.
Apply Rlt_Rinv; Sup0.
Rewrite <- Rmult_assoc; Rewrite <- Rinv_l_sym.
Rewrite Rmult_1l; Rewrite Rmult_sym.
Replace ``(pow (Rmax 1 (Rmax (Rabsolu x) (Rabsolu y))) (mult (S (S (S (S O)))) (S (div2 (pred n)))))/(INR (fact (div2 (pred n))))`` with ``(Rabsolu ((pow (Rmax 1 (Rmax (Rabsolu x) (Rabsolu y))) (mult (S (S (S (S O)))) (S (div2 (pred n)))))/(INR (fact (div2 (pred n))))-0))``.
Apply H2; Unfold ge.
Cut (le (mult (2) (S N0)) n).
Intro; Apply le_S_n.
Apply INR_le; Apply Rle_monotony_contra with (INR (2)).
Simpl; Sup0.
Do 2 Rewrite <- mult_INR; Apply le_INR.
Apply le_trans with n.
Apply H4.
Assert H5 := (even_odd_cor n).
Elim H5; Intros N1 H6.
Elim H6; Intro.
Cut (lt O N1).
Intro.
Rewrite H7.
Apply mult_le.
Replace (pred (mult (2) N1)) with (S (mult (2) (pred N1))).
Rewrite div2_S_double.
Replace (S (pred N1)) with N1.
Apply le_n.
Apply S_pred with O; Apply H8.
Replace (mult (2) N1) with (S (S (mult (2) (pred N1)))).
Reflexivity.
Pattern 2 N1; Replace N1 with (S (pred N1)).
Apply INR_eq; Do 2 Rewrite S_INR; Do 2 Rewrite mult_INR; Repeat Rewrite S_INR; Ring.
Symmetry; Apply S_pred with O; Apply H8.
Apply INR_lt.
Apply Rlt_monotony_contra with (INR (2)).
Simpl; Sup0.
Rewrite Rmult_Or; Rewrite <- mult_INR.
Apply lt_INR_0.
Rewrite <- H7.
Apply lt_le_trans with (2).
Apply lt_O_Sn.
Apply le_trans with (max (mult (2) (S N0)) (2)).
Apply le_max_r.
Apply H3.
Rewrite H7.
Replace (pred (S (mult (2) N1))) with (mult (2) N1).
Rewrite div2_double.
Replace (mult (2) (S N1)) with (S (S (mult (2) N1))).
Apply le_n_Sn.
Apply INR_eq; Do 2 Rewrite S_INR; Do 2 Rewrite mult_INR; Repeat Rewrite S_INR; Ring.
Reflexivity.
Apply le_trans with (max (mult (2) (S N0)) (2)).
Apply le_max_l.
Apply H3.
Rewrite minus_R0; Apply Rabsolu_right.
Apply Rle_sym1.
Unfold Rdiv; Repeat Apply Rmult_le_pos.
Apply pow_le.
Apply Rle_trans with R1.
Left; Apply Rlt_R0_R1.
Apply RmaxLess1.
Left; Apply Rlt_Rinv; Apply INR_fact_lt_0.
DiscrR.
Apply Rle_sym1.
Unfold Rdiv; Apply Rmult_le_pos.
Left; Sup0.
Apply Rmult_le_pos.
Apply pow_le.
Apply Rle_trans with R1.
Left; Apply Rlt_R0_R1.
Apply RmaxLess1.
Left; Apply Rlt_Rinv; Apply Rsqr_pos_lt; Apply INR_fact_neq_0.
Qed.

(**********)
Lemma Reste_E_cv : (x,y:R) (Un_cv (Reste_E x y) R0).
Intros; Assert H := (maj_Reste_cv_R0 x y).
Unfold Un_cv in H; Unfold Un_cv; Intros; Elim (H ? H0); Intros.
Exists (max x0 (1)); Intros.
Unfold R_dist; Rewrite minus_R0.
Apply Rle_lt_trans with (maj_Reste_E x y n).
Apply Reste_E_maj.
Apply lt_le_trans with (1).
Apply lt_O_Sn.
Apply le_trans with (max x0 (1)).
Apply le_max_r.
Apply H2.
Replace (maj_Reste_E x y n) with (R_dist (maj_Reste_E x y n) R0).
Apply H1.
Unfold ge; Apply le_trans with (max x0 (1)).
Apply le_max_l.
Apply H2.
Unfold R_dist; Rewrite minus_R0; Apply Rabsolu_right.
Apply Rle_sym1; Apply Rle_trans with (Rabsolu (Reste_E x y n)).
Apply Rabsolu_pos.
Apply Reste_E_maj.
Apply lt_le_trans with (1).
Apply lt_O_Sn.
Apply le_trans with (max x0 (1)).
Apply le_max_r.
Apply H2.
Qed.

(**********)
Lemma exp_plus : (x,y:R) ``(exp (x+y))==(exp x)*(exp y)``.
Intros; Assert H0 := (E1_cvg x).
Assert H := (E1_cvg y).
Assert H1 := (E1_cvg ``x+y``).
EApply UL_sequence.
Apply H1.
Assert H2 := (CV_mult ? ? ? ? H0 H).
Assert H3 := (CV_minus ? ? ? ? H2 (Reste_E_cv x y)).
Unfold Un_cv; Unfold Un_cv in H3; Intros.
Elim (H3 ? H4); Intros.
Exists (S x0); Intros.
Rewrite <- (exp_form x y n).
Rewrite minus_R0 in H5.
Apply H5.
Unfold ge; Apply le_trans with (S x0).
Apply le_n_Sn.
Apply H6.
Apply lt_le_trans with (S x0).
Apply lt_O_Sn.
Apply H6.
Qed.

(**********)
Lemma exp_pos_pos : (x:R) ``0<x`` -> ``0<(exp x)``.
Intros; Pose An := [N:nat]``/(INR (fact N))*(pow x N)``.
Cut (Un_cv [n:nat](sum_f_R0 An n) (exp x)).
Intro; Apply Rlt_le_trans with (sum_f_R0 An O).
Unfold An; Simpl; Rewrite Rinv_R1; Rewrite Rmult_1r; Apply Rlt_R0_R1.
Apply sum_incr.
Assumption.
Intro; Unfold An; Left; Apply Rmult_lt_pos.
Apply Rlt_Rinv; Apply INR_fact_lt_0.
Apply (pow_lt ? n H).
Unfold exp; Unfold projT1; Case (exist_exp x); Intro.
Unfold exp_in; Unfold infinit_sum Un_cv; Trivial.
Qed.

(**********)
Lemma exp_pos : (x:R) ``0<(exp x)``.
Intro; Case (total_order_T R0 x); Intro.
Elim s; Intro.
Apply (exp_pos_pos ? a).
Rewrite <- b; Rewrite exp_0; Apply Rlt_R0_R1.
Replace (exp x) with ``1/(exp (-x))``.
Unfold Rdiv; Apply Rmult_lt_pos.
Apply Rlt_R0_R1.
Apply Rlt_Rinv; Apply exp_pos_pos.
Apply (Rgt_RO_Ropp ? r).
Cut ``(exp (-x))<>0``.
Intro; Unfold Rdiv; Apply r_Rmult_mult with ``(exp (-x))``.
Rewrite Rmult_1l; Rewrite <- Rinv_r_sym.
Rewrite <- exp_plus.
Rewrite Rplus_Ropp_l; Rewrite exp_0; Reflexivity.
Apply H.
Apply H.
Assert H := (exp_plus x ``-x``).
Rewrite Rplus_Ropp_r in H; Rewrite exp_0 in H.
Red; Intro; Rewrite H0 in H.
Rewrite Rmult_Or in H.
Elim R1_neq_R0; Assumption.
Qed.

(* ((exp h)-1)/h -> 0 quand h->0 *)
Lemma derivable_pt_lim_exp_0 : (derivable_pt_lim exp ``0`` ``1``).
Unfold derivable_pt_lim; Intros.
Pose fn := [N:nat][x:R]``(pow x N)/(INR (fact (S N)))``.
Cut (CVN_R fn).
Intro; Cut (x:R)(sigTT ? [l:R](Un_cv [N:nat](SP fn N x) l)).
Intro cv; Cut ((n:nat)(continuity (fn n))).
Intro; Cut (continuity (SFL fn cv)).
Intro; Unfold continuity in H1.
Assert H2 := (H1 R0).
Unfold continuity_pt in H2; Unfold continue_in in H2; Unfold limit1_in in H2; Unfold limit_in in H2; Simpl in H2; Unfold R_dist in H2.
Elim (H2 ? H); Intros alp H3.
Elim H3; Intros.
Exists (mkposreal ? H4); Intros.
Rewrite Rplus_Ol; Rewrite exp_0.
Replace ``((exp h)-1)/h`` with (SFL fn cv h).
Replace R1 with (SFL fn cv R0).
Apply H5.
Split.
Unfold D_x no_cond; Split.
Trivial.
Apply (not_sym ? ? H6).
Rewrite minus_R0; Apply H7.
Unfold SFL.
Case (cv ``0``); Intros.
EApply UL_sequence.
Apply u.
Unfold Un_cv SP.
Intros; Exists (1); Intros.
Unfold R_dist; Rewrite decomp_sum.
Rewrite (Rplus_sym (fn O R0)).
Replace (fn O R0) with R1.
Unfold Rminus; Rewrite Rplus_assoc; Rewrite Rplus_Ropp_r; Rewrite Rplus_Or.
Replace (sum_f_R0 [i:nat](fn (S i) ``0``) (pred n)) with R0.
Rewrite Rabsolu_R0; Apply H8.
Symmetry; Apply sum_eq_R0; Intros.
Unfold fn.
Simpl.
Unfold Rdiv; Do 2 Rewrite Rmult_Ol; Reflexivity.
Unfold fn; Simpl.
Unfold Rdiv; Rewrite Rinv_R1; Rewrite Rmult_1r; Reflexivity.
Apply lt_le_trans with (1); [Apply lt_n_Sn | Apply H9].
Unfold SFL exp.
Unfold projT1.
Case (cv h); Case (exist_exp h); Intros.
EApply UL_sequence.
Apply u.
Unfold Un_cv; Intros.
Unfold exp_in in e.
Unfold infinit_sum in e.
Cut ``0<eps0*(Rabsolu h)``.
Intro; Elim (e ? H9); Intros N0 H10.
Exists N0; Intros.
Unfold R_dist.
Apply Rlt_monotony_contra with ``(Rabsolu h)``.
Apply Rabsolu_pos_lt; Assumption.
Rewrite <- Rabsolu_mult.
Rewrite Rminus_distr.
Replace ``h*(x-1)/h`` with ``(x-1)``.
Unfold R_dist in H10.
Replace ``h*(SP fn n h)-(x-1)`` with (Rminus (sum_f_R0 [i:nat]``/(INR (fact i))*(pow h i)`` (S n)) x).
Rewrite (Rmult_sym (Rabsolu h)).
Apply H10.
Unfold ge.
Apply le_trans with (S N0).
Apply le_n_Sn.
Apply le_n_S; Apply H11.
Rewrite decomp_sum.
Replace ``/(INR (fact O))*(pow h O)`` with R1.
Unfold Rminus.
Rewrite Ropp_distr1.
Rewrite Ropp_Ropp.
Rewrite <- (Rplus_sym ``-x``).
Rewrite <- (Rplus_sym ``-x+1``).
Rewrite Rplus_assoc; Repeat Apply Rplus_plus_r.
Replace (pred (S n)) with n; [Idtac | Reflexivity].
Unfold SP.
Rewrite scal_sum.
Apply sum_eq; Intros.
Unfold fn.
Replace (pow h (S i)) with ``h*(pow h i)``.
Unfold Rdiv; Ring.
Simpl; Ring.
Simpl; Rewrite Rinv_R1; Rewrite Rmult_1r; Reflexivity.
Apply lt_O_Sn.
Unfold Rdiv.
Rewrite <- Rmult_assoc.
Symmetry; Apply Rinv_r_simpl_m.
Assumption.
Apply Rmult_lt_pos.
Apply H8.
Apply Rabsolu_pos_lt; Assumption.
Apply SFL_continuity; Assumption.
Intro; Unfold fn.
Replace [x:R]``(pow x n)/(INR (fact (S n)))`` with (div_fct (pow_fct n) (fct_cte (INR (fact (S n))))); [Idtac | Reflexivity].
Apply continuity_div.
Apply derivable_continuous; Apply (derivable_pow n).
Apply derivable_continuous; Apply derivable_const.
Intro; Unfold fct_cte; Apply INR_fact_neq_0.
Apply (CVN_R_CVS ? X).
Assert H0 := Alembert_exp.
Unfold CVN_R.
Intro; Unfold CVN_r.
Apply Specif.existT with [N:nat]``(pow r N)/(INR (fact (S N)))``.
Cut (SigT ? [l:R](Un_cv [n:nat](sum_f_R0 [k:nat](Rabsolu ``(pow r k)/(INR (fact (S k)))``) n) l)).
Intro.
Elim X; Intros.
Exists x; Intros.
Split.
Apply p.
Unfold Boule; Intros.
Rewrite minus_R0 in H1.
Unfold fn.
Unfold Rdiv; Rewrite Rabsolu_mult.
Cut ``0<(INR (fact (S n)))``.
Intro.
Rewrite (Rabsolu_right ``/(INR (fact (S n)))``).
Do 2 Rewrite <- (Rmult_sym ``/(INR (fact (S n)))``).
Apply Rle_monotony.
Left; Apply Rlt_Rinv; Apply H2.
Rewrite <- Pow_Rabsolu.
Apply pow_maj_Rabs.
Rewrite Rabsolu_Rabsolu; Left; Apply H1.
Apply Rle_sym1; Left; Apply Rlt_Rinv; Apply H2.
Apply INR_fact_lt_0.
Cut (r::R)<>``0``.
Intro; Apply Alembert_C2.
Intro; Apply Rabsolu_no_R0.
Unfold Rdiv; Apply prod_neq_R0.
Apply pow_nonzero; Assumption.
Apply Rinv_neq_R0; Apply INR_fact_neq_0.
Unfold Un_cv in H0.
Unfold Un_cv; Intros.
Cut ``0<eps0/r``; [Intro | Unfold Rdiv; Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Apply (cond_pos r)]].
Elim (H0 ? H3); Intros N0 H4.
Exists N0; Intros.
Cut (ge (S n) N0).
Intro hyp_sn.
Assert H6 := (H4 ? hyp_sn).
Unfold R_dist in H6; Rewrite minus_R0 in H6.
Rewrite Rabsolu_Rabsolu in H6.
Unfold R_dist; Rewrite minus_R0.
Rewrite Rabsolu_Rabsolu.
Replace ``(Rabsolu ((pow r (S n))/(INR (fact (S (S n))))))/
     (Rabsolu ((pow r n)/(INR (fact (S n)))))`` with ``r*/(INR (fact (S (S n))))*//(INR (fact (S n)))``.
Rewrite Rmult_assoc; Rewrite Rabsolu_mult.
Rewrite (Rabsolu_right r).
Apply Rlt_monotony_contra with ``/r``.
Apply Rlt_Rinv; Apply (cond_pos r).
Rewrite <- Rmult_assoc; Rewrite <- Rinv_l_sym.
Rewrite Rmult_1l; Rewrite <- (Rmult_sym eps0).
Apply H6.
Assumption.
Apply Rle_sym1; Left; Apply (cond_pos r).
Unfold Rdiv.
Repeat Rewrite Rabsolu_mult.
Repeat Rewrite Rabsolu_Rinv.
Rewrite Rinv_Rmult.
Repeat Rewrite Rabsolu_right.
Rewrite Rinv_Rinv.
Rewrite (Rmult_sym r).
Rewrite (Rmult_sym (pow r (S n))).
Repeat Rewrite Rmult_assoc.
Apply Rmult_mult_r.
Rewrite (Rmult_sym r).
Rewrite <- Rmult_assoc; Rewrite <- (Rmult_sym (INR (fact (S n)))).
Apply Rmult_mult_r.
Simpl.
Rewrite Rmult_assoc; Rewrite <- Rinv_r_sym.
Ring.
Apply pow_nonzero; Assumption.
Apply INR_fact_neq_0.
Apply Rle_sym1; Left; Apply INR_fact_lt_0.
Apply Rle_sym1; Left; Apply pow_lt; Apply (cond_pos r).
Apply Rle_sym1; Left; Apply INR_fact_lt_0.
Apply Rle_sym1; Left; Apply pow_lt; Apply (cond_pos r).
Apply Rabsolu_no_R0; Apply pow_nonzero; Assumption.
Apply Rinv_neq_R0; Apply Rabsolu_no_R0; Apply INR_fact_neq_0.
Apply INR_fact_neq_0.
Apply INR_fact_neq_0.
Unfold ge; Apply le_trans with n.
Apply H5.
Apply le_n_Sn.
Assert H1 := (cond_pos r); Red; Intro; Rewrite H2 in H1; Elim (Rlt_antirefl ? H1).
Qed.

(**********)
Lemma derivable_pt_lim_exp : (x:R) (derivable_pt_lim exp x (exp x)).
Intro; Assert H0 := derivable_pt_lim_exp_0.
Unfold derivable_pt_lim in H0; Unfold derivable_pt_lim; Intros.
Cut ``0<eps/(exp x)``; [Intro | Unfold Rdiv; Apply Rmult_lt_pos; [Apply H | Apply Rlt_Rinv; Apply exp_pos]].
Elim (H0 ? H1); Intros del H2.
Exists del; Intros.
Assert H5 := (H2 ? H3 H4).
Rewrite Rplus_Ol in H5; Rewrite exp_0 in H5.
Replace ``((exp (x+h))-(exp x))/h-(exp x)`` with ``(exp x)*(((exp h)-1)/h-1)``.
Rewrite Rabsolu_mult; Rewrite (Rabsolu_right (exp x)).
Apply Rlt_monotony_contra with ``/(exp x)``.
Apply Rlt_Rinv; Apply exp_pos.
Rewrite <- Rmult_assoc; Rewrite <- Rinv_l_sym.
Rewrite Rmult_1l; Rewrite <- (Rmult_sym eps).
Apply H5.
Assert H6 := (exp_pos x); Red; Intro; Rewrite H7 in H6; Elim (Rlt_antirefl ? H6).
Apply Rle_sym1; Left; Apply exp_pos.
Rewrite Rminus_distr.
Rewrite Rmult_1r; Unfold Rdiv; Rewrite <- Rmult_assoc; Rewrite Rminus_distr.
Rewrite Rmult_1r; Rewrite exp_plus; Reflexivity.
Qed.
