(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)
 
(*i $Id$ i*)

Require DiscrR.
Require Rbase.
Require Rseries.
Require Binome.
Require Rcomplet.
Require Rtrigo_def.

(*****************************************************************)
(* Using series definitions of cos and sin                       *)
(*****************************************************************)

Definition sin_term [a:R] : nat->R := [i:nat] ``(pow (-1) i)*(pow a (plus (mult (S (S O)) i) (S O)))/(INR (fact (plus (mult (S (S O)) i) (S O))))``.

Definition cos_term [a:R] : nat->R := [i:nat] ``(pow (-1) i)*(pow a (mult (S (S O)) i))/(INR (fact (mult (S (S O)) i)))``.

Definition sin_approx [a:R;n:nat] : R := (sum_f_R0 (sin_term a) n).

Definition cos_approx [a:R;n:nat] : R := (sum_f_R0 (cos_term a) n).

(**********)
Lemma PI_4 : ``PI<=4``.
Assert H0 := (PI_ineq O).
Elim H0; Clear H0; Intros _ H0.
Unfold tg_alt PI_tg in H0; Simpl in H0.
Rewrite Rinv_R1 in H0; Rewrite Rmult_1r in H0; Unfold Rdiv in H0.
Apply Rle_monotony_contra with ``/4``.
Apply Rlt_Rinv; Sup0.
Rewrite <- Rinv_l_sym; [Rewrite Rmult_sym; Assumption | DiscrR].
Qed.

(* Un -> +oo *)
Definition cv_infty [Un:nat->R] : Prop := (M:R)(EXT N:nat | (n:nat) (le N n) -> ``M<(Un n)``).

(* Un -> +oo => /Un -> O *)
Lemma cv_infty_cv_R0 : (Un:nat->R) ((n:nat)``(Un n)<>0``) -> (cv_infty Un) -> (Un_cv [n:nat]``/(Un n)`` R0).
Unfold cv_infty Un_cv; Unfold R_dist; Intros.
Elim (H0 ``/eps``); Intros N0 H2.
Exists N0; Intros.
Unfold Rminus; Rewrite Ropp_O; Rewrite Rplus_Or; Rewrite (Rabsolu_Rinv ? (H n)).
Apply Rlt_monotony_contra with (Rabsolu (Un n)).
Apply Rabsolu_pos_lt; Apply H.
Rewrite <- Rinv_r_sym.
Apply Rlt_monotony_contra with ``/eps``.
Apply Rlt_Rinv; Assumption.
Rewrite Rmult_1r; Rewrite (Rmult_sym ``/eps``); Rewrite Rmult_assoc; Rewrite <- Rinv_r_sym.
Rewrite Rmult_1r; Apply Rlt_le_trans with (Un n).
Apply H2; Assumption.
Apply Rle_Rabsolu.
Red; Intro; Rewrite H4 in H1; Elim (Rlt_antirefl ? H1).
Apply Rabsolu_no_R0; Apply H.
Qed.

(**********)
Lemma sum_eq_R0 : (An:nat->R;N:nat) ((n:nat)(le n N)->``(An n)==0``) -> (sum_f_R0 An N)==R0.
Intros; Induction N.
Simpl; Apply H; Apply le_n.
Rewrite tech5; Rewrite HrecN; [Rewrite Rplus_Ol; Apply H; Apply le_n | Intros; Apply H; Apply le_trans with N; [Assumption | Apply le_n_Sn]].
Qed.

(**********)
Lemma decreasing_prop : (Un:nat->R;m,n:nat) (Un_decreasing Un) -> (le m n) -> ``(Un n)<=(Un m)``.
Unfold Un_decreasing; Intros.
Induction n.
Induction m.
Right; Reflexivity.
Elim (le_Sn_O ? H0).
Cut (le m n)\/m=(S n).
Intro; Elim H1; Intro.
Apply Rle_trans with (Un n).
Apply H.
Apply Hrecn; Assumption.
Rewrite H2; Right; Reflexivity.
Inversion H0; [Right; Reflexivity | Left; Assumption].
Qed.

(* |x|^n/n! -> 0 *)
Lemma cv_speed_pow_fact : (x:R) (Un_cv [n:nat]``(pow x n)/(INR (fact n))`` R0).
Intro; Cut (Un_cv [n:nat]``(pow (Rabsolu x) n)/(INR (fact n))`` R0) -> (Un_cv [n:nat]``(pow x n)/(INR (fact n))`` ``0``).
Intro; Apply H.
Unfold Un_cv; Unfold R_dist; Intros; Case (Req_EM x R0); Intro.
Exists (S O); Intros.
Rewrite H1; Unfold Rminus; Rewrite Ropp_O; Rewrite Rplus_Or; Rewrite Rabsolu_R0; Rewrite pow_ne_zero; [Unfold Rdiv; Rewrite Rmult_Ol; Rewrite Rabsolu_R0; Assumption | Red; Intro; Rewrite H3 in H2; Elim (le_Sn_n ? H2)].
Assert H2 := (Rabsolu_pos_lt x H1); Pose M := (up (Rabsolu x)); Cut `0<=M`.
Intro; Elim (IZN M H3); Intros M_nat H4.
Pose Un := [n:nat]``(pow (Rabsolu x) (plus M_nat n))/(INR (fact (plus M_nat n)))``.
Cut (Un_cv Un R0); Unfold Un_cv; Unfold R_dist; Intros.
Elim (H5 eps H0); Intros N H6.
Exists (plus M_nat N); Intros; Cut (EX p:nat | (ge p N)/\n=(plus M_nat p)).
Intro; Elim H8; Intros p H9.
Elim H9; Intros; Rewrite H11; Unfold Un in H6; Apply H6; Assumption.
Exists (minus n M_nat).
Split.
Unfold ge; Apply simpl_le_plus_l with M_nat; Rewrite <- le_plus_minus.
Assumption.
Apply le_trans with (plus M_nat N).
Apply le_plus_l.
Assumption.
Apply le_plus_minus; Apply le_trans with (plus M_nat N); [Apply le_plus_l | Assumption].
Pose Vn := [n:nat]``(Rabsolu x)*(Un O)/(INR (S n))``.
Cut (le (1) M_nat).
Intro; Cut (n:nat)``0<(Un n)``.
Intro; Cut (Un_decreasing Un).
Intro; Cut (n:nat)``(Un (S n))<=(Vn n)``.
Intro; Cut (Un_cv Vn R0).
Unfold Un_cv; Unfold R_dist; Intros.
Elim (H10 eps0 H5); Intros N1 H11.
Exists (S N1); Intros.
Cut (n:nat)``0<(Vn n)``.
Intro; Apply Rle_lt_trans with ``(Rabsolu ((Vn (pred n))-0))``.
Repeat Rewrite Rabsolu_right.
Unfold Rminus; Rewrite Ropp_O; Do 2 Rewrite Rplus_Or; Replace n with (S (pred n)).
Apply H9.
Inversion H12; Simpl; Reflexivity.
Apply Rle_sym1; Unfold Rminus; Rewrite Ropp_O; Rewrite Rplus_Or; Left; Apply H13.
Apply Rle_sym1; Unfold Rminus; Rewrite Ropp_O; Rewrite Rplus_Or; Left; Apply H7.
Apply H11; Unfold ge; Apply le_S_n; Replace (S (pred n)) with n; [Unfold ge in H12; Exact H12 | Inversion H12; Simpl; Reflexivity].
Intro; Apply Rlt_le_trans with (Un (S n0)); [Apply H7 | Apply H9].
Cut (cv_infty [n:nat](INR (S n))).
Intro; Cut (Un_cv [n:nat]``/(INR (S n))`` R0).
Unfold Un_cv R_dist; Intros; Unfold Vn.
Cut ``0<eps1/((Rabsolu x)*(Un O))``.
Intro; Elim (H11 ? H13); Intros N H14.
Exists N; Intros; Replace ``(Rabsolu x)*(Un O)/(INR (S n))-0`` with ``((Rabsolu x)*(Un O))*(/(INR (S n))-0)``; [Idtac | Unfold Rdiv; Ring].
Rewrite Rabsolu_mult; Apply Rlt_monotony_contra with ``/(Rabsolu ((Rabsolu x)*(Un O)))``.
Apply Rlt_Rinv; Apply Rabsolu_pos_lt.
Apply prod_neq_R0.
Apply Rabsolu_no_R0; Assumption.
Assert H16 := (H7 O); Red; Intro; Rewrite H17 in H16; Elim (Rlt_antirefl ? H16).
Rewrite <- Rmult_assoc; Rewrite <- Rinv_l_sym.
Rewrite Rmult_1l.
Replace ``/(Rabsolu ((Rabsolu x)*(Un O)))*eps1`` with ``eps1/((Rabsolu x)*(Un O))``.
Apply H14; Assumption.
Unfold Rdiv; Rewrite (Rabsolu_right ``(Rabsolu x)*(Un O)``).
Apply Rmult_sym.
Apply Rle_sym1; Apply Rmult_le_pos.
Apply Rabsolu_pos.
Left; Apply H7.
Apply Rabsolu_no_R0.
Apply prod_neq_R0; [Apply Rabsolu_no_R0; Assumption | Assert H16 := (H7 O); Red; Intro; Rewrite H17 in H16; Elim (Rlt_antirefl ? H16)].
Unfold Rdiv; Apply Rmult_lt_pos.
Assumption.
Apply Rlt_Rinv; Apply Rmult_lt_pos.
Apply Rabsolu_pos_lt; Assumption.
Apply H7.
Apply (cv_infty_cv_R0 [n:nat]``(INR (S n))``).
Intro; Apply not_O_INR; Discriminate.
Assumption.
Unfold cv_infty; Intro; Case (total_order_T M0 R0); Intro.
Elim s; Intro.
Exists O; Intros.
Apply Rlt_trans with R0; [Assumption | Apply lt_INR_0; Apply lt_O_Sn].
Exists O; Intros; Rewrite b; Apply lt_INR_0; Apply lt_O_Sn.
Pose M0_z := (up M0).
Assert H10 := (archimed M0).
Cut `0<=M0_z`.
Intro; Elim (IZN ? H11); Intros M0_nat H12.
Exists M0_nat; Intros.
Apply Rlt_le_trans with (IZR M0_z).
Elim H10; Intros; Assumption.
Rewrite H12; Rewrite <- INR_IZR_INZ; Apply le_INR.
Apply le_trans with n; [Assumption | Apply le_n_Sn].
Apply le_IZR; Left; Simpl; Unfold M0_z; Apply Rlt_trans with M0; [Assumption | Elim H10; Intros; Assumption].
Intro; Apply Rle_trans with ``(Rabsolu x)*(Un n)*/(INR (S n))``.
Unfold Un; Replace (plus M_nat (S n)) with (plus (plus M_nat n) (1)).
Rewrite pow_add; Replace (pow (Rabsolu x) (S O)) with (Rabsolu x); [Idtac | Simpl; Ring].
Unfold Rdiv; Rewrite <- (Rmult_sym (Rabsolu x)); Repeat Rewrite Rmult_assoc; Repeat Apply Rle_monotony.
Apply Rabsolu_pos.
Left; Apply pow_lt; Assumption.
Replace (plus (plus M_nat n) (S O)) with (S (plus M_nat n)).
Rewrite fact_simpl; Rewrite mult_sym; Rewrite mult_INR; Rewrite Rinv_Rmult.
Apply Rle_monotony.
Left; Apply Rlt_Rinv; Apply lt_INR_0; Apply neq_O_lt; Red; Intro; Assert H10 := (sym_eq ? ? ? H9); Elim (fact_neq_0 ? H10).
Left; Apply Rinv_lt.
Apply Rmult_lt_pos; Apply lt_INR_0; Apply lt_O_Sn.
Apply lt_INR; Apply lt_n_S.
Pattern 1 n; Replace n with (plus O n); [Idtac | Reflexivity].
Apply lt_reg_r.
Apply lt_le_trans with (S O); [Apply lt_O_Sn | Assumption].
Apply INR_fact_neq_0.
Apply not_O_INR; Discriminate.
Apply INR_eq; Rewrite S_INR; Do 3 Rewrite plus_INR; Reflexivity.
Apply INR_eq; Do 3 Rewrite plus_INR; Do 2 Rewrite S_INR; Ring.
Unfold Vn; Rewrite Rmult_assoc; Unfold Rdiv; Rewrite (Rmult_sym (Un O)); Rewrite (Rmult_sym (Un n)).
Repeat Apply Rle_monotony.
Apply Rabsolu_pos.
Left; Apply Rlt_Rinv; Apply lt_INR_0; Apply lt_O_Sn.
Apply decreasing_prop; [Assumption | Apply le_O_n].
Unfold Un_decreasing; Intro; Unfold Un.
Replace (plus M_nat (S n)) with (plus (plus M_nat n) (1)).
Rewrite pow_add; Unfold Rdiv; Rewrite Rmult_assoc; Apply Rle_monotony.
Left; Apply pow_lt; Assumption.
Replace (pow (Rabsolu x) (S O)) with (Rabsolu x); [Idtac | Simpl; Ring].
Replace (plus (plus M_nat n) (S O)) with (S (plus M_nat n)).
Apply Rle_monotony_contra with (INR (fact (S (plus M_nat n)))).
Apply lt_INR_0; Apply neq_O_lt; Red; Intro; Assert H9 := (sym_eq ? ? ? H8); Elim (fact_neq_0 ? H9).
Rewrite (Rmult_sym (Rabsolu x)); Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym.
Rewrite Rmult_1l.
Rewrite fact_simpl; Rewrite mult_INR; Rewrite Rmult_assoc; Rewrite <- Rinv_r_sym.
Rewrite Rmult_1r; Apply Rle_trans with (INR M_nat).
Left; Rewrite INR_IZR_INZ.
Rewrite <- H4; Assert H8 := (archimed (Rabsolu x)); Elim H8; Intros; Assumption.
Apply le_INR; Apply le_trans with (S M_nat); [Apply le_n_Sn | Apply le_n_S; Apply le_plus_l].
Apply INR_fact_neq_0.
Apply INR_fact_neq_0.
Apply INR_eq; Rewrite S_INR; Do 3 Rewrite plus_INR; Reflexivity.
Apply INR_eq; Do 3 Rewrite plus_INR; Do 2 Rewrite S_INR; Ring.
Intro; Unfold Un; Unfold Rdiv; Apply Rmult_lt_pos.
Apply pow_lt; Assumption.
Apply Rlt_Rinv; Apply lt_INR_0; Apply neq_O_lt; Red; Intro; Assert H8 := (sym_eq ? ? ? H7); Elim (fact_neq_0 ? H8).
Clear Un Vn; Apply INR_le; Simpl.
Induction M_nat.
Assert H6 := (archimed (Rabsolu x)); Fold M in H6; Elim H6; Intros. 
Rewrite H4 in H7; Rewrite <- INR_IZR_INZ in H7.
Simpl in H7; Elim (Rlt_antirefl ? (Rlt_trans ? ? ? H2 H7)).
Replace R1 with (INR (S O)); [Apply le_INR | Reflexivity]; Apply le_n_S; Apply le_O_n.
Apply le_IZR; Simpl; Left; Apply Rlt_trans with (Rabsolu x).
Assumption.
Elim (archimed (Rabsolu x)); Intros; Assumption.
Unfold Un_cv; Unfold R_dist; Intros; Elim (H eps H0); Intros.
Exists x0; Intros; Apply Rle_lt_trans with ``(Rabsolu ((pow (Rabsolu x) n)/(INR (fact n))-0))``.
Unfold Rminus; Rewrite Ropp_O; Do 2 Rewrite Rplus_Or; Rewrite (Rabsolu_right ``(pow (Rabsolu x) n)/(INR (fact n))``).
Unfold Rdiv; Rewrite Rabsolu_mult; Rewrite (Rabsolu_right ``/(INR (fact n))``).
Rewrite Pow_Rabsolu; Right; Reflexivity.
Apply Rle_sym1; Left; Apply Rlt_Rinv; Apply lt_INR_0; Apply neq_O_lt; Red; Intro; Assert H4 := (sym_eq ? ? ? H3); Elim (fact_neq_0 ? H4).
Apply Rle_sym1; Unfold Rdiv; Apply Rmult_le_pos.
Case (Req_EM x R0); Intro.
Rewrite H3; Rewrite Rabsolu_R0.
Induction n; [Simpl; Left; Apply Rlt_R0_R1 | Simpl; Rewrite Rmult_Ol; Right; Reflexivity].
Left; Apply pow_lt; Apply Rabsolu_pos_lt; Assumption.
Left; Apply Rlt_Rinv; Apply lt_INR_0; Apply neq_O_lt; Red; Intro; Assert H4 := (sym_eq ? ? ? H3); Elim (fact_neq_0 ? H4).
Apply H1; Assumption.
Qed.

Lemma pow_Rsqr : (x:R;n:nat) (pow x (mult (2) n))==(pow (Rsqr x) n).
Intros; Induction n.
Reflexivity.
Replace (mult (2) (S n)) with (S (S (mult (2) n))).
Replace (pow x (S (S (mult (2) n)))) with ``x*x*(pow x (mult (S (S O)) n))``.
Rewrite Hrecn; Reflexivity.
Simpl; Ring.
Apply INR_eq; Do 2 Rewrite S_INR; Do 2 Rewrite mult_INR; Repeat Rewrite S_INR; Ring.
Qed.

Lemma Ropp_mul3 : (r1,r2:R) ``r1*(-r2) == -(r1*r2)``.
Intros; Rewrite <- Ropp_mul1; Ring.
Qed.

(**********)
(* Un encadrement de sin par ses sommes partielles sur [0;PI] *)
Theorem sin_bound : (a:R; n:nat) ``0 <= a``->``a <= PI``->``(sin_approx a (plus (mult (S (S O)) n) (S O))) <= (sin a)<= (sin_approx a (mult (S (S O)) (plus n (S O))))``.
Intros; Case (Req_EM a R0); Intro Hyp_a.
Rewrite Hyp_a; Rewrite sin_0; Split; Right; Unfold sin_approx; Apply sum_eq_R0 Orelse (Symmetry; Apply sum_eq_R0); Intros; Unfold sin_term; Rewrite pow_add; Simpl; Unfold Rdiv; Rewrite Rmult_Ol; Ring.
Unfold sin_approx; Cut ``0<a``.
Intro Hyp_a_pos.
Rewrite (decomp_sum (sin_term a) (plus (mult (S (S O)) n) (S O))).
Rewrite (decomp_sum (sin_term a) (mult (S (S O)) (plus n (S O)))).
Replace (sin_term a O) with a.
Cut (Rle (sum_f_R0 [i:nat](sin_term a (S i)) (pred (plus (mult (S (S O)) n) (S O)))) ``(sin a)-a``)/\(Rle ``(sin a)-a`` (sum_f_R0 [i:nat](sin_term a (S i)) (pred (mult (S (S O)) (plus n (S O)))))) -> (Rle (Rplus a (sum_f_R0 [i:nat](sin_term a (S i)) (pred (plus (mult (S (S O)) n) (S O))))) (sin a))/\(Rle (sin a) (Rplus a (sum_f_R0 [i:nat](sin_term a (S i)) (pred (mult (S (S O)) (plus n (S O))))))).
Intro; Apply H1.
Pose Un := [n:nat]``(pow a (plus (mult (S (S O)) (S n)) (S O)))/(INR (fact (plus (mult (S (S O)) (S n)) (S O))))``.
Replace (pred (plus (mult (S (S O)) n) (S O))) with (mult (S (S O)) n).
Replace (pred (mult (S (S O)) (plus n (S O)))) with (S (mult (S (S O)) n)).
Replace (sum_f_R0 [i:nat](sin_term a (S i)) (mult (S (S O)) n)) with ``-(sum_f_R0 (tg_alt Un) (mult (S (S O)) n))``.
Replace (sum_f_R0 [i:nat](sin_term a (S i)) (S (mult (S (S O)) n))) with ``-(sum_f_R0 (tg_alt Un) (S (mult (S (S O)) n)))``.
Cut ``(sum_f_R0 (tg_alt Un) (S (mult (S (S O)) n)))<=a-(sin a)<=(sum_f_R0 (tg_alt Un) (mult (S (S O)) n))``->`` -(sum_f_R0 (tg_alt Un) (mult (S (S O)) n)) <= (sin a)-a <=  -(sum_f_R0 (tg_alt Un) (S (mult (S (S O)) n)))``.
Intro; Apply H2.
Apply sommes_partielles_ineq.
Unfold Un_decreasing Un; Intro; Cut (plus (mult (S (S O)) (S (S n0))) (S O))=(S (S (plus (mult (S (S O)) (S n0)) (S O)))).
Intro; Rewrite H3.
Replace ``(pow a (S (S (plus (mult (S (S O)) (S n0)) (S O)))))`` with ``(pow a (plus (mult (S (S O)) (S n0)) (S O)))*(a*a)``.
Unfold Rdiv; Rewrite Rmult_assoc; Apply Rle_monotony.
Left; Apply pow_lt; Assumption.
Apply Rle_monotony_contra with ``(INR (fact (S (S (plus (mult (S (S O)) (S n0)) (S O))))))``.
Rewrite <- H3; Apply lt_INR_0; Apply neq_O_lt; Red; Intro; Assert H5 := (sym_eq ? ? ? H4); Elim (fact_neq_0 ? H5).
Rewrite <- H3; Rewrite (Rmult_sym ``(INR (fact (plus (mult (S (S O)) (S (S n0))) (S O))))``); Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r; Rewrite H3; Do 2 Rewrite fact_simpl; Do 2 Rewrite mult_INR; Repeat Rewrite Rmult_assoc; Rewrite <- Rinv_r_sym.
Rewrite Rmult_1r.
Do 2 Rewrite S_INR; Rewrite plus_INR; Rewrite mult_INR; Repeat Rewrite S_INR; Simpl; Replace ``((0+1+1)*((INR n0)+1)+(0+1)+1+1)*((0+1+1)*((INR n0)+1)+(0+1)+1)`` with ``4*(INR n0)*(INR n0)+18*(INR n0)+20``; [Idtac | Ring].
Apply Rle_trans with ``20``.
Apply Rle_trans with ``16``.
Replace ``16`` with ``(Rsqr 4)``; [Idtac | SqRing].
Replace ``a*a`` with (Rsqr a); [Idtac | Reflexivity].
Apply Rsqr_incr_1.
Apply Rle_trans with PI; [Assumption | Apply PI_4].
Assumption.
Left; Sup0.
Pattern 1 ``16``; Rewrite <- Rplus_Or; Replace ``20`` with ``16+4``; [Apply Rle_compatibility; Left; Sup0 | Ring].
Rewrite <- (Rplus_sym ``20``); Pattern 1 ``20``; Rewrite <- Rplus_Or; Apply Rle_compatibility.
Apply ge0_plus_ge0_is_ge0.
Repeat Apply Rmult_le_pos.
Left; Sup0.
Replace R0 with (INR O); [Apply le_INR; Apply le_O_n | Reflexivity].
Replace R0 with (INR O); [Apply le_INR; Apply le_O_n | Reflexivity].
Apply Rmult_le_pos.
Left; Sup0.
Replace R0 with (INR O); [Apply le_INR; Apply le_O_n | Reflexivity].
Apply INR_fact_neq_0.
Apply INR_fact_neq_0.
Simpl; Ring.
Apply INR_eq; Do 2 Rewrite S_INR; Do 2 Rewrite plus_INR; Do 2 Rewrite mult_INR; Repeat Rewrite S_INR; Ring.
Assert H3 := (cv_speed_pow_fact a); Unfold Un; Unfold Un_cv in H3; Unfold R_dist in H3; Unfold Un_cv; Unfold R_dist; Intros; Elim (H3 eps H4); Intros N H5.
Exists N; Intros; Apply H5.
Replace (plus (mult (2) (S n0)) (1)) with (S (mult (2) (S n0))).
Unfold ge; Apply le_trans with (mult (2) (S n0)).
Apply le_trans with (mult (2) (S N)).
Apply le_trans with (mult (2) N).
Apply le_n_2n.
Apply mult_le; Apply le_n_Sn.
Apply mult_le; Apply le_n_S; Assumption.
Apply le_n_Sn.
Apply INR_eq; Rewrite S_INR; Rewrite plus_INR; Rewrite mult_INR; Reflexivity.
Assert X := (exist_sin (Rsqr a)); Elim X; Intros.
Cut ``x==(sin a)/a``.
Intro; Rewrite H3 in p; Unfold sin_in in p; Unfold infinit_sum in p; Unfold R_dist in p; Unfold Un_cv; Unfold R_dist; Intros.
Cut ``0<eps/(Rabsolu a)``.
Intro; Elim (p ? H5); Intros N H6.
Exists N; Intros.
Replace (sum_f_R0 (tg_alt Un) n0) with (Rmult a (Rminus R1 (sum_f_R0 [i:nat]``(sin_n i)*(pow (Rsqr a) i)`` (S n0)))).
Unfold Rminus; Rewrite Rmult_Rplus_distr; Rewrite Rmult_1r; Rewrite Ropp_distr1; Rewrite Ropp_Ropp; Repeat Rewrite Rplus_assoc; Rewrite (Rplus_sym a); Rewrite (Rplus_sym ``-a``); Repeat Rewrite Rplus_assoc; Rewrite Rplus_Ropp_l; Rewrite Rplus_Or; Apply Rlt_monotony_contra with ``/(Rabsolu a)``.
Apply Rlt_Rinv; Apply Rabsolu_pos_lt; Assumption.
Pattern 1 ``/(Rabsolu a)``; Rewrite <- (Rabsolu_Rinv a  Hyp_a).
Rewrite <- Rabsolu_mult; Rewrite Rmult_Rplus_distr; Rewrite <- Rmult_assoc; Rewrite <- Rinv_l_sym; [Rewrite Rmult_1l | Assumption]; Rewrite (Rmult_sym ``/a``); Rewrite (Rmult_sym ``/(Rabsolu a)``); Rewrite <- Rabsolu_Ropp; Rewrite Ropp_distr1; Rewrite Ropp_Ropp; Unfold Rminus Rdiv in H6; Apply H6; Unfold ge; Apply le_trans with n0; [Exact H7 | Apply le_n_Sn].
Rewrite (decomp_sum [i:nat]``(sin_n i)*(pow (Rsqr a) i)`` (S n0)).
Replace (sin_n O) with R1.
Simpl; Rewrite Rmult_1r; Unfold Rminus; Rewrite Ropp_distr1; Rewrite <- Rplus_assoc; Rewrite Rplus_Ropp_r; Rewrite Rplus_Ol; Rewrite Ropp_mul3; Rewrite <- Ropp_mul1; Rewrite scal_sum; Apply sum_eq.
Intros; Unfold sin_n Un tg_alt; Replace ``(pow (-1) (S i))`` with ``-(pow (-1) i)``.
Replace ``(pow a (plus (mult (S (S O)) (S i)) (S O)))`` with ``(Rsqr a)*(pow (Rsqr a) i)*a``.
Unfold Rdiv; Ring.
Rewrite pow_add; Rewrite pow_Rsqr; Simpl; Ring.
Simpl; Ring.
Unfold sin_n; Unfold Rdiv; Simpl; Rewrite Rinv_R1; Rewrite Rmult_1r; Reflexivity.
Apply lt_O_Sn.
Unfold Rdiv; Apply Rmult_lt_pos.
Assumption.
Apply Rlt_Rinv; Apply Rabsolu_pos_lt; Assumption.
Unfold sin; Case (exist_sin (Rsqr a)).
Intros; Cut x==x0.
Intro; Rewrite H3; Unfold Rdiv.
Symmetry; Apply Rinv_r_simpl_m; Assumption.
Unfold sin_in in p; Unfold sin_in in s; EApply unicite_sum.
Apply p.
Apply s.
Intros; Elim H2; Intros.
Replace ``(sin a)-a`` with ``-(a-(sin a))``; [Idtac | Ring].
Split; Apply Rle_Ropp1; Assumption.
Replace ``-(sum_f_R0 (tg_alt Un) (S (mult (S (S O)) n)))`` with ``-1*(sum_f_R0 (tg_alt Un) (S (mult (S (S O)) n)))``; [Rewrite scal_sum | Ring].
Apply sum_eq; Intros; Unfold sin_term Un tg_alt; Replace ``(pow (-1) (S i))`` with ``-1*(pow (-1) i)``.
Unfold Rdiv; Ring.
Reflexivity.
Replace ``-(sum_f_R0 (tg_alt Un) (mult (S (S O)) n))`` with ``-1*(sum_f_R0 (tg_alt Un) (mult (S (S O)) n))``; [Rewrite scal_sum | Ring].
Apply sum_eq; Intros.
Unfold sin_term Un tg_alt; Replace ``(pow (-1) (S i))`` with ``-1*(pow (-1) i)``.
Unfold Rdiv; Ring.
Reflexivity.
Replace (mult (2) (plus n (1))) with (S (S (mult (2) n))).
Reflexivity.
Apply INR_eq; Do 2 Rewrite S_INR; Do 2 Rewrite mult_INR; Rewrite plus_INR; Repeat Rewrite S_INR; Ring.
Replace (plus (mult (2) n) (1)) with (S (mult (2) n)).
Reflexivity.
Apply INR_eq; Rewrite S_INR; Rewrite plus_INR; Rewrite mult_INR; Repeat Rewrite S_INR; Ring.
Intro; Elim H1; Intros.
Split.
Apply Rle_anti_compatibility with ``-a``.
Rewrite <- Rplus_assoc; Rewrite Rplus_Ropp_l; Rewrite Rplus_Ol; Rewrite (Rplus_sym ``-a``); Apply H2.
Apply Rle_anti_compatibility with ``-a``.
Rewrite <- Rplus_assoc; Rewrite Rplus_Ropp_l; Rewrite Rplus_Ol; Rewrite (Rplus_sym ``-a``); Apply H3.
Unfold sin_term; Simpl; Unfold Rdiv; Rewrite Rinv_R1; Ring.
Replace (mult (2) (plus n (1))) with (S (S (mult (2) n))).
Apply lt_O_Sn.
Apply INR_eq; Do 2 Rewrite S_INR; Do 2 Rewrite mult_INR; Rewrite plus_INR; Repeat Rewrite S_INR; Ring.
Replace (plus (mult (2) n) (1)) with (S (mult (2) n)).
Apply lt_O_Sn.
Apply INR_eq; Rewrite S_INR; Rewrite plus_INR; Rewrite mult_INR; Repeat Rewrite S_INR; Ring.
Inversion H; [Assumption | Elim Hyp_a; Symmetry; Assumption].
Qed.

Lemma pow_le : (a:R;n:nat) ``0<=a`` -> ``0<=(pow a n)``.
Intros; Induction n.
Simpl; Left; Apply Rlt_R0_R1.
Simpl; Apply Rmult_le_pos; Assumption.
Qed.

(**********)
(* Un encadrement de cos par ses sommes partielles sur [-PI/2;PI/2] *)
(* La preuve utilise bien sur la parite de cos et des sommes partielles *)
Lemma cos_bound : (a:R; n:nat) `` -PI/2 <= a``->``a <= PI/2``->``(cos_approx a (plus (mult (S (S O)) n) (S O))) <= (cos a) <= (cos_approx a (mult (S (S O)) (plus n (S O))))``. 
Cut ((a:R; n:nat) ``0 <= a``->``a <= PI/2``->``(cos_approx a (plus (mult (S (S O)) n) (S O))) <= (cos a) <= (cos_approx a (mult (S (S O)) (plus n (S O))))``) -> ((a:R; n:nat) `` -PI/2 <= a``->``a <= PI/2``->``(cos_approx a (plus (mult (S (S O)) n) (S O))) <= (cos a) <= (cos_approx a (mult (S (S O)) (plus n (S O))))``).
Intros H a n; Apply H.
Intros; Unfold cos_approx.
Rewrite (decomp_sum (cos_term a0) (plus (mult (S (S O)) n0) (S O))).
Rewrite (decomp_sum (cos_term a0) (mult (S (S O)) (plus n0 (S O)))).
Replace (cos_term a0 O) with R1.
Cut (Rle (sum_f_R0 [i:nat](cos_term a0 (S i)) (pred (plus (mult (S (S O)) n0) (S O)))) ``(cos a0)-1``)/\(Rle ``(cos a0)-1`` (sum_f_R0 [i:nat](cos_term a0 (S i)) (pred (mult (S (S O)) (plus n0 (S O)))))) -> (Rle (Rplus R1 (sum_f_R0 [i:nat](cos_term a0 (S i)) (pred (plus (mult (S (S O)) n0) (S O))))) (cos a0))/\(Rle (cos a0) (Rplus R1 (sum_f_R0 [i:nat](cos_term a0 (S i)) (pred (mult (S (S O)) (plus n0 (S O))))))).
Intro; Apply H2.
Pose Un := [n:nat]``(pow a0 (mult (S (S O)) (S n)))/(INR (fact (mult (S (S O)) (S n))))``.
Replace (pred (plus (mult (S (S O)) n0) (S O))) with (mult (S (S O)) n0).
Replace (pred (mult (S (S O)) (plus n0 (S O)))) with (S (mult (S (S O)) n0)).
Replace (sum_f_R0 [i:nat](cos_term a0 (S i)) (mult (S (S O)) n0)) with ``-(sum_f_R0 (tg_alt Un) (mult (S (S O)) n0))``.
Replace (sum_f_R0 [i:nat](cos_term a0 (S i)) (S (mult (S (S O)) n0))) with ``-(sum_f_R0 (tg_alt Un) (S (mult (S (S O)) n0)))``.
Cut ``(sum_f_R0 (tg_alt Un) (S (mult (S (S O)) n0)))<=1-(cos a0)<=(sum_f_R0 (tg_alt Un) (mult (S (S O)) n0))``->`` -(sum_f_R0 (tg_alt Un) (mult (S (S O)) n0)) <= (cos a0)-1 <=  -(sum_f_R0 (tg_alt Un) (S (mult (S (S O)) n0)))``.
Intro; Apply H3.
Apply sommes_partielles_ineq.
Unfold Un_decreasing; Intro; Unfold Un.
Cut (mult (S (S O)) (S (S n1)))=(S (S (mult (S (S O)) (S n1)))).
Intro; Rewrite H4; Replace ``(pow a0 (S (S (mult (S (S O)) (S n1)))))`` with ``(pow a0 (mult (S (S O)) (S n1)))*(a0*a0)``.
Unfold Rdiv; Rewrite Rmult_assoc; Apply Rle_monotony.
Apply pow_le; Assumption.
Apply Rle_monotony_contra with ``(INR (fact (S (S (mult (S (S O)) (S n1))))))``.
Rewrite <- H4; Apply lt_INR_0; Apply neq_O_lt; Red; Intro; Assert H6 := (sym_eq ? ? ? H5); Elim (fact_neq_0 ? H6).
Rewrite <- H4; Rewrite (Rmult_sym ``(INR (fact (mult (S (S O)) (S (S n1)))))``); Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r; Rewrite H4; Do 2 Rewrite fact_simpl; Do 2 Rewrite mult_INR; Repeat Rewrite Rmult_assoc; Rewrite <- Rinv_r_sym.
Rewrite Rmult_1r; Do 2 Rewrite S_INR; Rewrite mult_INR; Repeat Rewrite S_INR; Simpl; Replace ``((0+1+1)*((INR n1)+1)+1+1)*((0+1+1)*((INR n1)+1)+1)`` with ``4*(INR n1)*(INR n1)+14*(INR n1)+12``; [Idtac | Ring].
Apply Rle_trans with ``12``.
Apply Rle_trans with ``4``.
Replace ``4`` with ``(Rsqr 2)``; [Idtac | SqRing].
Replace ``a0*a0`` with (Rsqr a0); [Idtac | Reflexivity].
Apply Rsqr_incr_1.
Apply Rle_trans with ``PI/2``.
Assumption.
Unfold Rdiv; Apply Rle_monotony_contra with ``2``.
Apply Rgt_2_0.
Rewrite <- Rmult_assoc; Rewrite Rinv_r_simpl_m.
Replace ``2*2`` with ``4``; [Apply PI_4 | Ring].
DiscrR.
Assumption.
Left; Apply Rgt_2_0.
Pattern 1 ``4``; Rewrite <- Rplus_Or; Replace ``12`` with ``4+8``; [Apply Rle_compatibility; Left; Sup0 | Ring].
Rewrite <- (Rplus_sym ``12``); Pattern 1 ``12``; Rewrite <- Rplus_Or; Apply Rle_compatibility.
Apply ge0_plus_ge0_is_ge0.
Repeat Apply Rmult_le_pos.
Left; Sup0.
Replace R0 with (INR O); [Apply le_INR; Apply le_O_n | Reflexivity].
Replace R0 with (INR O); [Apply le_INR; Apply le_O_n | Reflexivity].
Apply Rmult_le_pos.
Left; Sup0.
Replace R0 with (INR O); [Apply le_INR; Apply le_O_n | Reflexivity].
Apply INR_fact_neq_0.
Apply INR_fact_neq_0.
Simpl; Ring.
Apply INR_eq; Do 2 Rewrite S_INR; Do 2 Rewrite mult_INR; Repeat Rewrite S_INR; Ring.
Assert H4 := (cv_speed_pow_fact a0); Unfold Un; Unfold Un_cv in H4; Unfold R_dist in H4; Unfold Un_cv; Unfold R_dist; Intros; Elim (H4 eps H5); Intros N H6; Exists N; Intros.
Apply H6; Unfold ge; Apply le_trans with (mult (2) (S N)).
Apply le_trans with (mult (2) N).
Apply le_n_2n.
Apply mult_le; Apply le_n_Sn.
Apply mult_le; Apply le_n_S; Assumption.
Assert X := (exist_cos (Rsqr a0)); Elim X; Intros.
Cut ``x==(cos a0)``.
Intro; Rewrite H4 in p; Unfold cos_in in p; Unfold infinit_sum in p; Unfold R_dist in p; Unfold Un_cv; Unfold R_dist; Intros.
Elim (p ? H5); Intros N H6.
Exists N; Intros.
Replace (sum_f_R0 (tg_alt Un) n1) with (Rminus R1 (sum_f_R0 [i:nat]``(cos_n i)*(pow (Rsqr a0) i)`` (S n1))).
Unfold Rminus; Rewrite Ropp_distr1; Rewrite Ropp_Ropp; Repeat Rewrite Rplus_assoc; Rewrite (Rplus_sym R1); Rewrite (Rplus_sym ``-1``); Repeat Rewrite Rplus_assoc; Rewrite Rplus_Ropp_l; Rewrite Rplus_Or; Rewrite <- Rabsolu_Ropp; Rewrite Ropp_distr1; Rewrite Ropp_Ropp; Unfold Rminus in H6; Apply H6.
Unfold ge; Apply le_trans with n1.
Exact H7.
Apply le_n_Sn.
Rewrite (decomp_sum [i:nat]``(cos_n i)*(pow (Rsqr a0) i)`` (S n1)).
Replace (cos_n O) with R1.
Simpl; Rewrite Rmult_1r; Unfold Rminus; Rewrite Ropp_distr1; Rewrite <- Rplus_assoc; Rewrite Rplus_Ropp_r; Rewrite Rplus_Ol; Replace (Ropp (sum_f_R0 [i:nat]``(cos_n (S i))*((Rsqr a0)*(pow (Rsqr a0) i))`` n1)) with (Rmult ``-1`` (sum_f_R0 [i:nat]``(cos_n (S i))*((Rsqr a0)*(pow (Rsqr a0) i))`` n1)); [Idtac | Ring]; Rewrite scal_sum; Apply sum_eq; Intros; Unfold cos_n Un tg_alt.
Replace ``(pow (-1) (S i))`` with ``-(pow (-1) i)``.
Replace ``(pow a0 (mult (S (S O)) (S i)))`` with ``(Rsqr a0)*(pow (Rsqr a0) i)``.
Unfold Rdiv; Ring.
Rewrite pow_Rsqr; Reflexivity.
Simpl; Ring.
Unfold cos_n; Unfold Rdiv; Simpl; Rewrite Rinv_R1; Rewrite Rmult_1r; Reflexivity.
Apply lt_O_Sn.
Unfold cos; Case (exist_cos (Rsqr a0)); Intros; Unfold cos_in in p; Unfold cos_in in c; EApply unicite_sum.
Apply p.
Apply c.
Intros; Elim H3; Intros; Replace ``(cos a0)-1`` with ``-(1-(cos a0))``; [Idtac | Ring].
Split; Apply Rle_Ropp1; Assumption.
Replace ``-(sum_f_R0 (tg_alt Un) (S (mult (S (S O)) n0)))`` with ``-1*(sum_f_R0 (tg_alt Un) (S (mult (S (S O)) n0)))``; [Rewrite scal_sum | Ring].
Apply sum_eq; Intros; Unfold cos_term Un tg_alt; Replace ``(pow (-1) (S i))`` with ``-1*(pow (-1) i)``.
Unfold Rdiv; Ring.
Reflexivity.
Replace ``-(sum_f_R0 (tg_alt Un) (mult (S (S O)) n0))`` with ``-1*(sum_f_R0 (tg_alt Un) (mult (S (S O)) n0))``; [Rewrite scal_sum | Ring]; Apply sum_eq; Intros; Unfold cos_term Un tg_alt; Replace ``(pow (-1) (S i))`` with ``-1*(pow (-1) i)``.
Unfold Rdiv; Ring.
Reflexivity.
Replace (mult (2) (plus n0 (1))) with (S (S (mult (2) n0))).
Reflexivity.
Apply INR_eq; Do 2 Rewrite S_INR; Do 2 Rewrite mult_INR; Rewrite plus_INR; Repeat Rewrite S_INR; Ring.
Replace (plus (mult (2) n0) (1)) with (S (mult (2) n0)).
Reflexivity.
Apply INR_eq; Rewrite S_INR; Rewrite plus_INR; Rewrite mult_INR; Repeat Rewrite S_INR; Ring.
Intro; Elim H2; Intros; Split.
Apply Rle_anti_compatibility with ``-1``.
Rewrite <- Rplus_assoc; Rewrite Rplus_Ropp_l; Rewrite Rplus_Ol; Rewrite (Rplus_sym ``-1``); Apply H3.
Apply Rle_anti_compatibility with ``-1``.
Rewrite <- Rplus_assoc; Rewrite Rplus_Ropp_l; Rewrite Rplus_Ol; Rewrite (Rplus_sym ``-1``); Apply H4.
Unfold cos_term; Simpl; Unfold Rdiv; Rewrite Rinv_R1; Ring.
Replace (mult (2) (plus n0 (1))) with (S (S (mult (2) n0))).
Apply lt_O_Sn.
Apply INR_eq; Do 2 Rewrite S_INR; Do 2 Rewrite mult_INR; Rewrite plus_INR; Repeat Rewrite S_INR; Ring.
Replace (plus (mult (2) n0) (1)) with (S (mult (2) n0)).
Apply lt_O_Sn.
Apply INR_eq; Rewrite S_INR; Rewrite plus_INR; Rewrite mult_INR; Repeat Rewrite S_INR; Ring.
Intros; Case (total_order_T R0 a); Intro.
Elim s; Intro.
Apply H; [Left; Assumption | Assumption].
Apply H; [Right; Assumption | Assumption].
Cut ``0< -a``.
Intro; Cut (x:R;n:nat) (cos_approx x n)==(cos_approx ``-x`` n).
Intro; Rewrite H3; Rewrite (H3 a (mult (S (S O)) (plus n (S O)))); Rewrite cos_paire; Apply H.
Left; Assumption.
Rewrite <- (Ropp_Ropp ``PI/2``); Apply Rle_Ropp1; Unfold Rdiv; Unfold Rdiv in H0; Rewrite <- Ropp_mul1; Exact H0.
Intros; Unfold cos_approx; Apply sum_eq; Intros; Unfold cos_term; Do 2 Rewrite pow_Rsqr; Rewrite Rsqr_neg; Unfold Rdiv; Reflexivity.
Apply Rgt_RO_Ropp; Assumption.
Qed.
