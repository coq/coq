(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
 
(*i $Id$ i*)

Require Compare.
Require Rbase.
Require Rfunctions.
Require Rseries.
Require PartSum.
Require Binomial.
V7only [ Import nat_scope. Import Z_scope. Import R_scope. ].
Open Local Scope R_scope.

(* TT Ak; 1<=k<=N *)
Fixpoint prod_f_SO [An:nat->R;N:nat] : R := Cases N of
  O => R1
| (S p) => ``(prod_f_SO An p)*(An (S p))``
end.

(**********)
Lemma prod_SO_split : (An:nat->R;n,k:nat) (le k n) -> (prod_f_SO An n)==(Rmult (prod_f_SO An k) (prod_f_SO [l:nat](An (plus k l)) (minus n k))).
Intros; Induction n.
Cut k=O; [Intro; Rewrite H0; Simpl; Ring | Inversion H; Reflexivity].
Cut k=(S n)\/(le k n).
Intro; Elim H0; Intro.
Rewrite H1; Simpl; Rewrite <- minus_n_n; Simpl; Ring.
Replace (minus (S n) k) with (S (minus n k)).
Simpl; Replace (plus k (S (minus n k))) with (S n).
Rewrite Hrecn; [Ring | Assumption].
Apply INR_eq; Rewrite S_INR; Rewrite plus_INR; Rewrite S_INR; Rewrite minus_INR; [Ring | Assumption].
Apply INR_eq; Rewrite S_INR; Repeat Rewrite minus_INR.
Rewrite S_INR; Ring.
Apply le_trans with n; [Assumption | Apply le_n_Sn].
Assumption.
Inversion H; [Left; Reflexivity | Right; Assumption].
Qed.

(**********)
Lemma prod_SO_pos : (An:nat->R;N:nat) ((n:nat)(le n N)->``0<=(An n)``) -> ``0<=(prod_f_SO An N)``.
Intros; Induction N.
Simpl; Left; Apply Rlt_R0_R1.
Simpl; Apply Rmult_le_pos.
Apply HrecN; Intros; Apply H; Apply le_trans with N; [Assumption | Apply le_n_Sn].
Apply H; Apply le_n.
Qed.

(**********)
Lemma prod_SO_Rle : (An,Bn:nat->R;N:nat) ((n:nat)(le n N)->``0<=(An n)<=(Bn n)``) -> ``(prod_f_SO An N)<=(prod_f_SO Bn N)``.
Intros; Induction N.
Right; Reflexivity.
Simpl; Apply Rle_trans with ``(prod_f_SO An N)*(Bn (S N))``.
Apply Rle_monotony.
Apply prod_SO_pos; Intros; Elim (H n (le_trans ? ? ? H0 (le_n_Sn N))); Intros; Assumption.
Elim (H (S N) (le_n (S N))); Intros; Assumption.
Do 2 Rewrite <- (Rmult_sym (Bn (S N))); Apply Rle_monotony.
Elim (H (S N) (le_n (S N))); Intros.
Apply Rle_trans with (An (S N)); Assumption.
Apply HrecN; Intros; Elim (H n (le_trans ? ? ? H0 (le_n_Sn N))); Intros; Split; Assumption.
Qed.

(* Application to factorial *)
Lemma fact_prodSO : (n:nat) (INR (fact n))==(prod_f_SO [k:nat](INR k) n).
Intro; Induction n.
Reflexivity.
Change (INR (mult (S n) (fact n)))==(prod_f_SO ([k:nat](INR k)) (S n)).
Rewrite mult_INR; Rewrite Rmult_sym; Rewrite Hrecn; Reflexivity.
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

(* We prove that (N!)²<=(2N-k)!*k! forall k in [|O;2N|] *)
Lemma RfactN_fact2N_factk : (N,k:nat) (le k (mult (2) N)) -> ``(Rsqr (INR (fact N)))<=(INR (fact (minus (mult (S (S O)) N) k)))*(INR (fact k))``.
Intros; Unfold Rsqr; Repeat Rewrite fact_prodSO.
Cut (le k N)\/(le N k).
Intro; Elim H0; Intro.
Rewrite (prod_SO_split [l:nat](INR l) (minus (mult (2) N) k) N).
Rewrite Rmult_assoc; Apply Rle_monotony.
Apply prod_SO_pos; Intros; Apply pos_INR.
Replace (minus (minus (mult (2) N) k) N) with (minus N k).
Rewrite Rmult_sym; Rewrite (prod_SO_split [l:nat](INR l) N k).
Apply Rle_monotony.
Apply prod_SO_pos; Intros; Apply pos_INR.
Apply prod_SO_Rle; Intros; Split.
Apply pos_INR.
Apply le_INR; Apply le_reg_r; Assumption.
Assumption.
Apply INR_eq; Repeat Rewrite minus_INR.
Rewrite mult_INR; Repeat Rewrite S_INR; Ring.
Apply le_trans with N; [Assumption | Apply le_n_2n].
Apply simpl_le_plus_l with k; Rewrite <- le_plus_minus.
Replace (mult (2) N) with (plus N N); [Idtac | Ring].
Apply le_reg_r; Assumption.
Assumption.
Assumption.
Apply simpl_le_plus_l with k; Rewrite <- le_plus_minus.
Replace (mult (2) N) with (plus N N); [Idtac | Ring].
Apply le_reg_r; Assumption.
Assumption.
Rewrite <- (Rmult_sym (prod_f_SO [l:nat](INR l) k)); Rewrite (prod_SO_split [l:nat](INR l) k N).
Rewrite Rmult_assoc; Apply Rle_monotony.
Apply prod_SO_pos; Intros; Apply pos_INR.
Rewrite Rmult_sym; Rewrite (prod_SO_split [l:nat](INR l) N (minus (mult (2) N) k)).
Apply Rle_monotony.
Apply prod_SO_pos; Intros; Apply pos_INR.
Replace (minus N (minus (mult (2) N) k)) with (minus k N).
Apply prod_SO_Rle; Intros; Split.
Apply pos_INR.
Apply le_INR; Apply le_reg_r.
Apply simpl_le_plus_l with k; Rewrite <- le_plus_minus.
Replace (mult (2) N) with (plus N N); [Idtac | Ring]; Apply le_reg_r; Assumption.
Assumption.
Apply INR_eq; Repeat Rewrite minus_INR.
Rewrite mult_INR; Do 2 Rewrite S_INR; Ring.
Assumption.
Apply simpl_le_plus_l with k; Rewrite <- le_plus_minus.
Replace (mult (2) N) with (plus N N); [Idtac | Ring]; Apply le_reg_r; Assumption.
Assumption.
Assumption.
Apply simpl_le_plus_l with k; Rewrite <- le_plus_minus.
Replace (mult (2) N) with (plus N N); [Idtac | Ring]; Apply le_reg_r; Assumption.
Assumption.
Assumption.
Elim (le_dec k N); Intro; [Left; Assumption | Right; Assumption].
Qed.

(**********)
Lemma INR_fact_lt_0 : (n:nat) ``0<(INR (fact n))``.
Intro; Apply lt_INR_0; Apply neq_O_lt; Red; Intro; Elim (fact_neq_0 n); Symmetry; Assumption.
Qed.

(* We have the following inequality : (C 2N k) <= (C 2N N) forall k in [|O;2N|] *)
Lemma C_maj : (N,k:nat) (le k (mult (2) N)) -> ``(C (mult (S (S O)) N) k)<=(C (mult (S (S O)) N) N)``.
Intros; Unfold C; Unfold Rdiv; Apply Rle_monotony.
Apply pos_INR.
Replace (minus (mult (2) N) N) with N.
Apply Rle_monotony_contra with ``((INR (fact N))*(INR (fact N)))``.
Apply Rmult_lt_pos; Apply INR_fact_lt_0.
Rewrite <- Rinv_r_sym.
Rewrite Rmult_sym; Apply Rle_monotony_contra with ``((INR (fact k))*
   (INR (fact (minus (mult (S (S O)) N) k))))``.
Apply Rmult_lt_pos; Apply INR_fact_lt_0.
Rewrite Rmult_1r; Rewrite <- mult_INR; Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym.
Rewrite Rmult_1l; Rewrite mult_INR; Rewrite (Rmult_sym (INR (fact k))); Replace ``(INR (fact N))*(INR (fact N))`` with (Rsqr (INR (fact N))).
Apply RfactN_fact2N_factk.
Assumption.
Reflexivity.
Rewrite mult_INR; Apply prod_neq_R0; Apply INR_fact_neq_0.
Apply prod_neq_R0; Apply INR_fact_neq_0.
Apply INR_eq; Rewrite minus_INR; [Rewrite mult_INR; Do 2 Rewrite S_INR; Ring | Apply le_n_2n].
Qed.
