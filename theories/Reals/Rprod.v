(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
 
(*i $Id$ i*)

Require Import Compare.
Require Import Rbase.
Require Import Rfunctions.
Require Import Rseries.
Require Import PartSum.
Require Import Binomial.
Open Local Scope R_scope.

(* TT Ak; 1<=k<=N *)
Fixpoint prod_f_SO (An:nat -> R) (N:nat) {struct N} : R :=
  match N with
  | O => 1
  | S p => prod_f_SO An p * An (S p)
  end.

(**********)
Lemma prod_SO_split :
 forall (An:nat -> R) (n k:nat),
   (k <= n)%nat ->
   prod_f_SO An n =
   prod_f_SO An k * prod_f_SO (fun l:nat => An (k + l)%nat) (n - k).
intros; induction  n as [| n Hrecn].
cut (k = 0%nat);
 [ intro; rewrite H0; simpl in |- *; ring | inversion H; reflexivity ].
cut (k = S n \/ (k <= n)%nat).
intro; elim H0; intro.
rewrite H1; simpl in |- *; rewrite <- minus_n_n; simpl in |- *; ring.
replace (S n - k)%nat with (S (n - k)).
simpl in |- *; replace (k + S (n - k))%nat with (S n).
rewrite Hrecn; [ ring | assumption ].
apply INR_eq; rewrite S_INR; rewrite plus_INR; rewrite S_INR;
 rewrite minus_INR; [ ring | assumption ].
apply INR_eq; rewrite S_INR; repeat rewrite minus_INR.
rewrite S_INR; ring.
apply le_trans with n; [ assumption | apply le_n_Sn ].
assumption.
inversion H; [ left; reflexivity | right; assumption ].
Qed.

(**********)
Lemma prod_SO_pos :
 forall (An:nat -> R) (N:nat),
   (forall n:nat, (n <= N)%nat -> 0 <= An n) -> 0 <= prod_f_SO An N.
intros; induction  N as [| N HrecN].
simpl in |- *; left; apply Rlt_0_1.
simpl in |- *; apply Rmult_le_pos.
apply HrecN; intros; apply H; apply le_trans with N;
 [ assumption | apply le_n_Sn ].
apply H; apply le_n.
Qed.

(**********)
Lemma prod_SO_Rle :
 forall (An Bn:nat -> R) (N:nat),
   (forall n:nat, (n <= N)%nat -> 0 <= An n <= Bn n) ->
   prod_f_SO An N <= prod_f_SO Bn N.
intros; induction  N as [| N HrecN].
right; reflexivity.
simpl in |- *; apply Rle_trans with (prod_f_SO An N * Bn (S N)).
apply Rmult_le_compat_l.
apply prod_SO_pos; intros; elim (H n (le_trans _ _ _ H0 (le_n_Sn N))); intros;
 assumption.
elim (H (S N) (le_n (S N))); intros; assumption.
do 2 rewrite <- (Rmult_comm (Bn (S N))); apply Rmult_le_compat_l.
elim (H (S N) (le_n (S N))); intros.
apply Rle_trans with (An (S N)); assumption.
apply HrecN; intros; elim (H n (le_trans _ _ _ H0 (le_n_Sn N))); intros;
 split; assumption.
Qed.

(* Application to factorial *)
Lemma fact_prodSO :
 forall n:nat, INR (fact n) = prod_f_SO (fun k:nat => INR k) n.
intro; induction  n as [| n Hrecn].
reflexivity.
change (INR (S n * fact n) = prod_f_SO (fun k:nat => INR k) (S n)) in |- *.
rewrite mult_INR; rewrite Rmult_comm; rewrite Hrecn; reflexivity.
Qed.

Lemma le_n_2n : forall n:nat, (n <= 2 * n)%nat.
simple induction n.
replace (2 * 0)%nat with 0%nat; [ apply le_n | ring ].
intros; replace (2 * S n0)%nat with (S (S (2 * n0))).
apply le_n_S; apply le_S; assumption.
replace (S (S (2 * n0))) with (2 * n0 + 2)%nat; [ idtac | ring ].
replace (S n0) with (n0 + 1)%nat; [ idtac | ring ].
ring.
Qed. 

(* We prove that (N!)²<=(2N-k)!*k! forall k in [|O;2N|] *)
Lemma RfactN_fact2N_factk :
 forall N k:nat,
   (k <= 2 * N)%nat ->
   Rsqr (INR (fact N)) <= INR (fact (2 * N - k)) * INR (fact k).
intros; unfold Rsqr in |- *; repeat rewrite fact_prodSO.
cut ((k <= N)%nat \/ (N <= k)%nat).
intro; elim H0; intro.
rewrite (prod_SO_split (fun l:nat => INR l) (2 * N - k) N).
rewrite Rmult_assoc; apply Rmult_le_compat_l.
apply prod_SO_pos; intros; apply pos_INR.
replace (2 * N - k - N)%nat with (N - k)%nat.
rewrite Rmult_comm; rewrite (prod_SO_split (fun l:nat => INR l) N k).
apply Rmult_le_compat_l.
apply prod_SO_pos; intros; apply pos_INR.
apply prod_SO_Rle; intros; split.
apply pos_INR.
apply le_INR; apply plus_le_compat_r; assumption.
assumption.
apply INR_eq; repeat rewrite minus_INR.
rewrite mult_INR; repeat rewrite S_INR; ring.
apply le_trans with N; [ assumption | apply le_n_2n ].
apply (fun p n m:nat => plus_le_reg_l n m p) with k; rewrite <- le_plus_minus.
replace (2 * N)%nat with (N + N)%nat; [ idtac | ring ].
apply plus_le_compat_r; assumption.
assumption.
assumption.
apply (fun p n m:nat => plus_le_reg_l n m p) with k; rewrite <- le_plus_minus.
replace (2 * N)%nat with (N + N)%nat; [ idtac | ring ].
apply plus_le_compat_r; assumption.
assumption.
rewrite <- (Rmult_comm (prod_f_SO (fun l:nat => INR l) k));
 rewrite (prod_SO_split (fun l:nat => INR l) k N).
rewrite Rmult_assoc; apply Rmult_le_compat_l.
apply prod_SO_pos; intros; apply pos_INR.
rewrite Rmult_comm;
 rewrite (prod_SO_split (fun l:nat => INR l) N (2 * N - k)).
apply Rmult_le_compat_l.
apply prod_SO_pos; intros; apply pos_INR.
replace (N - (2 * N - k))%nat with (k - N)%nat.
apply prod_SO_Rle; intros; split.
apply pos_INR.
apply le_INR; apply plus_le_compat_r.
apply (fun p n m:nat => plus_le_reg_l n m p) with k; rewrite <- le_plus_minus.
replace (2 * N)%nat with (N + N)%nat; [ idtac | ring ];
 apply plus_le_compat_r; assumption.
assumption.
apply INR_eq; repeat rewrite minus_INR.
rewrite mult_INR; do 2 rewrite S_INR; ring.
assumption.
apply (fun p n m:nat => plus_le_reg_l n m p) with k; rewrite <- le_plus_minus.
replace (2 * N)%nat with (N + N)%nat; [ idtac | ring ];
 apply plus_le_compat_r; assumption.
assumption.
assumption.
apply (fun p n m:nat => plus_le_reg_l n m p) with k; rewrite <- le_plus_minus.
replace (2 * N)%nat with (N + N)%nat; [ idtac | ring ];
 apply plus_le_compat_r; assumption.
assumption.
assumption.
elim (le_dec k N); intro; [ left; assumption | right; assumption ].
Qed.

(**********)
Lemma INR_fact_lt_0 : forall n:nat, 0 < INR (fact n).
intro; apply lt_INR_0; apply neq_O_lt; red in |- *; intro;
 elim (fact_neq_0 n); symmetry  in |- *; assumption.
Qed.

(* We have the following inequality : (C 2N k) <= (C 2N N) forall k in [|O;2N|] *)
Lemma C_maj : forall N k:nat, (k <= 2 * N)%nat -> C (2 * N) k <= C (2 * N) N.
intros; unfold C in |- *; unfold Rdiv in |- *; apply Rmult_le_compat_l.
apply pos_INR.
replace (2 * N - N)%nat with N.
apply Rmult_le_reg_l with (INR (fact N) * INR (fact N)).
apply Rmult_lt_0_compat; apply INR_fact_lt_0.
rewrite <- Rinv_r_sym.
rewrite Rmult_comm;
 apply Rmult_le_reg_l with (INR (fact k) * INR (fact (2 * N - k))).
apply Rmult_lt_0_compat; apply INR_fact_lt_0.
rewrite Rmult_1_r; rewrite <- mult_INR; rewrite <- Rmult_assoc;
 rewrite <- Rinv_r_sym.
rewrite Rmult_1_l; rewrite mult_INR; rewrite (Rmult_comm (INR (fact k)));
 replace (INR (fact N) * INR (fact N)) with (Rsqr (INR (fact N))).
apply RfactN_fact2N_factk.
assumption.
reflexivity.
rewrite mult_INR; apply prod_neq_R0; apply INR_fact_neq_0.
apply prod_neq_R0; apply INR_fact_neq_0.
apply INR_eq; rewrite minus_INR;
 [ rewrite mult_INR; do 2 rewrite S_INR; ring | apply le_n_2n ].
Qed.