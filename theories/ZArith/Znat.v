(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** Binary Integers (Pierre Crégut, CNET, Lannion, France) *)

Require Export Arith.
Require Import BinPos.
Require Import BinInt.
Require Import Zcompare.
Require Import Zorder.
Require Import Decidable.
Require Import Peano_dec.
Require Export Compare_dec.

Open Local Scope Z_scope.

Definition neq (x y:nat) := x <> y.

(**********************************************************************)
(** Properties of the injection from nat into Z *)

Theorem inj_S : forall n:nat, Z_of_nat (S n) = Zsucc (Z_of_nat n).
Proof.
intro y; induction y as [| n H];
 [ unfold Zsucc in |- *; simpl in |- *; trivial with arith
 | change (Zpos (Psucc (P_of_succ_nat n)) = Zsucc (Z_of_nat (S n))) in |- *;
    rewrite Zpos_succ_morphism; trivial with arith ].
Qed.
 
Theorem inj_plus : forall n m:nat, Z_of_nat (n + m) = Z_of_nat n + Z_of_nat m.
Proof.
intro x; induction x as [| n H]; intro y; destruct y as [| m];
 [ simpl in |- *; trivial with arith
 | simpl in |- *; trivial with arith
 | simpl in |- *; rewrite <- plus_n_O; trivial with arith
 | change (Z_of_nat (S (n + S m)) = Z_of_nat (S n) + Z_of_nat (S m)) in |- *;
    rewrite inj_S; rewrite H; do 2 rewrite inj_S; rewrite Zplus_succ_l;
    trivial with arith ].
Qed.
 
Theorem inj_mult : forall n m:nat, Z_of_nat (n * m) = Z_of_nat n * Z_of_nat m.
Proof.
intro x; induction x as [| n H];
 [ simpl in |- *; trivial with arith
 | intro y; rewrite inj_S; rewrite <- Zmult_succ_l_reverse; rewrite <- H;
    rewrite <- inj_plus; simpl in |- *; rewrite plus_comm; 
    trivial with arith ].
Qed.

Theorem inj_neq : forall n m:nat, neq n m -> Zne (Z_of_nat n) (Z_of_nat m).
Proof.
unfold neq, Zne, not in |- *; intros x y H1 H2; apply H1; generalize H2;
 case x; case y; intros;
 [ auto with arith
 | discriminate H0
 | discriminate H0
 | simpl in H0; injection H0;
    do 2 rewrite <- nat_of_P_o_P_of_succ_nat_eq_succ; 
    intros E; rewrite E; auto with arith ].
Qed. 

Theorem inj_le : forall n m:nat, (n <= m)%nat -> Z_of_nat n <= Z_of_nat m.
Proof.
intros x y; intros H; elim H;
 [ unfold Zle in |- *; elim (Zcompare_Eq_iff_eq (Z_of_nat x) (Z_of_nat x));
    intros H1 H2; rewrite H2; [ discriminate | trivial with arith ]
 | intros m H1 H2; apply Zle_trans with (Z_of_nat m);
    [ assumption | rewrite inj_S; apply Zle_succ ] ].
Qed.

Theorem inj_lt : forall n m:nat, (n < m)%nat -> Z_of_nat n < Z_of_nat m.
Proof.
intros x y H; apply Zgt_lt; apply Zlt_succ_gt; rewrite <- inj_S; apply inj_le;
 exact H.
Qed.

Theorem inj_gt : forall n m:nat, (n > m)%nat -> Z_of_nat n > Z_of_nat m.
Proof.
intros x y H; apply Zlt_gt; apply inj_lt; exact H.
Qed.

Theorem inj_ge : forall n m:nat, (n >= m)%nat -> Z_of_nat n >= Z_of_nat m.
Proof.
intros x y H; apply Zle_ge; apply inj_le; apply H.
Qed.

Theorem inj_eq : forall n m:nat, n = m -> Z_of_nat n = Z_of_nat m.
Proof.
intros x y H; rewrite H; trivial with arith.
Qed.

Theorem intro_Z :
 forall n:nat,  exists y : Z, Z_of_nat n = y /\ 0 <= y * 1 + 0.
Proof.
intros x; exists (Z_of_nat x); split;
 [ trivial with arith
 | rewrite Zmult_comm; rewrite Zmult_1_l; rewrite Zplus_0_r;
    unfold Zle in |- *; elim x; intros; simpl in |- *; 
    discriminate ].
Qed.

Theorem inj_minus1 :
 forall n m:nat, (m <= n)%nat -> Z_of_nat (n - m) = Z_of_nat n - Z_of_nat m.
Proof.
intros x y H; apply (Zplus_reg_l (Z_of_nat y)); unfold Zminus in |- *;
 rewrite Zplus_permute; rewrite Zplus_opp_r; rewrite <- inj_plus;
 rewrite <- (le_plus_minus y x H); rewrite Zplus_0_r; 
 trivial with arith.
Qed.
 
Theorem inj_minus2 : forall n m:nat, (m > n)%nat -> Z_of_nat (n - m) = 0.
Proof.
intros x y H; rewrite not_le_minus_0;
 [ trivial with arith | apply gt_not_le; assumption ].
Qed.

Theorem Zpos_eq_Z_of_nat_o_nat_of_P :
 forall p:positive, Zpos p = Z_of_nat (nat_of_P p).
Proof.
intros x; elim x; simpl in |- *; auto.
intros p H; rewrite ZL6.
apply f_equal with (f := Zpos).
apply nat_of_P_inj.
rewrite nat_of_P_o_P_of_succ_nat_eq_succ; unfold nat_of_P in |- *;
 simpl in |- *.
rewrite ZL6; auto.
intros p H; unfold nat_of_P in |- *; simpl in |- *.
rewrite ZL6; simpl in |- *.
rewrite inj_plus; repeat rewrite <- H.
rewrite Zpos_xO; simpl in |- *; rewrite Pplus_diag; reflexivity.
Qed.
