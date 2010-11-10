(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Binary Integers (Pierre Crégut, CNET, Lannion, France) *)

Require Export Arith_base.
Require Import BinPos.
Require Import BinInt.
Require Import Zcompare.
Require Import Zorder.
Require Import Decidable.
Require Import Peano_dec.
Require Import Min Max.
Require Export Compare_dec.

Open Local Scope Z_scope.

Definition neq (x y:nat) := x <> y.

(************************************************)
(** Properties of the injection from nat into Z *)

(** Injection and successor *)

Theorem inj_0 : Z_of_nat 0 = 0%Z.
Proof.
  reflexivity.
Qed.

Theorem inj_S : forall n:nat, Z_of_nat (S n) = Zsucc (Z_of_nat n).
Proof.
  intro y; induction y as [| n H];
    [ unfold Zsucc in |- *; simpl in |- *; trivial with arith
      | change (Zpos (Psucc (P_of_succ_nat n)) = Zsucc (Z_of_nat (S n))) in |- *;
	rewrite Zpos_succ_morphism; trivial with arith ].
Qed.

(** Injection and equality. *)

Theorem inj_eq : forall n m:nat, n = m -> Z_of_nat n = Z_of_nat m.
Proof.
  intros x y H; rewrite H; trivial with arith.
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

Theorem inj_eq_rev : forall n m:nat, Z_of_nat n = Z_of_nat m -> n = m.
Proof.
  intros x y H.
  destruct (eq_nat_dec x y) as [H'|H']; auto.
  exfalso.
  exact (inj_neq _ _ H' H).
Qed.

Theorem inj_eq_iff : forall n m:nat, n=m <-> Z_of_nat n = Z_of_nat m.
Proof.
 split; [apply inj_eq | apply inj_eq_rev].
Qed.


(** Injection and order relations: *)

Theorem inj_compare : forall n m:nat,
 (Z_of_nat n ?= Z_of_nat m) = nat_compare n m.
Proof.
 induction n; destruct m; trivial.
 rewrite 2 inj_S, Zcompare_succ_compat. now simpl.
Qed.

(* Both ways ... *)

Theorem inj_le_iff : forall n m:nat, (n<=m)%nat <-> Z_of_nat n <= Z_of_nat m.
Proof.
 intros. unfold Zle. rewrite inj_compare. apply nat_compare_le.
Qed.

Theorem inj_lt_iff : forall n m:nat, (n<m)%nat <-> Z_of_nat n < Z_of_nat m.
Proof.
 intros. unfold Zlt. rewrite inj_compare. apply nat_compare_lt.
Qed.

Theorem inj_ge_iff : forall n m:nat, (n>=m)%nat <-> Z_of_nat n >= Z_of_nat m.
Proof.
 intros. unfold Zge. rewrite inj_compare. apply nat_compare_ge.
Qed.

Theorem inj_gt_iff : forall n m:nat, (n>m)%nat <-> Z_of_nat n > Z_of_nat m.
Proof.
 intros. unfold Zgt. rewrite inj_compare. apply nat_compare_gt.
Qed.

(** One way ... *)

Theorem inj_le : forall n m:nat, (n <= m)%nat -> Z_of_nat n <= Z_of_nat m.
Proof. apply inj_le_iff. Qed.

Theorem inj_lt : forall n m:nat, (n < m)%nat -> Z_of_nat n < Z_of_nat m.
Proof. apply inj_lt_iff. Qed.

Theorem inj_ge : forall n m:nat, (n >= m)%nat -> Z_of_nat n >= Z_of_nat m.
Proof. apply inj_ge_iff. Qed.

Theorem inj_gt : forall n m:nat, (n > m)%nat -> Z_of_nat n > Z_of_nat m.
Proof. apply inj_gt_iff. Qed.

(** The other way ... *)

Theorem inj_le_rev : forall n m:nat, Z_of_nat n <= Z_of_nat m -> (n <= m)%nat.
Proof. apply inj_le_iff. Qed.

Theorem inj_lt_rev : forall n m:nat, Z_of_nat n < Z_of_nat m -> (n < m)%nat.
Proof. apply inj_lt_iff. Qed.

Theorem inj_ge_rev : forall n m:nat, Z_of_nat n >= Z_of_nat m -> (n >= m)%nat.
Proof. apply inj_ge_iff. Qed.

Theorem inj_gt_rev : forall n m:nat, Z_of_nat n > Z_of_nat m -> (n > m)%nat.
Proof. apply inj_gt_iff. Qed.

(** Injection and usual operations *)

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

Theorem inj_minus : forall n m:nat,
 Z_of_nat (minus n m) = Zmax 0 (Z_of_nat n - Z_of_nat m).
Proof.
 intros.
 unfold Zmax.
 destruct (le_lt_dec m n) as [H|H].

 rewrite inj_minus1; trivial.
 apply inj_le, Zle_minus_le_0 in H. revert H. unfold Zle.
 case Zcompare_spec; intuition.

 rewrite inj_minus2; trivial.
 apply inj_lt, Zlt_gt in H.
 apply (Zplus_gt_compat_r _ _ (- Z_of_nat m)) in H.
 rewrite Zplus_opp_r in H.
 unfold Zminus. rewrite H; auto.
Qed.

Theorem inj_min : forall n m:nat,
  Z_of_nat (min n m) = Zmin (Z_of_nat n) (Z_of_nat m).
Proof.
 intros n m. unfold Zmin. rewrite inj_compare.
 case nat_compare_spec; intros; f_equal.
 subst. apply min_idempotent.
 apply min_l. auto with arith.
 apply min_r. auto with arith.
Qed.

Theorem inj_max : forall n m:nat,
  Z_of_nat (max n m) = Zmax (Z_of_nat n) (Z_of_nat m).
Proof.
 intros n m. unfold Zmax. rewrite inj_compare.
 case nat_compare_spec; intros; f_equal.
 subst. apply max_idempotent.
 apply max_r. auto with arith.
 apply max_l. auto with arith.
Qed.

(** Composition of injections **)

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

(** Misc *)

Theorem intro_Z :
  forall n:nat,  exists y : Z, Z_of_nat n = y /\ 0 <= y * 1 + 0.
Proof.
  intros x; exists (Z_of_nat x); split;
    [ trivial with arith
      | rewrite Zmult_comm; rewrite Zmult_1_l; rewrite Zplus_0_r;
	unfold Zle in |- *; elim x; intros; simpl in |- *;
          discriminate ].
Qed.

Lemma Zpos_P_of_succ_nat : forall n:nat,
 Zpos (P_of_succ_nat n) = Zsucc (Z_of_nat n).
Proof.
  intros.
  unfold Z_of_nat.
  destruct n.
  simpl; auto.
  simpl (P_of_succ_nat (S n)).
  apply Zpos_succ_morphism.
Qed.
