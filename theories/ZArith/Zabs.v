(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(** Binary Integers (Pierre Crégut (CNET, Lannion, France) *)

Require Import Arith_base.
Require Import BinPos.
Require Import BinInt.
Require Import Zcompare.
Require Import Zorder.
Require Import Znat.
Require Import ZArith_dec.

Open Local Scope Z_scope.

(**********************************************************************)
(** * Properties of absolute value *)

Notation Zabs_eq := Zabs_eq (only parsing). (* 0 <= n -> Zabs n = n *)
Notation Zabs_non_eq := Zabs_non_eq (only parsing). (* n <= 0 -> Zabs n = -n *)

Theorem Zabs_Zopp : forall n:Z, Zabs (- n) = Zabs n.
Proof.
  intros z; case z; simpl; auto.
Qed.

(** * Proving a property of the absolute value by cases *)

Lemma Zabs_ind :
  forall (P:Z -> Prop) (n:Z),
    (n >= 0 -> P n) -> (n <= 0 -> P (- n)) -> P (Zabs n).
Proof.
  intros P x H H0; elim (Z_lt_ge_dec x 0); intro.
  assert (x <= 0). apply Zlt_le_weak; assumption.
  rewrite Zabs_non_eq. apply H0. assumption. assumption.
  rewrite Zabs_eq. apply H; assumption. apply Zge_le. assumption.
Qed.

Theorem Zabs_intro : forall P (n:Z), P (- n) -> P n -> P (Zabs n).
Proof.
  intros P z; case z; simpl in |- *; auto.
Qed.

Definition Zabs_dec : forall x:Z, {x = Zabs x} + {x = - Zabs x}.
Proof.
  intro x; destruct x; auto with arith.
Defined.

Lemma Zabs_pos : forall n:Z, 0 <= Zabs n.
  intro x; destruct x; auto with arith; compute in |- *; intros H; inversion H.
Qed.

Lemma Zabs_involutive : forall x:Z, Zabs (Zabs x) = Zabs x.
Proof.
  intros; apply Zabs_eq; apply Zabs_pos.
Qed.

Theorem Zabs_eq_case : forall n m:Z, Zabs n = Zabs m -> n = m \/ n = - m.
Proof.
  intros z1 z2; case z1; case z2; simpl in |- *; auto;
    try (intros; discriminate); intros p1 p2 H1; injection H1;
      (intros H2; rewrite H2); auto.
Qed.

Lemma Zabs_spec : forall x:Z,
  0 <= x /\ Zabs x = x \/
  0 > x /\ Zabs x = -x.
Proof.
 intros; unfold Zabs, Zle, Zgt; destruct x; simpl; intuition discriminate.
Qed.

(** * Triangular inequality *)

Hint Local Resolve Zle_neg_pos: zarith.

Theorem Zabs_triangle : forall n m:Z, Zabs (n + m) <= Zabs n + Zabs m.
Proof.
  intros z1 z2; case z1; case z2; try (simpl in |- *; auto with zarith; fail).
  intros p1 p2;
    apply Zabs_intro with (P := fun x => x <= Zabs (Zpos p2) + Zabs (Zneg p1));
      try rewrite Zopp_plus_distr; auto with zarith.
  apply Zplus_le_compat; simpl in |- *; auto with zarith.
  apply Zplus_le_compat; simpl in |- *; auto with zarith.
  intros p1 p2;
    apply Zabs_intro with (P := fun x => x <= Zabs (Zpos p2) + Zabs (Zneg p1));
      try rewrite Zopp_plus_distr; auto with zarith.
  apply Zplus_le_compat; simpl in |- *; auto with zarith.
  apply Zplus_le_compat; simpl in |- *; auto with zarith.
Qed.

(** * Absolute value and multiplication *)

Lemma Zsgn_Zabs : forall n:Z, n * Zsgn n = Zabs n.
Proof.
  intro x; destruct x; rewrite Zmult_comm; auto with arith.
Qed.

Lemma Zabs_Zsgn : forall n:Z, Zabs n * Zsgn n = n.
Proof.
  intro x; destruct x; rewrite Zmult_comm; auto with arith.
Qed.

Theorem Zabs_Zmult : forall n m:Z, Zabs (n * m) = Zabs n * Zabs m.
Proof.
  intros z1 z2; case z1; case z2; simpl in |- *; auto.
Qed.

Theorem Zabs_square : forall a, Zabs a * Zabs a = a * a.
Proof.
  destruct a; simpl; auto.
Qed.

(** * Results about absolute value in nat. *)

Theorem inj_Zabs_nat : forall z:Z, Z_of_nat (Zabs_nat z) = Zabs z.
Proof.
  destruct z; simpl; auto; symmetry; apply Zpos_eq_Z_of_nat_o_nat_of_P.
Qed.

Theorem Zabs_nat_Z_of_nat: forall n, Zabs_nat (Z_of_nat n) = n.
Proof.
  destruct n; simpl; auto.
  apply nat_of_P_of_succ_nat.
Qed.

Lemma Zabs_nat_mult: forall n m:Z, Zabs_nat (n*m) = (Zabs_nat n * Zabs_nat m)%nat.
Proof.
  intros; apply inj_eq_rev.
  rewrite inj_mult; repeat rewrite inj_Zabs_nat; apply Zabs_Zmult.
Qed.

Lemma Zabs_nat_Zsucc:
 forall p, 0 <= p ->  Zabs_nat (Zsucc p) = S (Zabs_nat p).
Proof.
  intros; apply inj_eq_rev.
  rewrite inj_S; repeat rewrite inj_Zabs_nat, Zabs_eq; auto with zarith.
Qed.

Lemma Zabs_nat_Zplus:
 forall x y, 0<=x -> 0<=y -> Zabs_nat (x+y) = (Zabs_nat x + Zabs_nat y)%nat.
Proof.
  intros; apply inj_eq_rev.
  rewrite inj_plus; repeat rewrite inj_Zabs_nat, Zabs_eq; auto with zarith.
  apply Zplus_le_0_compat; auto.
Qed.

Lemma Zabs_nat_compare :
 forall x y, 0<=x -> 0<=y -> nat_compare (Zabs_nat x) (Zabs_nat y) = (x?=y).
Proof.
 intros. rewrite <- inj_compare, 2 inj_Zabs_nat, 2 Zabs_eq; trivial.
Qed.

Lemma Zabs_nat_le :
  forall n m:Z, 0 <= n <= m -> (Zabs_nat n <= Zabs_nat m)%nat.
Proof.
 intros n m (H,H'). apply nat_compare_le. rewrite Zabs_nat_compare; trivial.
 apply Zle_trans with n; auto.
Qed.

Lemma Zabs_nat_lt :
  forall n m:Z, 0 <= n < m -> (Zabs_nat n < Zabs_nat m)%nat.
Proof.
  intros n m (H,H'). apply nat_compare_lt. rewrite Zabs_nat_compare; trivial.
  apply Zlt_le_weak; apply Zle_lt_trans with n; auto.
Qed.

Lemma Zabs_nat_Zminus:
 forall x y, 0 <= x <= y ->  Zabs_nat (y - x) = (Zabs_nat y - Zabs_nat x)%nat.
Proof.
  intros x y (H,H').
  assert (0 <= y) by (apply Zle_trans with x; auto).
  assert (0 <= y-x) by (apply Zle_minus_le_0; auto).
  apply inj_eq_rev.
  rewrite inj_minus1. rewrite !inj_Zabs_nat, !Zabs_eq; auto.
  apply Zabs_nat_le. now split.
Qed.

(** * Some results about the sign function. *)

Lemma Zsgn_Zmult : forall a b, Zsgn (a*b) = Zsgn a * Zsgn b.
Proof.
  destruct a; destruct b; simpl; auto.
Qed.

Lemma Zsgn_Zopp : forall a, Zsgn (-a) = - Zsgn a.
Proof.
  destruct a; simpl; auto.
Qed.

(** A characterization of the sign function: *)

Lemma Zsgn_spec : forall x:Z,
  0 < x /\ Zsgn x = 1 \/
  0 = x /\ Zsgn x = 0 \/
  0 > x /\ Zsgn x = -1.
Proof.
 intros; unfold Zsgn, Zle, Zgt; destruct x; compute; intuition.
Qed.

Lemma Zsgn_pos : forall x:Z, Zsgn x = 1 <-> 0 < x.
Proof.
 destruct x; now intuition.
Qed.

Lemma Zsgn_neg : forall x:Z, Zsgn x = -1 <-> x < 0.
Proof.
 destruct x; now intuition.
Qed.

Lemma Zsgn_null : forall x:Z, Zsgn x = 0 <-> x = 0.
Proof.
 destruct x; now intuition.
Qed.

