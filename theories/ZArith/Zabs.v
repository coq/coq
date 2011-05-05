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

Local Open Scope Z_scope.

(**********************************************************************)
(** * Properties of absolute value *)

Notation Zabs_eq := Z.abs_eq (only parsing). (* 0 <= n -> Zabs n = n *)
Notation Zabs_non_eq := Z.abs_neq (only parsing). (* n <= 0 -> Zabs n = -n *)

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

(** Compatibility *)

Notation inj_Zabs_nat := Zabs2Nat.id_abs (only parsing).
Notation Zabs_nat_Z_of_nat := Zabs2Nat.id (only parsing).
Notation Zabs_nat_mult := Zabs2Nat.inj_mul (only parsing).
Notation Zabs_nat_Zsucc := Zabs2Nat.inj_succ (only parsing).
Notation Zabs_nat_Zplus := Zabs2Nat.inj_add (only parsing).
Notation Zabs_nat_Zminus := (fun n m => Zabs2Nat.inj_sub m n) (only parsing).
Notation Zabs_nat_compare := Zabs2Nat.inj_compare (only parsing).

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
