(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*i $Id$ i*)

(** Binary Integers (Pierre Crégut (CNET, Lannion, France) *)

Require Import Arith_base.
Require Import BinPos.
Require Import BinInt.
Require Import Zorder.
Require Import ZArith_dec.

Open Local Scope Z_scope.

(**********************************************************************)
(** * Properties of absolute value *)

Lemma Zabs_eq : forall n:Z, 0 <= n -> Zabs n = n.
Proof.
  intro x; destruct x; auto with arith.
  compute in |- *; intros; absurd (Gt = Gt); trivial with arith.
Qed.

Lemma Zabs_non_eq : forall n:Z, n <= 0 -> Zabs n = - n.
Proof.
  intro x; destruct x; auto with arith.
  compute in |- *; intros; absurd (Gt = Gt); trivial with arith.
Qed.

Theorem Zabs_Zopp : forall n:Z, Zabs (- n) = Zabs n.
Proof.
  intros z; case z; simpl in |- *; auto.
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

(** * A characterization of the sign function: *)

Lemma Zsgn_spec : forall x:Z, 
  0 < x /\ Zsgn x = 1 \/ 
  0 = x /\ Zsgn x = 0 \/ 
  0 > x /\ Zsgn x = -1.
Proof. 
 intros; unfold Zsgn, Zle, Zgt; destruct x; compute; intuition.
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

(** * Absolute value in nat is compatible with order *)

Lemma Zabs_nat_lt :
  forall n m:Z, 0 <= n /\ n < m -> (Zabs_nat n < Zabs_nat m)%nat.
Proof.
  intros x y. case x; simpl in |- *. case y; simpl in |- *.

  intro. absurd (0 < 0). compute in |- *. intro H0. discriminate H0. intuition.
  intros. elim (ZL4 p). intros. rewrite H0. auto with arith.
  intros. elim (ZL4 p). intros. rewrite H0. auto with arith.
  
  case y; simpl in |- *.
  intros. absurd (Zpos p < 0). compute in |- *. intro H0. discriminate H0. intuition.
  intros. change (nat_of_P p > nat_of_P p0)%nat in |- *.
  apply nat_of_P_gt_Gt_compare_morphism.
  elim H; auto with arith. intro. exact (ZC2 p0 p).

  intros. absurd (Zpos p0 < Zneg p).
  compute in |- *. intro H0. discriminate H0. intuition.

  intros. absurd (0 <= Zneg p). compute in |- *. auto with arith. intuition.
Qed.
