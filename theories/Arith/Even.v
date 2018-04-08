(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Nota : this file is OBSOLETE, and left only for compatibility.
    Please consider instead predicates [Nat.Even] and [Nat.Odd]
    and Boolean functions [Nat.even] and [Nat.odd]. *)

(** Here we define the predicates [even] and [odd] by mutual induction
    and we prove the decidability and the exclusion of those predicates.
    The main results about parity are proved in the module Div2. *)

Require Import PeanoNat.

Local Open Scope nat_scope.

Implicit Types m n : nat.


(** * Inductive definition of [even] and [odd] *)

Inductive even : nat -> Prop :=
  | even_O : even 0
  | even_S : forall n, odd n -> even (S n)
with odd : nat -> Prop :=
    odd_S : forall n, even n -> odd (S n).

Hint Constructors even: arith.
Hint Constructors odd: arith.

(** * Equivalence with predicates [Nat.Even] and [Nat.odd] *)

Lemma even_equiv : forall n, even n <-> Nat.Even n.
Proof.
 fix even_equiv 1.
 destruct n as [|[|n]]; simpl.
 - split; [now exists 0 | constructor].
 - split.
   + inversion_clear 1. inversion_clear H0.
   + now rewrite <- Nat.even_spec.
 - rewrite Nat.Even_succ_succ, <- even_equiv.
   split.
   + inversion_clear 1. now inversion_clear H0.
   + now do 2 constructor.
Qed.

Lemma odd_equiv : forall n, odd n <-> Nat.Odd n.
Proof.
 fix odd_equiv 1.
 destruct n as [|[|n]]; simpl.
 - split.
   + inversion_clear 1.
   + now rewrite <- Nat.odd_spec.
 - split; [ now exists 0 | do 2 constructor ].
 - rewrite Nat.Odd_succ_succ, <- odd_equiv.
   split.
   + inversion_clear 1. now inversion_clear H0.
   + now do 2 constructor.
Qed.

(** Basic facts *)

Lemma even_or_odd n : even n \/ odd n.
Proof.
  induction n.
  - auto with arith.
  - elim IHn; auto with arith.
Qed.

Lemma even_odd_dec n : {even n} + {odd n}.
Proof.
  induction n.
  - auto with arith.
  - elim IHn; auto with arith.
Defined.

Lemma not_even_and_odd n : even n -> odd n -> False.
Proof.
  induction n.
  - intros Ev Od. inversion Od.
  - intros Ev Od. inversion Ev. inversion Od. auto with arith.
Qed.


(** * Facts about [even] & [odd] wrt. [plus] *)

Ltac parity2bool :=
 rewrite ?even_equiv, ?odd_equiv, <- ?Nat.even_spec, <- ?Nat.odd_spec.

Ltac parity_binop_spec :=
 rewrite ?Nat.even_add, ?Nat.odd_add, ?Nat.even_mul, ?Nat.odd_mul.

Ltac parity_binop :=
 parity2bool; parity_binop_spec; unfold Nat.odd;
 do 2 destruct Nat.even; simpl; tauto.


Lemma even_plus_split n m :
  even (n + m) -> even n /\ even m \/ odd n /\ odd m.
Proof. parity_binop. Qed.

Lemma odd_plus_split n m :
  odd (n + m) -> odd n /\ even m \/ even n /\ odd m.
Proof. parity_binop. Qed.

Lemma even_even_plus n m : even n -> even m -> even (n + m).
Proof. parity_binop. Qed.

Lemma odd_plus_l n m : odd n -> even m -> odd (n + m).
Proof. parity_binop. Qed.

Lemma odd_plus_r n m : even n -> odd m -> odd (n + m).
Proof. parity_binop. Qed.

Lemma odd_even_plus n m : odd n -> odd m -> even (n + m).
Proof. parity_binop. Qed.

Lemma even_plus_aux n m :
    (odd (n + m) <-> odd n /\ even m \/ even n /\ odd m) /\
    (even (n + m) <-> even n /\ even m \/ odd n /\ odd m).
Proof. parity_binop. Qed.

Lemma even_plus_even_inv_r n m : even (n + m) -> even n -> even m.
Proof. parity_binop. Qed.

Lemma even_plus_even_inv_l n m : even (n + m) -> even m -> even n.
Proof. parity_binop. Qed.

Lemma even_plus_odd_inv_r n m : even (n + m) -> odd n -> odd m.
Proof. parity_binop. Qed.

Lemma even_plus_odd_inv_l n m : even (n + m) -> odd m -> odd n.
Proof. parity_binop. Qed.

Lemma odd_plus_even_inv_l n m : odd (n + m) -> odd m -> even n.
Proof. parity_binop. Qed.

Lemma odd_plus_even_inv_r n m : odd (n + m) -> odd n -> even m.
Proof. parity_binop. Qed.

Lemma odd_plus_odd_inv_l n m : odd (n + m) -> even m -> odd n.
Proof. parity_binop. Qed.

Lemma odd_plus_odd_inv_r n m : odd (n + m) -> even n -> odd m.
Proof. parity_binop. Qed.


(** * Facts about [even] and [odd] wrt. [mult] *)

Lemma even_mult_aux n m :
  (odd (n * m) <-> odd n /\ odd m) /\ (even (n * m) <-> even n \/ even m).
Proof. parity_binop. Qed.

Lemma even_mult_l n m : even n -> even (n * m).
Proof. parity_binop. Qed.

Lemma even_mult_r n m : even m -> even (n * m).
Proof. parity_binop. Qed.

Lemma even_mult_inv_r n m : even (n * m) -> odd n -> even m.
Proof. parity_binop. Qed.

Lemma even_mult_inv_l n m : even (n * m) -> odd m -> even n.
Proof. parity_binop. Qed.

Lemma odd_mult n m : odd n -> odd m -> odd (n * m).
Proof. parity_binop. Qed.

Lemma odd_mult_inv_l n m : odd (n * m) -> odd n.
Proof. parity_binop. Qed.

Lemma odd_mult_inv_r n m : odd (n * m) -> odd m.
Proof. parity_binop. Qed.

Hint Resolve
 even_even_plus odd_even_plus odd_plus_l odd_plus_r
 even_mult_l even_mult_r even_mult_l even_mult_r odd_mult : arith.
