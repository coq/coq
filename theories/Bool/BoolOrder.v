(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The order relations [le] [lt] and [compare] are defined in [Bool.v] *)

(** Order properties of [bool]  *)

Require Export Bool.
Require Import Orders.
Import BoolNotations.
Local Ltac Tauto.intuition_solver ::= auto with typeclass_instances relations.

(** * Order [le] *)

Lemma le_refl : forall b, b <= b.
Proof. destr_bool. Qed.

Lemma le_trans : forall b1 b2 b3,
  b1 <= b2 -> b2 <= b3 -> b1 <= b3.
Proof. destr_bool. Qed.

Lemma le_true : forall b, b <= true.
Proof. destr_bool. Qed.

Lemma false_le : forall b, false <= b.
Proof. intros; constructor. Qed.

#[global]
Instance le_compat : Proper (eq ==> eq ==> iff) Bool.le.
Proof. intuition. Qed.

(** * Strict order [lt] *)

Lemma lt_irrefl : forall b, ~ b < b.
Proof. destr_bool; auto. Qed.

Lemma lt_trans : forall b1 b2 b3,
  b1 < b2 -> b2 < b3 -> b1 < b3.
Proof. destr_bool; auto. Qed.

#[global]
Instance lt_compat : Proper (eq ==> eq ==> iff) Bool.lt.
Proof. intuition. Qed.

Lemma lt_trichotomy : forall b1 b2, { b1 < b2 } + { b1 = b2 } + { b2 < b1 }.
Proof. destr_bool; auto. Qed.

Lemma lt_total : forall b1 b2, b1 < b2 \/ b1 = b2 \/ b2 < b1.
Proof. destr_bool; auto. Qed.

Lemma lt_le_incl : forall b1 b2, b1 < b2 -> b1 <= b2.
Proof. destr_bool; auto. Qed.

Lemma le_lteq_dec : forall b1 b2, b1 <= b2 -> { b1 < b2 } + { b1 = b2 }.
Proof. destr_bool; auto. Qed.

Lemma le_lteq : forall b1 b2, b1 <= b2 <-> b1 < b2 \/ b1 = b2.
Proof. destr_bool; intuition. Qed.


(** * Order structures *)

(* Class structure *)
#[global]
Instance le_preorder : PreOrder Bool.le.
Proof.
split.
- intros b; apply le_refl.
- intros b1 b2 b3; apply le_trans.
Qed.

#[global]
Instance lt_strorder : StrictOrder Bool.lt.
Proof.
split.
- intros b; apply lt_irrefl.
- intros b1 b2 b3; apply lt_trans.
Qed.

(* Module structure *)
Module BoolOrd <: UsualDecidableTypeFull <: OrderedTypeFull <: TotalOrder.
  Definition t := bool.
  Definition eq := @eq bool.
  Definition eq_equiv := @eq_equivalence bool.
  Definition lt := Bool.lt.
  Definition lt_strorder := lt_strorder.
  Definition lt_compat := lt_compat.
  Definition le := Bool.le.
  Definition le_lteq := le_lteq.
  Definition lt_total := lt_total.
  Definition compare := Bool.compare.
  Definition compare_spec := compare_spec.
  Definition eq_dec := bool_dec.
  Definition eq_refl := @eq_Reflexive bool.
  Definition eq_sym := @eq_Symmetric bool.
  Definition eq_trans := @eq_Transitive bool.
  Definition eqb := eqb.
  Definition eqb_eq := eqb_true_iff.
End BoolOrd.
