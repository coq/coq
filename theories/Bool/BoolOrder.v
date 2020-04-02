(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
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

Local Notation le := Bool.leb.
Local Notation lt := Bool.ltb.
Local Notation compare := Bool.compareb.
Local Notation compare_spec := Bool.compareb_spec.

(** * Order [le] *)

Lemma le_refl : forall b, le b b.
Proof. destr_bool. Qed.

Lemma le_trans : forall b1 b2 b3,
  le b1 b2 -> le b2 b3 -> le b1 b3.
Proof. destr_bool. Qed.

Lemma le_true : forall b, le b true.
Proof. destr_bool. Qed.

Lemma false_le : forall b, le false b.
Proof. intros; constructor. Qed.

Instance le_compat : Proper (eq ==> eq ==> iff) le.
Proof. intuition. Qed.

(** * Strict order [lt] *)

Lemma lt_irrefl : forall b, ~ lt b b.
Proof. destr_bool; auto. Qed.

Lemma lt_trans : forall b1 b2 b3,
  lt b1 b2 -> lt b2 b3 -> lt b1 b3.
Proof. destr_bool; auto. Qed.

Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
Proof. intuition. Qed.

Lemma lt_trichotomy : forall b1 b2, { lt b1 b2 } + { b1 = b2 } + { lt b2 b1 }.
Proof. destr_bool; auto. Qed.

Lemma lt_total : forall b1 b2, lt b1 b2 \/ b1 = b2 \/ lt b2 b1.
Proof. destr_bool; auto. Qed.

Lemma lt_le_incl : forall b1 b2, lt b1 b2 -> le b1 b2.
Proof. destr_bool; auto. Qed.

Lemma le_lteq_dec : forall b1 b2, le b1 b2 -> { lt b1 b2 } + { b1 = b2 }.
Proof. destr_bool; auto. Qed.

Lemma le_lteq : forall b1 b2, le b1 b2 <-> lt b1 b2 \/ b1 = b2.
Proof. destr_bool; intuition. Qed.


(** * Order structures *)

(* Class structure *)
Instance le_preorder : PreOrder le.
Proof.
split.
- intros b; apply le_refl.
- intros b1 b2 b3; apply le_trans.
Qed.

Instance lt_strorder : StrictOrder lt.
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
  Definition lt := lt.
  Definition lt_strorder := lt_strorder.
  Definition lt_compat := lt_compat.
  Definition le := le.
  Definition le_lteq := le_lteq.
  Definition lt_total := lt_total.
  Definition compare := compare.
  Definition compare_spec := compare_spec.
  Definition eq_dec := bool_dec.
  Definition eq_refl := @eq_Reflexive bool.
  Definition eq_sym := @eq_Symmetric bool.
  Definition eq_trans := @eq_Transitive bool.
  Definition eqb := eqb.
  Definition eqb_eq := eqb_true_iff.
End BoolOrd.
