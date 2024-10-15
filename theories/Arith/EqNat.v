(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import PeanoNat.
Local Open Scope nat_scope.

(** Equality on natural numbers *)

(** * Propositional equality  *)

Fixpoint eq_nat n m : Prop :=
  match n, m with
    | O, O => True
    | O, S _ => False
    | S _, O => False
    | S n1, S m1 => eq_nat n1 m1
  end.

Theorem eq_nat_refl n : eq_nat n n.
Proof.
  induction n; simpl; auto.
Qed.

(** [eq] restricted to [nat] and [eq_nat] are equivalent *)

Theorem eq_nat_is_eq n m : eq_nat n m <-> n = m.
Proof.
  split.
  - revert m; induction n; intro m; destruct m; simpl; contradiction || auto.
  - intros <-; apply eq_nat_refl.
Qed.

Lemma eq_eq_nat n m : n = m -> eq_nat n m.
Proof.
 apply eq_nat_is_eq.
Qed.

Lemma eq_nat_eq n m : eq_nat n m -> n = m.
Proof.
 apply eq_nat_is_eq.
Qed.

Theorem eq_nat_elim :
  forall n (P:nat -> Prop), P n -> forall m, eq_nat n m -> P m.
Proof.
  intros n P ? m ?; replace m with n; [ | apply eq_nat_eq ]; assumption.
Qed.

Theorem eq_nat_decide : forall n m, {eq_nat n m} + {~ eq_nat n m}.
Proof.
  intro n; induction n as [|n IHn]; intro m; destruct m; simpl.
  - left; trivial.
  - right; intro; trivial.
  - right; intro; trivial.
  - apply IHn.
Defined.
