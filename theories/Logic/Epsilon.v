(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This file provides indefinite description under the form of
    Hilbert's epsilon operator; it does not assume classical logic. *)

Require Import ChoiceFacts.

Set Implicit Arguments.

(** Hilbert's epsilon: operator and specification in one statement *)

Axiom epsilon_statement :
  forall (A : Type) (P : A->Prop), inhabited A ->
    { x : A | (exists x, P x) -> P x }.

Lemma constructive_indefinite_description :
  forall (A : Type) (P : A->Prop),
    (exists x, P x) -> { x : A | P x }.
Proof.
  apply epsilon_imp_constructive_indefinite_description.
  exact epsilon_statement.
Qed.

Lemma small_drinkers'_paradox :
  forall (A:Type) (P:A -> Prop), inhabited A ->
    exists x, (exists x, P x) -> P x.
Proof.
  apply epsilon_imp_small_drinker.
  exact epsilon_statement.
Qed.

Theorem iota_statement :
  forall (A : Type) (P : A->Prop), inhabited A ->
  { x : A | (exists! x : A, P x) -> P x }.
Proof.
  intros; destruct epsilon_statement with (P:=P); firstorder.
Qed.

Lemma constructive_definite_description :
  forall (A : Type) (P : A->Prop),
    (exists! x, P x) -> { x : A | P x }.
Proof.
  apply iota_imp_constructive_definite_description.
  exact iota_statement.
Qed.

(** Hilbert's epsilon operator and its specification *)

Definition epsilon (A : Type) (i:inhabited A) (P : A->Prop) : A
  := proj1_sig (epsilon_statement P i).

Definition epsilon_spec (A : Type) (i:inhabited A) (P : A->Prop) :
  (exists x, P x) -> P (epsilon i P)
  := proj2_sig (epsilon_statement P i).

(** Church's iota operator and its specification *)

Definition iota (A : Type) (i:inhabited A) (P : A->Prop) : A
  := proj1_sig (iota_statement P i).

Definition iota_spec (A : Type) (i:inhabited A) (P : A->Prop) :
  (exists! x:A, P x) -> P (iota i P)
  := proj2_sig (iota_statement P i).

