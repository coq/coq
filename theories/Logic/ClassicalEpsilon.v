(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(************************************************************************)

(** This file provides classical logic and indefinite description under
    the form of Hilbert's epsilon operator *)

(** Hilbert's epsilon operator and classical logic implies
    excluded-middle in [Set] and leads to a classical world populated
    with non computable functions. It conflicts with the
    impredicativity of [Set] *)

Require Export Classical.
Require Import ChoiceFacts.

Set Implicit Arguments.

Axiom constructive_indefinite_description :
  forall (A : Type) (P : A->Prop),
    (exists x, P x) -> { x : A | P x }.

Lemma constructive_definite_description :
  forall (A : Type) (P : A->Prop),
    (exists! x, P x) -> { x : A | P x }.
Proof.
  intros; apply constructive_indefinite_description; firstorder.
Qed.

Theorem excluded_middle_informative : forall P:Prop, {P} + {~ P}.
Proof.
  apply
    (constructive_definite_descr_excluded_middle
      constructive_definite_description classic).
Qed.

Theorem classical_indefinite_description :
  forall (A : Type) (P : A->Prop), inhabited A ->
    { x : A | (exists x, P x) -> P x }.
Proof.
  intros A P i.
  destruct (excluded_middle_informative (exists x, P x)) as [Hex|HnonP].
  apply constructive_indefinite_description
    with (P:= fun x => (exists x, P x) -> P x).
  destruct Hex as (x,Hx).
    exists x; intros _; exact Hx.
  assert {x : A | True} as (a,_).
    apply constructive_indefinite_description with (P := fun _ : A => True).
    destruct i as (a); firstorder.
  firstorder.
Defined.

(** Hilbert's epsilon operator *)

Definition epsilon (A : Type) (i:inhabited A) (P : A->Prop) : A
  := proj1_sig (classical_indefinite_description P i).

Definition epsilon_spec (A : Type) (i:inhabited A) (P : A->Prop) :
  (exists x, P x) -> P (epsilon i P)
  := proj2_sig (classical_indefinite_description P i).

(** Open question: is classical_indefinite_description constructively
    provable from [relational_choice] and
    [constructive_definite_description] (at least, using the fact that
    [functional_choice] is provable from [relational_choice] and
    [unique_choice], we know that the double negation of
    [classical_indefinite_description] is provable (see
    [relative_non_contradiction_of_indefinite_desc]). *)

(** A proof that if [P] is inhabited, [epsilon a P] does not depend on
    the actual proof that the domain of [P] is inhabited
    (proof idea kindly provided by Pierre Castéran) *)

Lemma epsilon_inh_irrelevance :
   forall (A:Type) (i j : inhabited A) (P:A->Prop),
   (exists x, P x) -> epsilon i P = epsilon j P.
Proof.
 intros.
 unfold epsilon, classical_indefinite_description.
 destruct (excluded_middle_informative (exists x : A, P x)) as [|[]]; trivial.
Qed.

Opaque epsilon.

(** *** Weaker lemmas (compatibility lemmas) *)

Theorem choice :
  forall (A B : Type) (R : A->B->Prop),
    (forall x : A, exists y : B, R x y) ->
    (exists f : A->B, forall x : A, R x (f x)).
Proof.
  intros A B R H.
  exists (fun x => proj1_sig (constructive_indefinite_description _ (H x))).
  intro x.
  apply (proj2_sig (constructive_indefinite_description _ (H x))).
Qed.

