(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This module states the functional form of the axiom of choice over
  setoids, commonly called extensional axiom of choice [[Carlström04]],
  [[Martin-Löf05]]. This is obtained by a decomposition of the axiom
  into the following components:

  - classical logic
  - relational axiom of choice
  - axiom of unique choice
  - a limited form of functional extensionality

  Among other results, it entails:
  - proof irrelevance
  - choice of a representative in equivalence classes

  [[Carlström04]] Jesper Carlström, EM + Ext_ + AC_int is equivalent to
  AC_ext, Mathematical Logic Quaterly, vol 50(3), pp 236-240, 2004.

  [[Martin-Löf05] Per Martin-Löf, 100 years of Zermelo’s axiom of
  choice: what was the problem with it?, lecture notes for KTH/SU
  colloquium, 2005.

*)

Require Export ClassicalChoice. (* classical logic, relational choice, unique choice *)
Require Export ExtensionalFunctionRepresentative.

Require Import ChoiceFacts.
Require Import ClassicalFacts.
Require Import RelationClasses.

Theorem setoid_choice :
  forall A B,
  forall R : A -> A -> Prop,
  forall T : A -> B -> Prop,
  Equivalence R ->
  (forall x x' y, R x x' -> T x y -> T x' y) ->
  (forall x, exists y, T x y) ->
  exists f : A -> B, forall x : A, T x (f x) /\ (forall x' : A, R x x' -> f x = f x').
Proof.
  apply setoid_functional_choice_first_characterization. split; [|split].
  - exact choice.
  - exact extensional_function_representative.
  - exact classic.
Qed.

Theorem representative_choice :
  forall A (R:A->A->Prop), (Equivalence R) ->
  exists f : A->A, forall x : A, R x (f x) /\ forall x', R x x' -> f x = f x'.
Proof.
  apply setoid_fun_choice_imp_repr_fun_choice.
  exact setoid_choice.
Qed.
