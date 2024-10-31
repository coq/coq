(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(** Standard functions and combinators.

   Proofs about them require functional extensionality and can be found
   in [Combinators].

   Author: Matthieu Sozeau
   Institution: LRI, CNRS UMR 8623 - University Paris Sud
*)
Require Import Notations.
Require Import Logic.

(** The polymorphic identity function is defined in [Datatypes]. *)

Require Import Datatypes.
Arguments id {A} x.

(** Function composition. *)

Definition compose {A B C} (g : B -> C) (f : A -> B) :=
  fun x : A => g (f x).

#[global]
Hint Unfold compose : core.

Declare Scope program_scope.

Notation " g ∘ f " := (compose g f)
  (at level 40, left associativity) : program_scope.

Local Open Scope program_scope.

(** The non-dependent function space between [A] and [B]. *)

Definition arrow (A B : Type) := A -> B.
Register arrow as core.arrow.

(** Logical implication. *)

Definition impl (A B : Prop) : Prop := A -> B.
Register impl as core.impl.

(** The constant function [const a] always returns [a]. *)

Definition const {A B} (a : A) := fun _ : B => a.

(** The [flip] combinator reverses the first two arguments of a function. *)

Definition flip {A B C} (f : A -> B -> C) x y := f y x.
Register flip as core.flip.

(** Application as a combinator. *)

Definition apply {A B} (f : A -> B) (x : A) := f x.
