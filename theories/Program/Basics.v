(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
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

(** The polymorphic identity function is defined in [Datatypes]. *)

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
#[deprecated(since="8.16",note="Use Init.Datatypes.arrow instead.")]
Notation arrow := arrow.

(** Logical implication. *)

Definition impl (A B : Prop) : Prop := A -> B.

(** The constant function [const a] always returns [a]. *)

Definition const {A B} (a : A) := fun _ : B => a.

(** The [flip] combinator reverses the first two arguments of a function. *)
#[deprecated(since="8.16",note="Use Init.Datatypes.flip instead.")]
Notation flip := flip.

(** Application as a combinator. *)

Definition apply {A B} (f : A -> B) (x : A) := f x.

(** Curryfication of [prod] is defined in [Logic.Datatypes]. *)

Arguments prod_curry_subdef   {A B C} f p.
Arguments prod_uncurry_subdef {A B C} f x y.
