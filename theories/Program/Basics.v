(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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

Hint Unfold compose.

Notation " g ∘ f " := (compose g f)
  (at level 40, left associativity) : program_scope.

Local Open Scope program_scope.

(** The non-dependent function space between [A] and [B]. *)

Definition arrow (A B : Type) := A -> B.

(** Logical implication. *)

Definition impl (A B : Prop) : Prop := A -> B.

(** The constant function [const a] always returns [a]. *)

Definition const {A B} (a : A) := fun _ : B => a.

(** The [flip] combinator reverses the first two arguments of a function. *)

Definition flip {A B C} (f : A -> B -> C) x y := f y x.

(** Application as a combinator. *)

Definition apply {A B} (f : A -> B) (x : A) := f x.

(** Curryfication of [prod] is defined in [Logic.Datatypes]. *)

Arguments prod_curry   {A B C} f p.
Arguments prod_uncurry {A B C} f x y.
