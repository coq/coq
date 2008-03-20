(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Standard functions and combinators.
 * Proofs about them require functional extensionality and can be found in [Combinators].
 *
 * Author: Matthieu Sozeau
 * Institution: LRI, CNRS UMR 8623 - UniversitÃcopyright Paris Sud
 *              91405 Orsay, France *)

(* $Id: FSetAVL_prog.v 616 2007-08-08 12:28:10Z msozeau $ *)

(** The polymorphic identity function. *)

Definition id {A} := fun x : A => x.

(** Function composition. *)

Definition compose {A B C} (g : B -> C) (f : A -> B) := fun x : A => g (f x).

Hint Unfold compose.

Notation " g ∘ f " := (compose g f)  (at level 50, left associativity) : program_scope.

Open Local Scope program_scope.

(** [arrow A B] represents the non-dependent function space between [A] and [B]. *)

Definition arrow (A B : Type) := A -> B.

(** [impl A B] represents the logical implication of [B] by [A]. *)

Definition impl (A B : Prop) : Prop := A -> B.

(** The constant function [const a] always returns [a]. *)

Definition const {A B} (a : A) := fun _ : B => a.

(** The [flip] combinator reverses the first two arguments of a function. *)

Definition flip {A B C} (f : A -> B -> C) x y := f y x.

(** [apply f x] simply applies [f] to [x]. *)

Definition apply {A B} (f : A -> B) (x : A) := f x.

(** Curryfication of [prod] is defined in [Logic.Datatypes]. *)

Implicit Arguments prod_curry [[A] [B] [C]].
Implicit Arguments prod_uncurry [[A] [B] [C]].
