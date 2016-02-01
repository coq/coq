(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** * Initialization code for typeclasses, setting up the default tactic
   for instance search.

   Author: Matthieu Sozeau
   Institution: LRI, CNRS UMR 8623 - University Paris Sud
*)

(** Hints for the proof search: these combinators should be considered rigid. *)

Require Import Coq.Program.Basics.

Typeclasses Opaque id const flip compose arrow impl not all.

(** Apply using the same opacity information as typeclass proof search. *)

Ltac class_apply c := autoapply c using typeclass_instances.

(** The unconvertible typeclass, to test that two objects of the same type are
   actually different. *)

Class Unconvertible (A : Type) (a b : A) := unconvertible : unit.

Ltac unconvertible :=
  match goal with
    | |- @Unconvertible _ ?x ?y => unify x y with typeclass_instances ; fail 1 "Convertible"
    | |- _ => exact tt
  end.

Hint Extern 0 (@Unconvertible _ _ _) => unconvertible : typeclass_instances.
