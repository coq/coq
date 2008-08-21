(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Initialization code for typeclasses, setting up the default tactic 
   for instance search.

   Author: Matthieu Sozeau
   Institution: LRI, CNRS UMR 8623 - UniversitÃcopyright Paris Sud
   91405 Orsay, France *)

(* $Id$ *)

(* Ltac typeclass_instantiation := typeclasses eauto || eauto. *)

Tactic Notation "clapply" ident(c) :=
  eapply @c ; typeclasses eauto.

(** The unconvertible typeclass, to test that two objects of the same type are 
   actually different. *)

Class Unconvertible (A : Type) (a b : A).

Ltac unconvertible :=
  match goal with
    | |- @Unconvertible _ ?x ?y => conv x y ; fail 1 "Convertible"
    | |- _ => apply Build_Unconvertible 
  end.

Hint Extern 0 (@Unconvertible _ _ _) => unconvertible : typeclass_instances.