(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** This file provides classical logic and functional choice *)

(** This file extends ClassicalDescription.v with the axiom of choice.
    As ClassicalDescription.v, it implies the double-negation of
    excluded-middle in Set and implies a strongly classical
    world. Especially it conflicts with impredicativity of Set, knowing
    that true<>false in Set.
*)

Require Export ClassicalDescription.
Require Export RelationalChoice.
Require Import ChoiceFacts.

Theorem choice :
 forall (A B:Type) (R:A -> B -> Prop),
   (forall x:A,  exists y : B, R x y) ->
    exists f : A -> B, (forall x:A, R x (f x)).
Proof.
apply description_rel_choice_imp_funct_choice.
exact description.
exact relational_choice.
Qed.