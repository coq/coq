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
Require ChoiceFacts.

Theorem choice : 
 (A:Type;B:Type;R: A->B->Prop)
  ((x:A)(EX y:B|(R x y))) -> (EX f:A->B | (x:A)(R x (f x))).
Proof.
Apply description_rel_choice_imp_funct_choice.
Exact description.
Exact relational_choice.
Qed.
