(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** This file axiomatizes the relational form of the axiom of choice *)

Axiom relational_choice :
  forall (A B : Type) (R : A->B->Prop),
   (forall x : A, exists y : B, R x y) ->
     exists R' : A->B->Prop, 
       subrelation R' R /\ forall x : A, exists! y : B, R' x y.
