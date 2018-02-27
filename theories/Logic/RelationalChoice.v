(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This file axiomatizes the relational form of the axiom of choice *)

Axiom relational_choice :
  forall (A B : Type) (R : A->B->Prop),
   (forall x : A, exists y : B, R x y) ->
     exists R' : A->B->Prop,
       subrelation R' R /\ forall x : A, exists! y : B, R' x y.
