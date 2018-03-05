(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This file axiomatizes proof-irrelevance and derives some consequences *)

Require Import ProofIrrelevanceFacts.

Axiom proof_irrelevance : forall (P:Prop) (p1 p2:P), p1 = p2.

Module PI. Definition proof_irrelevance := proof_irrelevance. End PI.

Module ProofIrrelevanceTheory := ProofIrrelevanceTheory(PI).
Export ProofIrrelevanceTheory.
