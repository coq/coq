(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This file axiomatizes proof-irrelevance and derives some consequences *)

Require Import ProofIrrelevanceFacts.

Axiom proof_irrelevance : forall (P:Prop) (p1 p2:P), p1 = p2.

Register proof_irrelevance as core.proof_irrelevance.

Module PI. Definition proof_irrelevance := proof_irrelevance. End PI.

Module ProofIrrelevanceTheory := ProofIrrelevanceTheory(PI).
Export ProofIrrelevanceTheory.
