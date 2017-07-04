(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** This module states propositional extensionality and draws
    consequences of it *)

Axiom propositional_extensionality :
  forall (P Q : Prop), (P <-> Q) -> P = Q.

Require Import ClassicalFacts.

Theorem proof_irrelevance : forall (P:Prop) (p1 p2:P), p1 = p2.
Proof.
  apply ext_prop_dep_proof_irrel_cic.
  exact propositional_extensionality.
Qed.

