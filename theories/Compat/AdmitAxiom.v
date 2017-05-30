(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Compatibility file for making the admit tactic act similar to Coq v8.4. In
8.4, [admit] created a new axiom; in 8.5, it just shelves the goal. This
compatibility definition is not in the Coq84.v file to avoid loading an
inconsistent axiom implicitly. *)

Axiom proof_admitted : False.
Ltac admit := clear; abstract case proof_admitted.
