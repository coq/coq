(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Compatibility file for making the admit tactic act similar to Coq v8.4. In
8.4, [admit] created a new axiom; in 8.5, it just shelves the goal. This
compatibility definition is not in the Coq84.v file to avoid loading an
inconsistent axiom implicitly. *)

Axiom proof_admitted : False.
Ltac admit := clear; abstract case proof_admitted.
