(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open EConstr
open Tacticals
open Tactypes

(** Eliminations tactics. *)

val introCaseAssumsThen : Tactics.evars_flag ->
  (intro_patterns -> branch_assumptions -> unit Proofview.tactic) ->
    branch_args -> unit Proofview.tactic

val h_decompose       : inductive list -> constr -> unit Proofview.tactic
val h_decompose_or    : constr -> unit Proofview.tactic
val h_decompose_and   : constr -> unit Proofview.tactic
val h_double_induction : quantified_hypothesis -> quantified_hypothesis-> unit Proofview.tactic
