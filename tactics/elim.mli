(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open EConstr
open Tacticals
open Misctypes
open Tactypes

(** Eliminations tactics. *)

val introCaseAssumsThen : evars_flag ->
  (intro_patterns -> branch_assumptions -> unit Proofview.tactic) ->
    branch_args -> unit Proofview.tactic

val h_decompose       : inductive list -> constr -> unit Proofview.tactic
val h_decompose_or    : constr -> unit Proofview.tactic
val h_decompose_and   : constr -> unit Proofview.tactic
val h_double_induction : quantified_hypothesis -> quantified_hypothesis-> unit Proofview.tactic
