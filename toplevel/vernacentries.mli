(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Misctypes

val dump_global : Libnames.reference or_by_notation -> unit

(** Vernacular entries *)

val show_prooftree : unit -> unit

val show_node : unit -> unit

(** This function can be used by any command that want to observe terms
   in the context of the current goal *)
val get_current_context_of_args : int option -> Evd.evar_map * Environ.env

(** The main interpretation function of vernacular expressions *)
val interp : 
  ?verbosely:bool ->
  ?proof:Proof_global.closed_proof ->
    Loc.t * Vernacexpr.vernac_expr -> unit

(** Print subgoals when the verbose flag is on.
    Meant to be used inside vernac commands from plugins. *)

val print_subgoals : unit -> unit
val try_print_subgoals : unit -> unit

(** The printing of goals via [print_subgoals] or during
    [interp] can be controlled by the following flag.
    Used for instance by coqide, since it has its own
    goal-fetching mechanism. *)

val enable_goal_printing : bool ref

(** Should Qed try to display the proof script ?
    True by default, but false in ProofGeneral and coqIDE *)

val qed_display_script : bool ref

(** Prepare a "match" template for a given inductive type.
    For each branch of the match, we list the constructor name
    followed by enough pattern variables.
    [Not_found] is raised if the given string isn't the qualid of
    a known inductive type. *)

val make_cases : string -> string list list

val vernac_end_proof :
  ?proof:Proof_global.closed_proof -> Vernacexpr.proof_end -> unit

val with_fail : bool -> (unit -> unit) -> unit
