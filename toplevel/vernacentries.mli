(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term
open Vernacinterp
open Vernacexpr
open Topconstr

(** Vernacular entries *)

val show_script : unit -> unit
val show_prooftree : unit -> unit

val show_node : unit -> unit

(** This function can be used by any command that want to observe terms
   in the context of the current goal, as for instance in pcoq *)
val get_current_context_of_args : int option -> Evd.evar_map * Environ.env

(*i

(** this function is used to analyse the extra arguments in search commands.
   It is used in pcoq. *) (*i anciennement: inside_outside i*)
val interp_search_restriction : search_restriction -> dir_path list * bool
i*)

type pcoq_hook = {
  start_proof : unit -> unit;
  solve : int -> unit;
  abort : string -> unit;
  search : searchable -> dir_path list * bool -> unit;
  print_name : Libnames.reference Genarg.or_by_notation -> unit;
  print_check : Environ.env -> Environ.unsafe_judgment -> unit;
  print_eval : Reductionops.reduction_function -> Environ.env -> Evd.evar_map -> constr_expr ->
    Environ.unsafe_judgment -> unit;
  show_goal : goal_reference -> unit
}

val set_pcoq_hook : pcoq_hook -> unit

(** This function makes sure that the function given in argument is preceded
   by a command aborting all proofs if necessary.
   It is used in pcoq. *)
val abort_refine : ('a -> unit) -> 'a -> unit;;

val interp : Vernacexpr.vernac_expr -> unit

(** Print subgoals when the verbose flag is on.
    Meant to be used inside vernac commands from plugins. *)

val print_subgoals : unit -> unit

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
