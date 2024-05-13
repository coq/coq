(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open DebuggerTypes

val set_debug : bool -> unit

val get_debug : unit -> bool

val upd_bpts : ((string * int) * bool) list -> unit

val stop_in_debugger : Loc.t option -> bool

val action : DebugHook.Action.t ref

val get_sigma : unit -> Evd.evar_map

(* Comm module stuff *)

val init : unit -> unit

val isTerminal : unit -> bool

(*  Stacks and chunks

    Ltac1 and Ltac2 maintain stacks using their own private, inaccessible types.
    Stack chunks (in !top_chunk :: !chunk_stack) abstract the
    differences between the two types.  Each chunk can represent multiple
    stack entries.  chunk_stack is empty unless the overall call stack has
    both Ltac1 and Ltac2 parts, or (corner case) if the Ltac1 interpreter is
    invoked recursively.

    cur_loc is the location of the next code to be executed.  This value
    isn't present in top_chunk.  Note that the Ltac1 and Ltac2 stacks
    have entries containing

      (called function, Loc where the function was called)

    rather than more standard

      (called function, current loc within the function).

    fmt_stack adjusts for this.
*)

type chunk = {
  locs : Loc.t option list;
  stack_f : unit -> string list;
  vars_f : int -> db_vars_rty;
}

val empty_chunk : chunk

val read : unit -> DebugHook.Action.t

val show_exn_in_debugger : Exninfo.iexn -> Loc.t option -> unit

val format_stack : string option list -> Loc.t option list -> db_stack_rty

val pr_goals : unit -> unit

val push_top_chunk : unit -> unit

val set_top_chunk : chunk -> unit

val get_top_chunk : unit -> chunk

val pop_chunk : unit -> unit

val save_goals : Loc.t option -> (unit -> unit) -> 'a -> 'a Proofview.tactic

val save_in_history : chunk -> Loc.t option -> unit

val is_hidden_code : Loc.t option -> bool

val cur_loc : Loc.t option ref

val print_loc : string -> Loc.t option -> string

val in_history : unit -> bool

val set_in_ltac : bool -> unit

type export_goals_args = {
  sigma:    Evd.evar_map;
  goals:    Evar.t list;
  bgsigma:  Evd.evar_map;
  stack:    (Evar.t list * Evar.t list) list;
  show_diffs: bool;
}

val fwd_db_subgoals : (goal_flags -> export_goals_args option ->
                      Proof_diffs.goal_map_args option -> subgoals_rty) ref
