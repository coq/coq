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

val breakpoint_stop : Loc.t option -> bool

val stepping_stop : Loc.t option -> bool

val action : DebugHook.Action.t ref

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

type fmt_stack_f = unit -> string list
type fmt_vars_f = int -> db_vars_rty
type chunk = Loc.t option list * fmt_stack_f * fmt_vars_f  (* todo: record? *)
val empty_chunk : chunk

val read : unit -> DebugHook.Action.t

val format_stack : string option list -> Loc.t option list -> db_stack_rty

val db_pr_goals_t : unit Proofview.tactic

val db_pr_goals : unit -> unit

val pop_chunk : unit -> unit

val new_stop_point : unit -> unit

val save_goals : unit -> unit Proofview.tactic

val save_chunk : chunk -> Loc.t option -> unit

val set_top_chunk : chunk -> unit

val push_top_chunk : unit -> unit

val cur_loc : Loc.t option ref

val print_loc : string -> Loc.t option -> string

val in_history : unit -> bool
