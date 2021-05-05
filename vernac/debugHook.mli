(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Ltac debugger interface; clients should register hooks to interact
   with their provided interface. *)
module Action : sig
  type t =
    | Step
    (** Step one tactic *)
    | Skip
    (** Skip one tactic *)
    | Exit
    | Help
    | RunCnt of int
    | RunBreakpoint of string
    | Failed

  (* XXX: Should be moved to the clients *)
  val parse : string -> (t, string) result
end

module Answer : sig
  type t =
    | Prompt of Pp.t
    | Goal of Pp.t
    | Output of Pp.t
end

module Intf : sig
  type t =
    { read_cmd : unit -> Action.t
    (** request a debugger command from the client *)
    ; submit_answer : Answer.t -> unit
    (** receive a debugger answer from Ltac *)
    }

  val set : t -> unit
  val get : unit -> t option
end

(** breakpoints as used by tactic_debug *)
type breakpoint = {
  dirpath : string;
  offset : int;
}

module BPSet : CSet.S with type elt = breakpoint

val breakpoints : BPSet.t ref

(** breakpoints as defined by the debugger IDE, using absolute file names *)
type ide_breakpoint = {
  file : string;
  offset : int;
}
module IBPSet : CSet.S with type elt = ide_breakpoint

val ide_breakpoints : IBPSet.t ref

val update_bpt : bool -> ide_breakpoint -> unit
val refresh_bpts : unit -> unit

type debugger_state = {
  mutable cur_loc : Loc.t option;
}

val debugger_state : debugger_state
