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
    | StepIn
    | StepOver
    | StepOut
    | Continue
    | Skip
    | Interrupt
    | Help
    | RunCnt of int
    | RunBreakpoint of string
    | Command of string
    | Failed
    | Ignore (* do nothing, read another command *)

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
    ; isTerminal : bool
    (** whether the debugger is running as a terminal (non-visual) *)
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
  (* next code to execute, is not in stack *)
  mutable cur_loc : Loc.t option;
  (* yields the call stack *)
  mutable get_stack : unit -> (string * Loc.t option) list;
  mutable varmaps : Geninterp.Val.t Names.Id.Map.t list;
}

val debugger_state : debugger_state
