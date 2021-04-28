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
