(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Ltac debugger interface; clients should register hooks to interact
   with their provided interface. *)

(** The debugger receives requests by calling read_cmd to get Actions.
 Each Action may return one or more responses as Answers by calling submit_answer.
 Many of them return a single Answer or no Answer, but a single step may generate any
 number of Outputs.

 Debugger initialization has the following steps:
 -> Rocq sends Answer.Init
 <- IDE sends zero or more initialization requests such as Action.UpdBpts
 <- IDE sends Action.Configd

 Stopping in the debugger generates Answer.Prompt and Answer.Goal messages,
 at which point the IDE will typically call GetStack and GetVars.  When the
 IDE sends with StepIn..Continue, the debugger will execute more code.  At
 that point, Rocq won't try to read more messages from the IDE until the
 debugger stops again or exits.
 *)
module Action : sig
  type t =
    | StepIn    (* execute a single step in the tactic *)
    | StepOver  (* execute steps until DB is back in the current stack frame *)
    | StepOut   (* execute steps until DB exits current stack frame *)
    | Continue  (* execute steps until a breakpoint or the debugger exits *)
    | Skip      (* legacy: continue execution with no further debugging *)
    | Interrupt (* exit the debugger *)
    | Help      (* legacy: print help text *)
    | UpdBpts of ((string * int) * bool) list
                (* sets or clears breakpoints.  Values are:
                   - absolute pathname of the the file
                   - byte offset in the UTF-8 representation of the file
                   - true to set, false to clear *)
    | Configd   (* "config done" - indicates that the debugger has been
                   configured, debugger does a Continue *)
    | GetStack  (* request the call stack, returned as Answer.Stack *)
    | GetVars of int
                (* request the variables defined for stack frame N,
                   returned as Answer.Vars.  0 is the topmost frame,
                   followed by 1,2,3, ... *)
    | RunCnt of int
                (* legacy: run for N steps *)
    | RunBreakpoint of string
                (* legacy: run until an idtac prints the string *)
    | Command of string
                (* legacy: user-typed command to the debugger *)
    | Failed    (* legacy: user command doesn't parse *)
    | Ignore    (* internal: do nothing, read another command *)

  (* XXX: Should be moved to the clients *)
  val parse : string -> (t, string) result
end

module Answer : sig
  type t =
    | Prompt of Pp.t (* output signalling the debugger has stopped
                        Should be printed as a prompt for user input,
                        e.g. in color without a newline at the end *)
    | Goal of Pp.t   (* goal for the current proof state *)
    | Output of Pp.t (* general output *)
    | Init           (* signals initialization of the debugger *)
    | Stack of (string * (string * int list) option) list
                     (* The call stack, starting from TOS.
                        Values are:
                        - description of the frame
                          (eg tactic name, line number, module)
                        - absolute pathname of the file
                        - array containing Loc.bp and Loc.ep of the
                          corresponding code *)
    | Vars of (string * Pp.t) list
                     (* The variable values for the specified stack
                        frame.  Values are variable name and variable value *)
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
