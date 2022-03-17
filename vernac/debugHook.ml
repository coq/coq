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
module Action = struct
  type t =
    | StepIn
    | StepInRev
    | StepOver
    | StepOverRev
    | StepOut
    | StepOutRev
    | Continue
    | ContinueRev
    | Skip
    | Interrupt
    | Help
    | UpdBpts of ((string * int) * bool) list
    | Configd
    | GetStack
    | GetVars of int
    | Subgoals of Interface.goal_flags
    | RunCnt of int
    | RunBreakpoint of string
    | Command of string
    | Failed
    | Ignore (* do nothing, read another command *)

  (* XXX: Could we move this to the CString utility library? *)
  let possibly_unquote s =
    if String.length s >= 2 && s.[0] == '"' && s.[String.length s - 1] == '"' then
      String.sub s 1 (String.length s - 2)
    else
      s

  let parse_complex inst : (t, string) result =
    if 'r' = String.get inst 0 then
      let arg = String.(trim (sub inst 1 (length inst - 1))) in
      if arg <> "" then
        match int_of_string_opt arg with
        | Some num ->
          if num < 0 then
            Error "number must be positive"
          else
            Ok (RunCnt num)
        | None ->
          Ok (RunBreakpoint (possibly_unquote arg))
      else
        Error ("invalid input: " ^ inst)
    else
      Error ("invalid input: " ^ inst)

  (* XXX: Should be moved to the clients *)
  let parse inst : (t, string) result =
    match inst with
    | ""  -> Ok StepIn
    | "s" -> Ok Skip
    | "x" -> Ok Interrupt
    | "h"| "?" -> Ok Help
    | _ -> parse_complex inst

  let to_string t =
    match t with
    | Continue -> "Continue"
    | ContinueRev -> "ContinueRev"
    | StepIn -> "StepIn"
    | StepInRev -> "StepInRev"
    | StepOver -> "StepOver"
    | StepOverRev -> "StepOverRev"
    | StepOut -> "StepOut"
    | StepOutRev -> "StepOutRev"
    | Skip -> "Skip"
    | Interrupt -> "Interrupt"
    | Help -> "Help"
    | UpdBpts _ -> "UpdBpts"
    | Configd -> "Configd"
    | GetStack -> "GetStack"
    | GetVars _ -> "GetVars"
    | Subgoals _ -> "Subgoals"
    | RunCnt _ -> "RunCnt"
    | RunBreakpoint _ -> "RunBreakpoint"
    | Command _ -> "Command"
    | Failed -> "Failed"
    | Ignore -> "Ignore"

end

module Answer = struct
  type stack = (string * (string * int list) option) list
  type vars = (string * Pp.t) list
  type t =
    | Prompt of Pp.t
    | Output of Pp.t
    | Init
    | Stack of stack
    | Vars of vars
    | Subgoals of Interface.goals_rty
end

module Intf = struct

  type t =
    { read_cmd : bool -> Action.t
    (** request a debugger command from the client.  true = in debugger *)
    ; submit_answer : Answer.t -> unit
    (** receive a debugger answer from Ltac *)
    ; isTerminal : bool
    (** whether the debugger is running as a terminal (non-visual) *)
    }

  let ltac_debug_ref : t option ref = ref None
  let set hooks = ltac_debug_ref := Some hooks
  let get () = !ltac_debug_ref

end

let fwd_db_subgoals = Interface.(ref ((fun x y -> failwith "fwd_db_subgoals")
                  : goal_flags -> (Evd.evar_map * Evar.t list) option -> subgoals_rty))

(* MOVE *)
(* for displaying goals when stopped in debugger (only sigma and goals) *)
let debug_proof = ref None

(* tells whether we're in the debugger or not *)
let set_in_debug in_debug =
  if not in_debug then debug_proof := None
