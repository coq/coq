(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Names
open Pp
open Tacexpr
open Termops

let (prtac, tactic_printer) = Hook.make ()
let (prmatchpatt, match_pattern_printer) = Hook.make ()
let (prmatchrl, match_rule_printer) = Hook.make ()


(* This module intends to be a beginning of debugger for tactic expressions.
   Currently, it is quite simple and we can hope to have, in the future, a more
   complete panel of commands dedicated to a proof assistant framework *)

(* Debug information *)
type debug_info =
  | DebugOn of int
  | DebugOff

(* An exception handler *)
let explain_logic_error = ref (fun e -> mt())

let explain_logic_error_no_anomaly = ref (fun e -> mt())

let msg_tac_debug s = Proofview.NonLogical.print (s++fnl())

(* Prints the goal *)

let db_pr_goal gl =
  let env = Proofview.Goal.env gl in
  let concl = Proofview.Goal.concl gl in
  let penv = print_named_context env in
  let pc = print_constr_env env concl in
    str"  " ++ hv 0 (penv ++ fnl () ++
                   str "============================" ++ fnl ()  ++
                   str" "  ++ pc) ++ fnl ()

let db_pr_goal =
  Proofview.Goal.nf_enter begin fun gl ->
  let pg = db_pr_goal gl in
  Proofview.tclLIFT (msg_tac_debug (str "Goal:" ++ fnl () ++ pg))
  end


(* Prints the commands *)
let help () =
  msg_tac_debug (str "Commands: <Enter> = Continue" ++ fnl() ++
         str "          h/? = Help" ++ fnl() ++
         str "          r <num> = Run <num> times" ++ fnl() ++
         str "          r <string> = Run up to next idtac <string>" ++ fnl() ++
         str "          s = Skip" ++ fnl() ++
         str "          x = Exit")

(* Prints the goal and the command to be executed *)
let goal_com tac =
  Proofview.tclTHEN
    db_pr_goal
    (Proofview.tclLIFT (msg_tac_debug (str "Going to execute:" ++ fnl () ++ Hook.get prtac tac)))

(* [run (new_ref _)] gives us a ref shared among [NonLogical.t]
   expressions. It avoids parametrizing everything over a
   reference. *)
let skipped = Proofview.NonLogical.run (Proofview.NonLogical.ref 0)
let skip = Proofview.NonLogical.run (Proofview.NonLogical.ref 0)
let breakpoint = Proofview.NonLogical.run (Proofview.NonLogical.ref None)

let rec drop_spaces inst i =
  if String.length inst > i && inst.[i] == ' ' then drop_spaces inst (i+1)
  else i

let possibly_unquote s =
  if String.length s >= 2 && s.[0] == '"' && s.[String.length s - 1] == '"' then
    String.sub s 1 (String.length s - 2)
  else
    s

(* (Re-)initialize debugger *)
let db_initialize =
  let open Proofview.NonLogical in
  (skip:=0) >> (skipped:=0) >> (breakpoint:=None)

let int_of_string s =
  try Proofview.NonLogical.return (int_of_string s)
  with e -> Proofview.NonLogical.raise e

let string_get s i =
  try Proofview.NonLogical.return (String.get s i)
  with e -> Proofview.NonLogical.raise e

(* Gives the number of steps or next breakpoint of a run command *)
let run_com inst =
  let open Proofview.NonLogical in
  string_get inst 0 >>= fun first_char ->
  if first_char ='r' then
    let i = drop_spaces inst 1 in
    if String.length inst > i then
      let s = String.sub inst i (String.length inst - i) in
      if inst.[0] >= '0' && inst.[0] <= '9' then
        int_of_string s >>= fun num ->
        (if num<0 then invalid_arg "run_com" else return ()) >>
        (skip:=num) >> (skipped:=0)
      else
        breakpoint:=Some (possibly_unquote s)
    else
      invalid_arg "run_com"
  else
    invalid_arg "run_com"

(* Prints the run counter *)
let run ini =
  let open Proofview.NonLogical in
  if not ini then
    begin
      Proofview.NonLogical.print (str"\b\r\b\r") >>
      !skipped >>= fun skipped ->
      msg_tac_debug (str "Executed expressions: " ++ int skipped ++ fnl())
    end >>
    !skipped >>= fun x ->
    skipped := x+1
  else
    return ()

(* Prints the prompt *)
let rec prompt level =
  (* spiwack: avoid overriding by the open below *)
  let runtrue = run true in
  begin
    let open Proofview.NonLogical in
    Proofview.NonLogical.print (fnl () ++ str "TcDebug (" ++ int level ++ str ") > ") >>
    let exit = (skip:=0) >> (skipped:=0) >> raise Sys.Break in
    Proofview.NonLogical.catch Proofview.NonLogical.read_line
      begin function (e, info) -> match e with
        | End_of_file -> exit
        | e -> raise ~info e
      end
    >>= fun inst ->
    match inst with
    | ""  -> return (DebugOn (level+1))
    | "s" -> return (DebugOff)
    | "x" -> Proofview.NonLogical.print_char '\b' >> exit
    | "h"| "?" ->
      begin
        help () >>
        prompt level
      end
    | _ ->
        Proofview.NonLogical.catch (run_com inst >> runtrue >> return (DebugOn (level+1)))
          begin function (e, info) -> match e with
            | Failure _ | Invalid_argument _ -> prompt level
            | e -> raise ~info e
          end
  end

(* Prints the state and waits for an instruction *)
(* spiwack: the only reason why we need to take the continuation [f]
   as an argument rather than returning the new level directly seems to
   be that [f] is wrapped in with "explain_logic_error". I don't think
   it serves any purpose in the current design, so we could just drop
   that. *)
let debug_prompt lev tac f =
  (* spiwack: avoid overriding by the open below *)
  let runfalse = run false in
  let open Proofview.NonLogical in
  let (>=) = Proofview.tclBIND in
  (* What to print and to do next *)
  let newlevel =
    Proofview.tclLIFT !skip >= fun initial_skip ->
    if Int.equal initial_skip 0 then
      Proofview.tclLIFT !breakpoint >= fun breakpoint ->
      if Option.is_empty breakpoint then Proofview.tclTHEN (goal_com tac) (Proofview.tclLIFT (prompt lev))
      else Proofview.tclLIFT(runfalse >> return (DebugOn (lev+1)))
    else Proofview.tclLIFT begin
      (!skip >>= fun s -> skip:=s-1) >>
      runfalse >>
      !skip >>= fun new_skip ->
      (if Int.equal new_skip 0 then skipped:=0 else return ()) >>
      return (DebugOn (lev+1))
    end in
  newlevel >= fun newlevel ->
  (* What to execute *)
  Proofview.tclOR
    (f newlevel)
    begin fun (reraise, info) ->
      Proofview.tclTHEN
        (Proofview.tclLIFT begin
          (skip:=0) >> (skipped:=0) >>
            if Logic.catchable_exception reraise then
              msg_tac_debug (str "Level " ++ int lev ++ str ": " ++ Pervasives.(!) explain_logic_error reraise)
            else return ()
        end)
        (Proofview.tclZERO ~info reraise)
    end

let is_debug db =
  let open Proofview.NonLogical in
  !breakpoint >>= fun breakpoint ->
  match db, breakpoint with
  | DebugOff, _ -> return false
  | _, Some _ -> return false
  | _ ->
      !skip >>= fun skip ->
      return (Int.equal skip 0)

(* Prints a constr *)
let db_constr debug env c =
  let open Proofview.NonLogical in
  is_debug debug >>= fun db ->
  if db then
    msg_tac_debug (str "Evaluated term: " ++ print_constr_env env c)
  else return ()

(* Prints the pattern rule *)
let db_pattern_rule debug num r =
  let open Proofview.NonLogical in
  is_debug debug >>= fun db ->
  if db then
  begin
    msg_tac_debug (str "Pattern rule " ++ int num ++ str ":" ++ fnl () ++
      str "|" ++ spc () ++ Hook.get prmatchrl r)
  end
  else return ()

(* Prints the hypothesis pattern identifier if it exists *)
let hyp_bound = function
  | Anonymous -> " (unbound)"
  | Name id -> " (bound to "^(Names.Id.to_string id)^")"

(* Prints a matched hypothesis *)
let db_matched_hyp debug env (id,_,c) ido =
  let open Proofview.NonLogical in
  is_debug debug >>= fun db ->
  if db then
    msg_tac_debug (str "Hypothesis " ++
           str ((Names.Id.to_string id)^(hyp_bound ido)^
                " has been matched: ") ++ print_constr_env env c)
  else return ()

(* Prints the matched conclusion *)
let db_matched_concl debug env c =
  let open Proofview.NonLogical in
  is_debug debug >>= fun db ->
  if db then
    msg_tac_debug (str "Conclusion has been matched: " ++ print_constr_env env c)
  else return ()

(* Prints a success message when the goal has been matched *)
let db_mc_pattern_success debug =
  let open Proofview.NonLogical in
  is_debug debug >>= fun db ->
  if db then
    msg_tac_debug (str "The goal has been successfully matched!" ++ fnl() ++
           str "Let us execute the right-hand side part..." ++ fnl())
  else return ()

(* Prints a failure message for an hypothesis pattern *)
let db_hyp_pattern_failure debug env sigma (na,hyp) =
  let open Proofview.NonLogical in
  is_debug debug >>= fun db ->
  if db then
    msg_tac_debug (str ("The pattern hypothesis"^(hyp_bound na)^
                " cannot match: ") ++
           Hook.get prmatchpatt env sigma hyp)
  else return ()

(* Prints a matching failure message for a rule *)
let db_matching_failure debug =
  let open Proofview.NonLogical in
  is_debug debug >>= fun db ->
  if db then
    msg_tac_debug (str "This rule has failed due to matching errors!" ++ fnl() ++
           str "Let us try the next one...")
  else return ()

(* Prints an evaluation failure message for a rule *)
let db_eval_failure debug s =
  let open Proofview.NonLogical in
  is_debug debug >>= fun db ->
  if db then
    let s = str "message \"" ++ s ++ str "\"" in
    msg_tac_debug
      (str "This rule has failed due to \"Fail\" tactic (" ++
       s ++ str ", level 0)!" ++ fnl() ++ str "Let us try the next one...")
  else return ()

(* Prints a logic failure message for a rule *)
let db_logic_failure debug err =
  let open Proofview.NonLogical in
  is_debug debug >>= fun db ->
  if db then
  begin
    msg_tac_debug (Pervasives.(!) explain_logic_error err) >>
    msg_tac_debug (str "This rule has failed due to a logic error!" ++ fnl() ++
           str "Let us try the next one...")
  end
  else return ()

let is_breakpoint brkname s = match brkname, s with
  | Some s, MsgString s'::_ -> String.equal s s'
  | _ -> false

let db_breakpoint debug s =
  let open Proofview.NonLogical in
  !breakpoint >>= fun opt_breakpoint ->
  match debug with
  | DebugOn lev when not (CList.is_empty s) && is_breakpoint opt_breakpoint s ->
      breakpoint:=None
  | _ ->
      return ()
