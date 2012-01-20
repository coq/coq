(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Constrextern
open Pp
open Tacexpr
open Termops

let prtac = ref (fun _ -> assert false)
let set_tactic_printer f = prtac := f
let prmatchpatt = ref (fun _ _ -> assert false)
let set_match_pattern_printer f = prmatchpatt := f
let prmatchrl = ref (fun _ -> assert false)
let set_match_rule_printer f = prmatchrl := f

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

(* Prints the goal *)

let db_pr_goal g =
  let env = Refiner.pf_env g in
  let penv = print_named_context env in
  let pc = print_constr_env env (Goal.V82.concl (Refiner.project g) (Refiner.sig_it g)) in
  str"  " ++ hv 0 (penv ++ fnl () ++
                   str "============================" ++ fnl ()  ++
                   str" "  ++ pc) ++ fnl ()

let db_pr_goal g =
  msgnl (str "Goal:" ++ fnl () ++ db_pr_goal g)


(* Prints the commands *)
let help () =
  msgnl (str "Commands: <Enter> = Continue" ++ fnl() ++
         str "          h/? = Help" ++ fnl() ++
         str "          r <num> = Run <num> times" ++ fnl() ++
         str "          r <string> = Run up to next idtac <string>" ++ fnl() ++
         str "          s = Skip" ++ fnl() ++
         str "          x = Exit")

(* Prints the goal and the command to be executed *)
let goal_com g tac =
  begin
    db_pr_goal g;
    msg (str "Going to execute:" ++ fnl () ++ !prtac tac ++ fnl ())
  end

let skipped = ref 0
let skip = ref 0
let breakpoint = ref None

let rec drop_spaces inst i =
  if String.length inst > i && inst.[i] = ' ' then drop_spaces inst (i+1)
  else i

let possibly_unquote s =
  if String.length s >= 2 & s.[0] = '"' & s.[String.length s - 1] = '"' then
    String.sub s 1 (String.length s - 2)
  else
    s

(* (Re-)initialize debugger *)
let db_initialize () =
  skip:=0;skipped:=0;breakpoint:=None

(* Gives the number of steps or next breakpoint of a run command *)
let run_com inst =
  if (String.get inst 0)='r' then
    let i = drop_spaces inst 1 in
    if String.length inst > i then
      let s = String.sub inst i (String.length inst - i) in
      if inst.[0] >= '0' && inst.[0] <= '9' then
        let num = int_of_string s in
        if num<0 then raise (Invalid_argument "run_com");
        skip:=num;skipped:=0
      else
        breakpoint:=Some (possibly_unquote s)
    else
      raise (Invalid_argument "run_com")
  else
    raise (Invalid_argument "run_com")

(* Prints the run counter *)
let run ini =
  if not ini then
  begin
    for i=1 to 2 do
      print_char (Char.chr 8);print_char (Char.chr 13)
    done;
    msg (str "Executed expressions: " ++ int !skipped ++ fnl() ++ fnl())
  end;
  incr skipped

(* Prints the prompt *)
let rec prompt level =
  begin
    msg (fnl () ++ str "TcDebug (" ++ int level ++ str ") > ");
    flush stdout;
    let exit () = skip:=0;skipped:=0;raise Sys.Break in
    let inst = try read_line () with End_of_file -> exit () in
    match inst with
    | ""  -> DebugOn (level+1)
    | "s" -> DebugOff
    | "x" -> print_char (Char.chr 8); exit ()
    | "h"| "?" ->
      begin
        help ();
        prompt level
      end
    | _ ->
      (try run_com inst;run true;DebugOn (level+1)
       with Failure _ | Invalid_argument _ -> prompt level)
  end

(* Prints the state and waits for an instruction *)
let debug_prompt lev g tac f =
  (* What to print and to do next *)
  let newlevel =
    if !skip = 0 then
      if !breakpoint = None then (goal_com g tac; prompt lev)
      else (run false; DebugOn (lev+1))
    else (decr skip; run false; if !skip=0 then skipped:=0; DebugOn (lev+1)) in
  (* What to execute *)
  try f newlevel
  with e ->
    skip:=0; skipped:=0;
    if Logic.catchable_exception e then
      ppnl (str "Level " ++ int lev ++ str ": " ++ !explain_logic_error e);
    raise e

(* Prints a constr *)
let db_constr debug env c =
  if debug <> DebugOff & !skip = 0 & !breakpoint = None then
    msgnl (str "Evaluated term: " ++ print_constr_env env c)

(* Prints the pattern rule *)
let db_pattern_rule debug num r =
  if debug <> DebugOff & !skip = 0 & !breakpoint = None then
  begin
    msgnl (str "Pattern rule " ++ int num ++ str ":");
    msgnl (str "|" ++ spc () ++ !prmatchrl r)
  end

(* Prints the hypothesis pattern identifier if it exists *)
let hyp_bound = function
  | Anonymous -> " (unbound)"
  | Name id -> " (bound to "^(Names.string_of_id id)^")"

(* Prints a matched hypothesis *)
let db_matched_hyp debug env (id,_,c) ido =
  if debug <> DebugOff & !skip = 0 & !breakpoint = None then
    msgnl (str "Hypothesis " ++
           str ((Names.string_of_id id)^(hyp_bound ido)^
                " has been matched: ") ++ print_constr_env env c)

(* Prints the matched conclusion *)
let db_matched_concl debug env c =
  if debug <> DebugOff & !skip = 0 & !breakpoint = None then
    msgnl (str "Conclusion has been matched: " ++ print_constr_env env c)

(* Prints a success message when the goal has been matched *)
let db_mc_pattern_success debug =
  if debug <> DebugOff & !skip = 0 & !breakpoint = None then
    msgnl (str "The goal has been successfully matched!" ++ fnl() ++
           str "Let us execute the right-hand side part..." ++ fnl())

(* Prints a failure message for an hypothesis pattern *)
let db_hyp_pattern_failure debug env (na,hyp) =
  if debug <> DebugOff & !skip = 0 & !breakpoint = None then
    msgnl (str ("The pattern hypothesis"^(hyp_bound na)^
                " cannot match: ") ++
           !prmatchpatt env hyp)

(* Prints a matching failure message for a rule *)
let db_matching_failure debug =
  if debug <> DebugOff & !skip = 0 & !breakpoint = None then
    msgnl (str "This rule has failed due to matching errors!" ++ fnl() ++
           str "Let us try the next one...")

(* Prints an evaluation failure message for a rule *)
let db_eval_failure debug s =
  if debug <> DebugOff & !skip = 0 & !breakpoint = None then
    let s = str "message \"" ++ s ++ str "\"" in
    msgnl
      (str "This rule has failed due to \"Fail\" tactic (" ++
       s ++ str ", level 0)!" ++ fnl() ++ str "Let us try the next one...")

(* Prints a logic failure message for a rule *)
let db_logic_failure debug err =
  if debug <> DebugOff & !skip = 0 & !breakpoint = None then
  begin
    msgnl (!explain_logic_error err);
    msgnl (str "This rule has failed due to a logic error!" ++ fnl() ++
           str "Let us try the next one...")
  end

let is_breakpoint brkname s = match brkname, s with
  | Some s, MsgString s'::_ -> s = s'
  | _ -> false

let db_breakpoint debug s =
  match debug with
  | DebugOn lev when s <> [] & is_breakpoint !breakpoint s ->
      breakpoint:=None
  | _ ->
      ()
