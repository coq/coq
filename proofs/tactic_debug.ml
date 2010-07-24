(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

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
  msgnl (str "Goal:" ++ fnl () ++ Proof_trees.db_pr_goal (Refiner.sig_it g))

(* Prints the commands *)
let help () =
  msgnl (str "Commands: <Enter>=Continue" ++ fnl() ++
         str "          h/?=Help" ++ fnl() ++
         str "          r<num>=Run <num> times" ++ fnl() ++
         str "          s=Skip" ++ fnl() ++
         str "          x=Exit")

(* Prints the goal and the command to be executed *)
let goal_com g tac =
  begin
    db_pr_goal g;
    msg (str "Going to execute:" ++ fnl () ++ !prtac tac ++ fnl ())
  end

(* Gives the number of a run command *)
let run_com inst =
  if (String.get inst 0)='r' then
    let num = int_of_string (String.sub inst 1 ((String.length inst)-1)) in
    if num>0 then num
    else raise (Invalid_argument "run_com")
  else
    raise (Invalid_argument "run_com")

let allskip = ref 0
let skip = ref 0

(* Prints the run counter *)
let run ini =
  if not ini then
    for i=1 to 2 do
      print_char (Char.chr 8);print_char (Char.chr 13)
    done;
  msg (str "Executed expressions: " ++ int (!allskip - !skip) ++
       fnl() ++ fnl())

(* Prints the prompt *)
let rec prompt level =
  begin
    msg (fnl () ++ str "TcDebug (" ++ int level ++ str ") > ");
    flush stdout;
    let exit () = skip:=0;allskip:=0;raise Sys.Break in
    let inst = try read_line () with End_of_file -> exit () in
    match inst with
    | ""  -> true
    | "s" -> false
    | "x" -> print_char (Char.chr 8); exit ()
    | "h"| "?" ->
      begin
        help ();
        prompt level
      end
    | _ ->
      (try let ctr=run_com inst in skip:=ctr;allskip:=ctr;run true;true
       with Failure _ | Invalid_argument _ -> prompt level)
  end

(* Prints the state and waits for an instruction *)
let debug_prompt lev g tac f =
  (* What to print and to do next *)
  let continue =
    if !skip = 0 then (goal_com g tac; prompt lev)
    else (decr skip; run false; if !skip=0 then allskip:=0; true) in
  (* What to execute *)
  try f (if continue then DebugOn (lev+1) else DebugOff)
  with e ->
    skip:=0; allskip:=0;
    if Logic.catchable_exception e then
      ppnl (str "Level " ++ int lev ++ str ": " ++ !explain_logic_error e);
    raise e

(* Prints a constr *)
let db_constr debug env c =
  if debug <> DebugOff & !skip = 0 then
    msgnl (str "Evaluated term: " ++ print_constr_env env c)

(* Prints the pattern rule *)
let db_pattern_rule debug num r =
  if debug <> DebugOff & !skip = 0 then
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
  if debug <> DebugOff & !skip = 0 then
    msgnl (str "Hypothesis " ++
           str ((Names.string_of_id id)^(hyp_bound ido)^
                " has been matched: ") ++ print_constr_env env c)

(* Prints the matched conclusion *)
let db_matched_concl debug env c =
  if debug <> DebugOff & !skip = 0 then
    msgnl (str "Conclusion has been matched: " ++ print_constr_env env c)

(* Prints a success message when the goal has been matched *)
let db_mc_pattern_success debug =
  if debug <> DebugOff & !skip = 0 then
    msgnl (str "The goal has been successfully matched!" ++ fnl() ++
           str "Let us execute the right-hand side part..." ++ fnl())

let pp_match_pattern env = function
  | Term c -> Term (extern_constr_pattern (names_of_rel_context env) c)
  | Subterm (b,o,c) ->
    Subterm (b,o,(extern_constr_pattern (names_of_rel_context env) c))

(* Prints a failure message for an hypothesis pattern *)
let db_hyp_pattern_failure debug env (na,hyp) =
  if debug <> DebugOff & !skip = 0 then
    msgnl (str ("The pattern hypothesis"^(hyp_bound na)^
                " cannot match: ") ++
           !prmatchpatt env hyp)

(* Prints a matching failure message for a rule *)
let db_matching_failure debug =
  if debug <> DebugOff & !skip = 0 then
    msgnl (str "This rule has failed due to matching errors!" ++ fnl() ++
           str "Let us try the next one...")

(* Prints an evaluation failure message for a rule *)
let db_eval_failure debug s =
  if debug <> DebugOff & !skip = 0 then
    let s = str "message \"" ++ s ++ str "\"" in
    msgnl
      (str "This rule has failed due to \"Fail\" tactic (" ++
       s ++ str ", level 0)!" ++ fnl() ++ str "Let us try the next one...")

(* Prints a logic failure message for a rule *)
let db_logic_failure debug err =
  if debug <> DebugOff & !skip = 0 then
  begin
    msgnl (!explain_logic_error err);
    msgnl (str "This rule has failed due to a logic error!" ++ fnl() ++
           str "Let us try the next one...")
  end
