(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

open Ast
open Names
open Constrextern
open Pp
open Pptactic
open Printer
open Tacexpr
open Termops

(* This module intends to be a beginning of debugger for tactic expressions.
   Currently, it is quite simple and we can hope to have, in the future, a more
   complete panel of commands dedicated to a proof assistant framework *)

(* Debug information *)
type debug_info =
  | DebugOn
  | DebugOff
  | Run of int

(* Prints the goal *)
let db_pr_goal g =
  msgnl (str "Goal:" ++ fnl () ++ Proof_trees.pr_goal (Tacmach.sig_it g))

(* Prints the commands *)
let help () =
  msgnl (str "Commands: <Enter>=Continue" ++ fnl() ++
         str "          h/?=Help" ++ fnl() ++
         str "          r<num>=Run <num> times" ++ fnl() ++
         str "          s=Skip" ++ fnl() ++
         str "          x=Exit")

(* Prints the goal and the command to be executed *)
let goal_com g tac_ast =
  begin
    db_pr_goal g;
    msg (str "Going to execute:" ++ fnl () ++ (pr_glob_tactic tac_ast) ++
         fnl ())
  end

(* Gives the number of a run command *)
let run_com inst =
  if (String.get inst 0)='r' then
    let num = int_of_string (String.sub inst 1 ((String.length inst)-1)) in
    if num>0 then num
    else raise (Invalid_argument "run_com")
  else
    raise (Invalid_argument "run_com")

(* Prints the run counter *)
let run ini ctr =
  if ini then msg (str "Executed expressions: 0" ++ fnl() ++ fnl())
  else
  begin
    for i=1 to 2 do
      print_char (Char.chr 8);print_char (Char.chr 13)
    done;
    msg (str "Executed expressions: " ++ int ctr ++ fnl() ++ fnl())
  end

(* Prints the prompt *)
let rec prompt () =
  begin
    msg (fnl () ++ str "TcDebug > ");
    flush stdout;
    let inst = read_line () in
    match inst with
    | ""  -> DebugOn
    | "s" -> DebugOff
    | "x" -> print_char (Char.chr 8);raise Sys.Break
    | "h"| "?" ->
      begin
        help ();
        prompt ()
      end
    | _ ->
      (try let ctr=run_com inst in run true ctr;Run ctr
       with Failure _ | Invalid_argument _ -> prompt ())
  end

(* Prints the whole state *)
let state g tac_ast ctr =
  begin
    goal_com g tac_ast;
    let debug = prompt () in
    match debug with
    | Run n -> ctr := 0;debug
    | _ -> debug
  end

(* Prints the state and waits for an instruction *)
let debug_prompt =
  let ctr = ref 0 in
  fun g debug tac_ast ->
  match debug with
  | Run n ->
    if !ctr=n then state g tac_ast ctr
    else (incr ctr;run false !ctr;debug)
  | _ -> state g tac_ast ctr

(* Prints a constr *)
let db_constr debug env c =
  if debug <> DebugOff then
    msgnl (str "Evaluated term: " ++ prterm_env env c)

(* Prints the pattern rule *)
let db_pattern_rule debug num r =
  if debug = DebugOn then
  begin
    msgnl (str "Pattern rule " ++ int num ++ str ":");
    msgnl (str "|" ++ spc () ++ 
      pr_match_rule false Printer.pr_pattern pr_glob_tactic r)
  end

(* Prints the hypothesis pattern identifier if it exists *)
let hyp_bound = function
  | Anonymous -> " (unbound)"
  | Name id -> " (bound to "^(Names.string_of_id id)^")"

(* Prints a matched hypothesis *)
let db_matched_hyp debug env (id,c) ido =
  if debug = DebugOn then
    msgnl (str "Hypothesis " ++
           str ((Names.string_of_id id)^(hyp_bound ido)^
                " has been matched: ") ++ prterm_env env c)

(* Prints the matched conclusion *)
let db_matched_concl debug env c =
  if debug = DebugOn then
    msgnl (str "Conclusion has been matched: " ++ prterm_env env c)

(* Prints a success message when the goal has been matched *)
let db_mc_pattern_success debug =
  if debug = DebugOn then
    msgnl (str "The goal has been successfully matched!" ++ fnl() ++
           str "Let us execute the right-hand side part..." ++ fnl())

let pp_match_pattern env = function
  | Term c -> Term (extern_pattern env (names_of_rel_context env) c)
  | Subterm (o,c) ->
    Subterm (o,(extern_pattern env (names_of_rel_context env) c))

(* Prints a failure message for an hypothesis pattern *)
let db_hyp_pattern_failure debug env (na,hyp) =
  if debug = DebugOn then
    msgnl (str ("The pattern hypothesis"^(hyp_bound na)^
                " cannot match: ") ++
           pr_match_pattern
             (Printer.pr_pattern_env env (names_of_rel_context env))
             hyp)

(* Prints a matching failure message for a rule *)
let db_matching_failure debug =
  if debug = DebugOn then
    msgnl (str "This rule has failed due to matching errors!" ++ fnl() ++
           str "Let us try the next one...")

(* Prints an evaluation failure message for a rule *)
let db_eval_failure debug s =
  if debug = DebugOn then
    let s = if s="" then "no message" else "message \""^s^"\"" in
    msgnl 
      (str "This rule has failed due to \"Fail\" tactic (" ++
       str s ++ str ", level 0)!" ++ fnl() ++ str "Let us try the next one...")

(* An exception handler *)
let explain_logic_error = ref (fun e -> mt())

(* Prints a logic failure message for a rule *)
let db_logic_failure debug err =
  if debug = DebugOn then
  begin
    msgnl (!explain_logic_error err);
    msgnl (str "This rule has failed due to a logic error!" ++ fnl() ++
           str "Let us try the next one...")
  end
