(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)
open Ast
open Pp
open Pptactic
open Printer

(* This module intends to be a beginning of debugger for tactic expressions.
   Currently, it is quite simple and we can hope to have, in the future, a more
   complete panel of commands dedicated to a proof assistant framework *)

(* Debug information *)
type debug_info =
  | DebugOn
  | DebugOff
  | Exit

(* Prints the goal if it exists *)
let db_pr_goal = function
  | None -> 
      msgnl (str "No goal")
  | Some g ->
      msgnl (str "Goal:" ++ fnl () ++ Proof_trees.pr_goal (Tacmach.sig_it g))

(* Prints the commands *)
let help () =
  msgnl (str "Commands: <Enter>=Continue, h=Help, s=Skip, x=Exit")

(* Prints the state and waits for an instruction *)
let debug_prompt goalopt tac_ast =
  db_pr_goal goalopt;
  msg (str "Going to execute:" ++ fnl () ++ (pr_raw_tactic tac_ast) ++ fnl ());
(*         str "Commands: <Enter>=Continue, s=Skip, x=Exit" >];*)
(*  mSG (str "Going to execute:" ++ fnl () ++ (gentacpr tac_ast) ++ fnl () ++ fnl () ++
         str "----<Enter>=Continue----s=Skip----x=Exit----");*)
  let rec prompt () =
    msg (fnl () ++ str "TcDebug > ");
    flush stdout;
    let inst = read_line () in
(*    mSGNL (mt ());*)
    match inst with
    | ""  -> DebugOn
    | "s" -> DebugOff
    | "x" -> Exit
    | "h" ->
      begin
        help ();
        prompt ()
      end
    | _   -> prompt () in
  prompt ()

(* Prints a constr *)
let db_constr debug env c =
  if debug = DebugOn then
    msgnl (str "Evaluated term --> " ++ prterm_env env c)

(* Prints a matched hypothesis *)
let db_matched_hyp debug env (id,c) =
  if debug = DebugOn then
    msgnl (str "Matched hypothesis --> " ++ str (Names.string_of_id id^": ") ++
           prterm_env env c)

(* Prints the matched conclusion *)
let db_matched_concl debug env c =
  if debug = DebugOn then
    msgnl (str "Matched goal --> " ++ prterm_env env c)
