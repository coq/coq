(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)
open Ast
open Pp
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
  | None -> mSGNL [< 'sTR "No goal" >]
  | Some g ->
    mSGNL [<'sTR ("Goal:"); 'fNL; Proof_trees.pr_goal (Tacmach.sig_it g) >]

(* Prints the commands *)
let help () =
  mSGNL [< 'sTR "Commands: <Enter>=Continue, h=Help, s=Skip, x=Exit" >]

(* Prints the state and waits for an instruction *)
let debug_prompt goalopt tac_ast =
  db_pr_goal goalopt;
  mSG [< 'sTR "Going to execute:"; 'fNL; (gentacpr tac_ast); 'fNL >];
(*         'sTR "Commands: <Enter>=Continue, s=Skip, x=Exit" >];*)
(*  mSG [< 'sTR "Going to execute:"; 'fNL; (gentacpr tac_ast); 'fNL; 'fNL;
         'sTR "----<Enter>=Continue----s=Skip----x=Exit----" >];*)
  let rec prompt () =
    mSG [<'fNL; 'sTR "TcDebug > " >];
    flush stdout;
    let inst = read_line () in
(*    mSGNL [<>];*)
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
    mSGNL [< 'sTR "Evaluated term --> ";  prterm_env env c >]

(* Prints a matched hypothesis *)
let db_matched_hyp debug env (id,c) =
  if debug = DebugOn then
    mSGNL [< 'sTR "Matched hypothesis --> "; 'sTR (id^": ");
             prterm_env env c >]

(* Prints the matched conclusion *)
let db_matched_concl debug env c =
  if debug = DebugOn then
    mSGNL [< 'sTR "Matched goal --> "; prterm_env env c >]
