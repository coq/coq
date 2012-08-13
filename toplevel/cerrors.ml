(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Pp
open Util
open Ast
open Indtypes
open Type_errors
open Pretype_errors
open Lexer

let print_loc loc =
  if loc = dummy_loc then 
    (str"<unknown>")
  else 
    let loc = unloc loc in
    (int (fst loc) ++ str"-" ++ int (snd loc))

let guill s = "\""^s^"\""

let where s =
  if !Options.debug then  (str"in " ++ str s ++ str":" ++ spc ()) else (mt ())

let report () = (str "." ++ spc () ++ str "Please report.")

(* assumption : explain_sys_exn does NOT end with a 'FNL anymore! *)

let rec explain_exn_default = function
  | Stream.Failure -> 
      hov 0 (str "Anomaly: uncaught Stream.Failure.")
  | Stream.Error txt -> 
      hov 0 (str "Syntax error: " ++ str txt)
  | Token.Error txt -> 
      hov 0 (str "Syntax error: " ++ str txt)
  | Sys_error msg -> 
      hov 0 (str "Anomaly: uncaught exception Sys_error " ++ str (guill msg) ++ report ())
  | UserError(s,pps) -> 
      hov 1 (str "User error: " ++ where s ++ pps)
  | Out_of_memory -> 
      hov 0 (str "Out of memory")
  | Stack_overflow -> 
      hov 0 (str "Stack overflow")
  | Ast.No_match s -> 
      hov 0 (str "Anomaly: Ast matching error: " ++ str s ++ report ())
  | Anomaly (s,pps) -> 
      hov 1 (str "Anomaly: " ++ where s ++ pps ++ report ())
  | Match_failure(filename,pos1,pos2) ->
      hov 1 (str "Anomaly: Match failure in file " ++ str (guill filename) ++ 
      if Sys.ocaml_version = "3.06" then
		   (str " from character " ++ int pos1 ++ 
                    str " to " ++ int pos2)
		 else
		   (str " at line " ++ int pos1 ++
		    str " character " ++ int pos2)
	           ++ report ())
  | Not_found -> 
      hov 0 (str "Anomaly: uncaught exception Not_found" ++ report ())
  | Failure s -> 
      hov 0 (str "Anomaly: uncaught exception Failure " ++ str (guill s) ++ report ())
  | Invalid_argument s -> 
      hov 0 (str "Anomaly: uncaught exception Invalid_argument " ++ str (guill s) ++ report ())
  | Sys.Break -> 
      hov 0 (fnl () ++ str "User Interrupt.")
  | Univ.UniverseInconsistency -> 
      hov 0 (str "Error: Universe Inconsistency.")
  | TypeError(ctx,te) -> 
      hov 0 (str "Error:" ++ spc () ++ Himsg.explain_type_error ctx te)
  | PretypeError(ctx,te) ->
      hov 0 (str "Error:" ++ spc () ++ Himsg.explain_pretype_error ctx te)
  | InductiveError e -> 
      hov 0 (str "Error:" ++ spc () ++ Himsg.explain_inductive_error e)
  | Cases.PatternMatchingError (env,e) -> 
      hov 0
	(str "Error:" ++ spc () ++ Himsg.explain_pattern_matching_error env e)
  | Logic.RefinerError e -> 
      hov 0 (str "Error:" ++ spc () ++ Himsg.explain_refiner_error e)
  | Nametab.GlobalizationError q ->
      hov 0 (str "Error:" ++ spc () ++
	       str "The reference" ++ spc () ++ Libnames.pr_qualid q ++
	       spc () ++ str "was not found" ++ 
	       spc () ++ str "in the current" ++ spc () ++ str "environment")
  | Nametab.GlobalizationConstantError q ->
      hov 0 (str "Error:" ++ spc () ++
	       str "No constant of this name:" ++ spc () ++ Libnames.pr_qualid q)
  | Refiner.FailError (i,s) ->
      let s = if s="" then "" else " \""^s^"\"" in
      hov 0 (str "Error: Tactic failure" ++ str s ++
             if i=0 then mt () else str " (level " ++ int i ++ str").")
  | Compat.Exc_located (loc,exc) ->
      hov 0 ((if loc = dummy_loc then (mt ())
               else (str"At location " ++ print_loc loc ++ str":" ++ fnl ()))
               ++ explain_exn_default exc)
  | Lexer.Error Illegal_character -> 
      hov 0 (str "Syntax error: Illegal character.")
  | Lexer.Error Unterminated_comment -> 
      hov 0 (str "Syntax error: Unterminated comment.")
  | Lexer.Error Unterminated_string -> 
      hov 0 (str "Syntax error: Unterminated string.")
  | Lexer.Error Undefined_token -> 
      hov 0 (str "Syntax error: Undefined token.")
  | Lexer.Error (Bad_token s) -> 
      hov 0 (str "Syntax error: Bad token" ++ spc () ++ str s ++ str ".")
  | Assert_failure (s,b,e) ->
      hov 0 (str "Anomaly: assert failure" ++ spc () ++
	       (if s <> "" then 
		 if Sys.ocaml_version = "3.06" then
		   (str ("(file \"" ^ s ^ "\", characters ") ++ 
		    int b ++ str "-" ++ int e ++ str ")")
		 else
		   (str ("(file \"" ^ s ^ "\", line ") ++ int b ++
		    str ", characters " ++ int e ++ str "-" ++
		    int (e+6) ++ str ")")
	       else
		 (mt ())) ++
	       report ())
  | reraise ->
      hov 0 (str "Anomaly: Uncaught exception " ++ 
	       str (Printexc.to_string reraise) ++ report ())

let raise_if_debug e =
  if !Options.debug then raise e

let _ = Tactic_debug.explain_logic_error := explain_exn_default

let explain_exn_function = ref explain_exn_default

let explain_exn e = !explain_exn_function e
