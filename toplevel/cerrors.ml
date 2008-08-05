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
open Indtypes
open Type_errors
open Pretype_errors
open Indrec
open Lexer

let print_loc loc =
  if loc = dummy_loc then 
    (str"<unknown>")
  else 
    let loc = unloc loc in
    (int (fst loc) ++ str"-" ++ int (snd loc))

let guill s = "\""^s^"\""

let where s =
  if !Flags.debug then  (str"in " ++ str s ++ str":" ++ spc ()) else (mt ())

(* assumption : explain_sys_exn does NOT end with a 'FNL anymore! *)

let rec explain_exn_default_aux anomaly_string report_fn = function
  | Stream.Failure -> 
      hov 0 (anomaly_string () ++ str "uncaught Stream.Failure.")
  | Stream.Error txt -> 
      hov 0 (str "Syntax error: " ++ str txt ++ str ".")
  | Token.Error txt -> 
      hov 0 (str "Syntax error: " ++ str txt ++ str ".")
  | Sys_error msg -> 
      hov 0 (anomaly_string () ++ str "uncaught exception Sys_error " ++ str (guill msg) ++ report_fn ())
  | UserError(s,pps) -> 
      hov 0 (str "Error: " ++ where s ++ pps)
  | Out_of_memory -> 
      hov 0 (str "Out of memory.")
  | Stack_overflow -> 
      hov 0 (str "Stack overflow.")
  | Anomaly (s,pps) -> 
      hov 0 (anomaly_string () ++ where s ++ pps ++ report_fn ())
  | Match_failure(filename,pos1,pos2) ->
      hov 0 (anomaly_string () ++ str "Match failure in file " ++ str (guill filename) ++ 
      if Sys.ocaml_version = "3.06" then
		   (str " from character " ++ int pos1 ++ 
                    str " to " ++ int pos2)
		 else
		   (str " at line " ++ int pos1 ++
		    str " character " ++ int pos2)
	           ++ report_fn ())
  | Not_found -> 
      hov 0 (anomaly_string () ++ str "uncaught exception Not_found" ++ report_fn ())
  | Failure s -> 
      hov 0 (anomaly_string () ++ str "uncaught exception Failure " ++ str (guill s) ++ report_fn ())
  | Invalid_argument s -> 
      hov 0 (anomaly_string () ++ str "uncaught exception Invalid_argument " ++ str (guill s) ++ report_fn ())
  | Sys.Break -> 
      hov 0 (fnl () ++ str "User interrupt.")
  | Univ.UniverseInconsistency (o,u,v) ->
      let msg = 
	if !Constrextern.print_universes then
	  spc() ++ str "(cannot enforce" ++ spc() ++ Univ.pr_uni u ++ spc() ++
          str (match o with Univ.Lt -> "<" | Univ.Le -> "<=" | Univ.Eq -> "=")
	  ++ spc() ++ Univ.pr_uni v ++ str")"
	else
	  mt() in
      hov 0 (str "Error: Universe inconsistency" ++ msg ++ str ".")
  | TypeError(ctx,te) -> 
      hov 0 (str "Error:" ++ spc () ++ Himsg.explain_type_error ctx te)
  | PretypeError(ctx,te) ->
      hov 0 (str "Error:" ++ spc () ++ Himsg.explain_pretype_error ctx te)
  | Typeclasses_errors.TypeClassError(env, te) ->
      hov 0 (str "Error:" ++ spc () ++ Himsg.explain_typeclass_error env te)
  | InductiveError e -> 
      hov 0 (str "Error:" ++ spc () ++ Himsg.explain_inductive_error e)
  | RecursionSchemeError e -> 
      hov 0 (str "Error:" ++ spc () ++ Himsg.explain_recursion_scheme_error e)
  | Proof_type.LtacLocated (_,(Refiner.FailError (i,s) as exc)) when s <> mt () ->
      explain_exn_default_aux anomaly_string report_fn exc
  | Proof_type.LtacLocated (s,exc) ->
      hov 0 (Himsg.explain_ltac_call_trace s ++ fnl ()
             ++ explain_exn_default_aux anomaly_string report_fn exc)
  | Cases.PatternMatchingError (env,e) -> 
      hov 0
	(str "Error:" ++ spc () ++ Himsg.explain_pattern_matching_error env e)
  | Tacred.ReductionTacticError e -> 
      hov 0 (str "Error:" ++ spc () ++ Himsg.explain_reduction_tactic_error e)
  | Logic.RefinerError e -> 
      hov 0 (str "Error:" ++ spc () ++ Himsg.explain_refiner_error e)
  | Nametab.GlobalizationError q ->
      hov 0 (str "Error:" ++ spc () ++
	       str "The reference" ++ spc () ++ Libnames.pr_qualid q ++
	       spc () ++ str "was not found" ++ 
	       spc () ++ str "in the current" ++ spc () ++ str "environment.")
  | Nametab.GlobalizationConstantError q ->
      hov 0 (str "Error:" ++ spc () ++
	       str "No constant of this name:" ++ spc () ++ 
               Libnames.pr_qualid q ++ str ".")
  | Refiner.FailError (i,s) ->
      hov 0 (str "Error: Tactic failure" ++ 
                (if s <> mt() then str ":" ++ s else mt ()) ++
                if i=0 then str "." else str " (level " ++ int i ++ str").")
  | Stdpp.Exc_located (loc,exc) ->
      hov 0 ((if loc = dummy_loc then (mt ())
               else (str"At location " ++ print_loc loc ++ str":" ++ fnl ()))
               ++ explain_exn_default_aux anomaly_string report_fn exc)
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
      hov 0 (anomaly_string () ++ str "assert failure" ++ spc () ++
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
	       report_fn ())
  | reraise ->
      hov 0 (anomaly_string () ++ str "Uncaught exception " ++ 
	       str (Printexc.to_string reraise) ++ report_fn ())

let anomaly_string () = str "Anomaly: "

let report () = (str "." ++ spc () ++ str "Please report.")

let explain_exn_default =
  explain_exn_default_aux anomaly_string report

let raise_if_debug e =
  if !Flags.debug then raise e

let _ = Tactic_debug.explain_logic_error := explain_exn_default

let _ = Tactic_debug.explain_logic_error_no_anomaly :=
          explain_exn_default_aux (fun () -> mt()) (fun () -> str ".")

let explain_exn_function = ref explain_exn_default

let explain_exn e = !explain_exn_function e
