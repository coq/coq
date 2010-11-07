(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Compat
open Pp
open Util
open Indtypes
open Type_errors
open Pretype_errors
open Indrec

let print_loc loc =
  if loc = dummy_loc then
    (str"<unknown>")
  else
    let loc = unloc loc in
    (int (fst loc) ++ str"-" ++ int (snd loc))

let guill s = "\""^s^"\""

let where s =
  if !Flags.debug then  (str"in " ++ str s ++ str":" ++ spc ()) else (mt ())

exception EvaluatedError of std_ppcmds * exn option

(* assumption : explain_sys_exn does NOT end with a 'FNL anymore! *)

let rec explain_exn_default_aux anomaly_string report_fn = function
  | Stream.Failure ->
      hov 0 (anomaly_string () ++ str "uncaught Stream.Failure.")
  | Stream.Error txt ->
      hov 0 (str "Syntax error: " ++ str txt ++ str ".")
  | Token.Error txt ->
      hov 0 (str "Syntax error: " ++ str txt ++ str ".")
  | Lexer.Error.E err -> hov 0 (str (Lexer.Error.to_string err))
  | Sys_error msg ->
      hov 0 (anomaly_string () ++ str "uncaught exception Sys_error " ++ str (guill msg) ++ report_fn ())
  | UserError(s,pps) ->
      hov 0 (str "Error: " ++ where s ++ pps)
  | Out_of_memory ->
      hov 0 (str "Out of memory.")
  | Stack_overflow ->
      hov 0 (str "Stack overflow.")
  | Timeout ->
      hov 0 (str "Timeout!")
  | Anomaly (s,pps) ->
      hov 0 (anomaly_string () ++ where s ++ pps ++ report_fn ())
  | AnomalyOnError (s,exc) ->
      hov 0 (anomaly_string () ++ str s ++ str ". Received exception is:" ++
	fnl() ++ explain_exn_default_aux anomaly_string report_fn exc)
  | Match_failure(filename,pos1,pos2) ->
      hov 0 (anomaly_string () ++ str "Match failure in file " ++
	     str (guill filename) ++ str " at line " ++ int pos1 ++
	     str " character " ++ int pos2 ++ report_fn ())
  | Not_found ->
      hov 0 (anomaly_string () ++ str "uncaught exception Not_found" ++ report_fn ())
  | Failure s ->
      hov 0 (anomaly_string () ++ str "uncaught exception Failure " ++ str (guill s) ++ report_fn ())
  | Invalid_argument s ->
      hov 0 (anomaly_string () ++ str "uncaught exception Invalid_argument " ++ str (guill s) ++ report_fn ())
  | Sys.Break ->
      hov 0 (fnl () ++ str "User interrupt.")
  | Loc.Exc_located (loc,exc) ->
      hov 0 ((if loc = dummy_loc then (mt ())
               else (str"At location " ++ print_loc loc ++ str":" ++ fnl ()))
               ++ explain_exn_default_aux anomaly_string report_fn exc)
  | Assert_failure (s,b,e) ->
      hov 0 (anomaly_string () ++ str "assert failure" ++ spc () ++
	       (if s = "" then mt ()
		else
		  (str ("(file \"" ^ s ^ "\", line ") ++ int b ++
		   str ", characters " ++ int e ++ str "-" ++
		   int (e+6) ++ str ")")) ++
	       report_fn ())
  | EvaluatedError (msg,None) ->
      msg
  | EvaluatedError (msg,Some reraise) ->
      msg ++ explain_exn_default_aux anomaly_string report_fn reraise
  | Ploc.Exc(loc,exc) -> 
      hov 0 ((if loc = dummy_loc then (mt ())
               else (str"At location " ++ print_loc loc ++ str":" ++ fnl ()))
               ++ explain_exn_default_aux anomaly_string report_fn exc)
  | reraise ->
      hov 0 (anomaly_string () ++ str "Uncaught exception " ++
	       str (Printexc.to_string reraise) ++ report_fn ())

let wrap_vernac_error strm =
  EvaluatedError (hov 0 (str "Error:" ++ spc () ++ strm), None)

let rec process_vernac_interp_error = function
  | Univ.UniverseInconsistency (o,u,v) ->
      let msg =
	if !Constrextern.print_universes then
	  spc() ++ str "(cannot enforce" ++ spc() ++ Univ.pr_uni u ++ spc() ++
          str (match o with Univ.Lt -> "<" | Univ.Le -> "<=" | Univ.Eq -> "=")
	  ++ spc() ++ Univ.pr_uni v ++ str")"
	else
	  mt() in
      wrap_vernac_error (str "Universe inconsistency" ++ msg ++ str ".")
  | TypeError(ctx,te) ->
      wrap_vernac_error (Himsg.explain_type_error ctx Evd.empty te)
  | PretypeError(ctx,sigma,te) ->
      wrap_vernac_error (Himsg.explain_pretype_error ctx sigma te)
  | Typeclasses_errors.TypeClassError(env, te) ->
      wrap_vernac_error (Himsg.explain_typeclass_error env te)
  | InductiveError e ->
      wrap_vernac_error (Himsg.explain_inductive_error e)
  | RecursionSchemeError e ->
      wrap_vernac_error (Himsg.explain_recursion_scheme_error e)
  | Cases.PatternMatchingError (env,e) ->
      wrap_vernac_error (Himsg.explain_pattern_matching_error env e)
  | Tacred.ReductionTacticError e ->
      wrap_vernac_error (Himsg.explain_reduction_tactic_error e)
  | Logic.RefinerError e ->
      wrap_vernac_error (Himsg.explain_refiner_error e)
  | Nametab.GlobalizationError q ->
      wrap_vernac_error
        (str "The reference" ++ spc () ++ Libnames.pr_qualid q ++
	 spc () ++ str "was not found" ++
	 spc () ++ str "in the current" ++ spc () ++ str "environment.")
  | Nametab.GlobalizationConstantError q ->
      wrap_vernac_error
        (str "No constant of this name:" ++ spc () ++
         Libnames.pr_qualid q ++ str ".")
  | Refiner.FailError (i,s) ->
      EvaluatedError (hov 0 (str "Error: Tactic failure" ++
                (if Lazy.force s <> mt() then str ":" ++ Lazy.force s else mt ()) ++
                if i=0 then str "." else str " (level " ++ int i ++ str")."),
                None)
  | AlreadyDeclared msg ->
      wrap_vernac_error (msg ++ str ".")
  | Proof_type.LtacLocated (_,(Refiner.FailError (i,s) as exc)) when Lazy.force s <> mt () ->
      process_vernac_interp_error exc
  | Proof_type.LtacLocated (s,exc) ->
      EvaluatedError (hov 0 (Himsg.explain_ltac_call_trace s ++ fnl()),
        Some (process_vernac_interp_error exc))
  | Loc.Exc_located (loc,exc) ->
      Loc.Exc_located (loc,process_vernac_interp_error exc)
  | exc ->
      exc

let anomaly_string () = str "Anomaly: "

let report () = (str "." ++ spc () ++ str "Please report.")

let explain_exn_default =
  explain_exn_default_aux anomaly_string report

let raise_if_debug e =
  if !Flags.debug then raise e

let _ = Tactic_debug.explain_logic_error :=
  (fun e -> explain_exn_default (process_vernac_interp_error e))

let _ = Tactic_debug.explain_logic_error_no_anomaly :=
  (fun e ->
    explain_exn_default_aux mt (fun () -> str ".")
      (process_vernac_interp_error e))

let explain_exn_function = ref explain_exn_default

let explain_exn e = !explain_exn_function e

let explain_exn_no_anomaly e =
   explain_exn_default_aux (fun () -> raise e) mt e
