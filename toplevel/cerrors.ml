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


exception EvaluatedError of std_ppcmds * exn option

(** Registration of generic errors
    Nota: explain_exn does NOT end with a newline anymore!
*)

let explain_exn_default = function
  (* Basic interaction exceptions *)
  | Stream.Error txt -> hov 0 (str ("Syntax error: " ^ txt ^ "."))
  | Token.Error txt ->  hov 0 (str ("Syntax error: " ^ txt ^ "."))
  | Lexer.Error.E err -> hov 0 (str (Lexer.Error.to_string err))
  | Sys_error msg -> hov 0 (str ("System error: " ^ guill msg))
  | Out_of_memory -> hov 0 (str "Out of memory.")
  | Stack_overflow -> hov 0 (str "Stack overflow.")
  | Timeout -> hov 0 (str "Timeout!")
  | Sys.Break -> hov 0 (fnl () ++ str "User interrupt.")
  (* Meta-exceptions *)
  | Loc.Exc_located (loc,exc) ->
      hov 0 ((if loc = dummy_loc then (mt ())
               else (str"At location " ++ print_loc loc ++ str":" ++ fnl ()))
               ++ Errors.print_no_anomaly exc)
  | EvaluatedError (msg,None) -> msg
  | EvaluatedError (msg,Some reraise) -> msg ++ Errors.print_no_anomaly reraise
  (* Otherwise, not handled here *)
  | _ -> raise Errors.Unhandled

let _ = Errors.register_handler explain_exn_default


(** Pre-explain a vernac interpretation error *)

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
  | Modops.ModuleTypingError e ->
      wrap_vernac_error (Himsg.explain_module_error e)
  | Modintern.ModuleInternalizationError e ->
      wrap_vernac_error (Himsg.explain_module_internalization_error e)
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
      wrap_vernac_error
	(str "Tactic failure" ++
           (if Lazy.force s <> mt() then str ":" ++ Lazy.force s else mt ()) ++
           if i=0 then str "." else str " (level " ++ int i ++ str").")
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

let _ = Tactic_debug.explain_logic_error :=
  (fun e -> Errors.print (process_vernac_interp_error e))

let _ = Tactic_debug.explain_logic_error_no_anomaly :=
  (fun e -> Errors.print_no_report (process_vernac_interp_error e))
