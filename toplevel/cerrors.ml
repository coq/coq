(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Pp
open Errors
open Indtypes
open Type_errors
open Pretype_errors
open Indrec

let print_loc loc =
  if Loc.is_ghost loc then
    (str"<unknown>")
  else
    let loc = Loc.unloc loc in
    (int (fst loc) ++ str"-" ++ int (snd loc))

let guill s = "\""^s^"\""

(** Invariant : exceptions embedded in EvaluatedError satisfy
    Errors.noncritical *)

exception EvaluatedError of std_ppcmds * exn option

(** Registration of generic errors
    Nota: explain_exn does NOT end with a newline anymore!
*)

let explain_exn_default = function
  (* Basic interaction exceptions *)
  | Stream.Error txt -> hov 0 (str ("Syntax error: " ^ txt ^ "."))
  | Compat.Token.Error txt ->  hov 0 (str ("Syntax error: " ^ txt ^ "."))
  | Lexer.Error.E err -> hov 0 (str (Lexer.Error.to_string err))
  | Sys_error msg -> hov 0 (str ("System error: " ^ guill msg))
  | Out_of_memory -> hov 0 (str "Out of memory.")
  | Stack_overflow -> hov 0 (str "Stack overflow.")
  | Timeout -> hov 0 (str "Timeout!")
  | Sys.Break -> hov 0 (fnl () ++ str "User interrupt.")
  (* Exceptions with pre-evaluated error messages *)
  | EvaluatedError (msg,None) -> msg
  | EvaluatedError (msg,Some reraise) -> msg ++ Errors.print reraise
  (* Otherwise, not handled here *)
  | _ -> raise Errors.Unhandled

let _ = Errors.register_handler explain_exn_default


(** Pre-explain a vernac interpretation error *)

let wrap_vernac_error exn strm =
  let e = EvaluatedError (hov 0 (str "Error:" ++ spc () ++ strm), None) in
  Exninfo.copy exn e

let process_vernac_interp_error exn = match exn with
  | Univ.UniverseInconsistency (o,u,v,p) ->
    let pr_rel r =
      match r with
	  Univ.Eq -> str"=" | Univ.Lt -> str"<" | Univ.Le -> str"<=" in
    let reason = match p with
	[] -> mt()
      | _::_ ->
	str " because" ++ spc() ++ Univ.pr_uni v ++
	  prlist (fun (r,v) -> spc() ++ pr_rel r ++ str" " ++ Univ.pr_uni v)
	  p ++
	  (if Univ.Universe.equal (snd (List.last p)) u then mt() else
	      (spc() ++ str "= " ++ Univ.pr_uni u)) in
    let msg =
      if !Constrextern.print_universes then
	spc() ++ str "(cannot enforce" ++ spc() ++ Univ.pr_uni u ++ spc() ++
          pr_rel o ++ spc() ++ Univ.pr_uni v ++ reason ++ str")"
      else
	mt() in
    wrap_vernac_error exn (str "Universe inconsistency" ++ msg ++ str ".")
  | TypeError(ctx,te) ->
      wrap_vernac_error exn (Himsg.explain_type_error ctx Evd.empty te)
  | PretypeError(ctx,sigma,te) ->
      wrap_vernac_error exn (Himsg.explain_pretype_error ctx sigma te)
  | Typeclasses_errors.TypeClassError(env, te) ->
      wrap_vernac_error exn (Himsg.explain_typeclass_error env te)
  | InductiveError e ->
      wrap_vernac_error exn (Himsg.explain_inductive_error e)
  | Modops.ModuleTypingError e ->
      wrap_vernac_error exn (Himsg.explain_module_error e)
  | Modintern.ModuleInternalizationError e ->
      wrap_vernac_error exn (Himsg.explain_module_internalization_error e)
  | RecursionSchemeError e ->
      wrap_vernac_error exn (Himsg.explain_recursion_scheme_error e)
  | Cases.PatternMatchingError (env,e) ->
      wrap_vernac_error exn (Himsg.explain_pattern_matching_error env e)
  | Tacred.ReductionTacticError e ->
      wrap_vernac_error exn (Himsg.explain_reduction_tactic_error e)
  | Logic.RefinerError e ->
      wrap_vernac_error exn (Himsg.explain_refiner_error e)
  | Nametab.GlobalizationError q ->
      wrap_vernac_error exn
        (str "The reference" ++ spc () ++ Libnames.pr_qualid q ++
	 spc () ++ str "was not found" ++
	 spc () ++ str "in the current" ++ spc () ++ str "environment.")
  | Refiner.FailError (i,s) ->
      let s = Lazy.force s in
      wrap_vernac_error exn
	(str "Tactic failure" ++
         (if Pp.is_empty s then s else str ":" ++ s) ++
         if Int.equal i 0 then str "." else str " (level " ++ int i ++ str").")
  | AlreadyDeclared msg ->
      wrap_vernac_error exn (msg ++ str ".")
  | exc ->
      exc

let rec strip_wrapping_exceptions = function
  | Proof_errors.TacticFailure e as src ->
    let e = Backtrace.app_backtrace ~src ~dst:e in
    strip_wrapping_exceptions e
  | exc -> exc

let process_vernac_interp_error exc =
  let exc = strip_wrapping_exceptions exc in
  let e = process_vernac_interp_error exc in
  let ltac_trace = Exninfo.get exc Proof_type.ltac_trace_info in
  let loc = Option.default Loc.ghost (Loc.get_loc e) in
  match ltac_trace with
  | None -> e
  | Some trace ->
    match Himsg.extract_ltac_trace trace loc with
    | None, loc -> Loc.add_loc e loc
    | Some msg, loc -> Loc.add_loc (EvaluatedError (msg, Some e)) loc

let _ = Tactic_debug.explain_logic_error :=
  (fun e -> Errors.print (process_vernac_interp_error e))

let _ = Tactic_debug.explain_logic_error_no_anomaly :=
  (fun e -> Errors.print_no_report (process_vernac_interp_error e))
