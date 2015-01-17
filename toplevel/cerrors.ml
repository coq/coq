(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
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

let wrap_vernac_error (exn, info) strm =
  let header = Pp.tag (Pp.Tag.inj Ppstyle.error_tag Ppstyle.tag) (str "Error:") in
  let e = EvaluatedError (hov 0 (header ++ spc () ++ strm), None) in
  (e, info)

let process_vernac_interp_error exn = match fst exn with
  | Univ.UniverseInconsistency i ->
    let msg =
      if !Constrextern.print_universes then
	str "." ++ spc() ++ 
	  Univ.explain_universe_inconsistency Universes.pr_with_global_universes i
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
  | Cases.PatternMatchingError (env,sigma,e) ->
      wrap_vernac_error exn (Himsg.explain_pattern_matching_error env sigma e)
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
         (if Pp.is_empty s then s else str ": " ++ s) ++
         if Int.equal i 0 then str "." else str " (level " ++ int i ++ str").")
  | AlreadyDeclared msg ->
      wrap_vernac_error exn (msg ++ str ".")
  | _ ->
      exn

let rec strip_wrapping_exceptions = function
  | Logic_monad.TacticFailure e ->
    strip_wrapping_exceptions e
  | exc -> exc

let process_vernac_interp_error (exc, info) =
  let exc = strip_wrapping_exceptions exc in
  let e = process_vernac_interp_error (exc, info) in
  let ltac_trace = Exninfo.get info Proof_type.ltac_trace_info in
  let loc = Option.default Loc.ghost (Loc.get_loc info) in
  match ltac_trace with
  | None -> e
  | Some trace ->
    let (e, info) = e in
    match Himsg.extract_ltac_trace trace loc with
    | None, loc -> (e, Loc.add_loc info loc)
    | Some msg, loc ->
      (EvaluatedError (msg, Some e), Loc.add_loc info loc)

let _ = Tactic_debug.explain_logic_error :=
  (fun e -> Errors.print (fst (process_vernac_interp_error (e, Exninfo.null))))

let _ = Tactic_debug.explain_logic_error_no_anomaly :=
  (fun e -> Errors.print_no_report (fst (process_vernac_interp_error (e, Exninfo.null))))
