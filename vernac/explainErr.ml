(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open CErrors
open Indtypes
open Type_errors
open Pretype_errors
open Indrec

let guill s = str "\"" ++ str s ++ str "\""

(** Invariant : exceptions embedded in EvaluatedError satisfy
    Errors.noncritical *)

exception EvaluatedError of Pp.t * exn option

(** Registration of generic errors
    Nota: explain_exn does NOT end with a newline anymore!
*)

let explain_exn_default = function
  (* Basic interaction exceptions *)
  | Stream.Error txt -> hov 0 (str "Syntax error: " ++ str txt ++ str ".")
  | Token.Error txt -> hov 0 (str "Syntax error: " ++ str txt ++ str ".")
  | CLexer.Error.E err -> hov 0 (str (CLexer.Error.to_string err))
  | Sys_error msg -> hov 0 (str "System error: " ++ guill msg)
  | Out_of_memory -> hov 0 (str "Out of memory.")
  | Stack_overflow -> hov 0 (str "Stack overflow.")
  | Dynlink.Error e -> hov 0 (str "Dynlink error: " ++ str Dynlink.(error_message e))
  | Timeout -> hov 0 (str "Timeout!")
  | Sys.Break -> hov 0 (fnl () ++ str "User interrupt.")
  (* Exceptions with pre-evaluated error messages *)
  | EvaluatedError (msg,None) -> msg
  | EvaluatedError (msg,Some reraise) -> msg ++ CErrors.print reraise
  (* Otherwise, not handled here *)
  | _ -> raise CErrors.Unhandled

let _ = CErrors.register_handler explain_exn_default


(** Pre-explain a vernac interpretation error *)

let wrap_vernac_error (exn, info) strm = (EvaluatedError (strm, None), info)

let process_vernac_interp_error exn = match fst exn with
  | Univ.UniverseInconsistency i ->
    let msg =
      if !Constrextern.print_universes then
	str "." ++ spc() ++ 
          Univ.explain_universe_inconsistency UnivNames.pr_with_global_universes i
      else
	mt() in
    wrap_vernac_error exn (str "Universe inconsistency" ++ msg ++ str ".")
  | TypeError(ctx,te) ->
      let te = Himsg.map_ptype_error EConstr.of_constr te in
      wrap_vernac_error exn (Himsg.explain_type_error ctx Evd.empty te)
  | PretypeError(ctx,sigma,te) ->
      wrap_vernac_error exn (Himsg.explain_pretype_error ctx sigma te)
  | Notation.NumeralNotationError(ctx,sigma,te) ->
      wrap_vernac_error exn (Himsg.explain_numeral_notation_error ctx sigma te)
  | Typeclasses_errors.TypeClassError(env, te) ->
      wrap_vernac_error exn (Himsg.explain_typeclass_error env te)
  | Implicit_quantifiers.MismatchedContextInstance(e,c,l,x) ->
    wrap_vernac_error exn (Himsg.explain_mismatched_contexts e c l x)
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
  | Logic.RefinerError (env, sigma, e) ->
    wrap_vernac_error exn (Himsg.explain_refiner_error env sigma e)
  | Nametab.GlobalizationError q ->
      wrap_vernac_error exn
        (str "The reference" ++ spc () ++ Libnames.pr_qualid q ++
	 spc () ++ str "was not found" ++
	 spc () ++ str "in the current" ++ spc () ++ str "environment.")
  | Refiner.FailError (i,s) ->
      let s = Lazy.force s in
      wrap_vernac_error exn
	(str "Tactic failure" ++
         (if Pp.ismt s then s else str ": " ++ s) ++
         if Int.equal i 0 then str "." else str " (level " ++ int i ++ str").")
  | AlreadyDeclared msg ->
      wrap_vernac_error exn (msg ++ str ".")
  | _ ->
      exn

let rec strip_wrapping_exceptions = function
  | Logic_monad.TacticFailure e ->
    strip_wrapping_exceptions e
  | exc -> exc

let additional_error_info = ref []

let register_additional_error_info f =
  additional_error_info := f :: !additional_error_info

let process_vernac_interp_error ?(allow_uncaught=true) (exc, info) =
  let exc = strip_wrapping_exceptions exc in
  let e = process_vernac_interp_error (exc, info) in
  let () =
    if not allow_uncaught && not (CErrors.handled (fst e)) then
      let (e, info) = e in
      let msg = str "Uncaught exception " ++ str (Printexc.to_string e) ++ str "." in
      let err = CErrors.make_anomaly msg in
      Util.iraise (err, info)
  in
  let e' =
    try Some (CList.find_map (fun f -> f e) !additional_error_info)
    with _ -> None
  in
  let add_loc_opt ?loc info = Option.cata (fun l -> Loc.add_loc info l) info loc in
  match e' with
  | None -> e
  | Some (loc, None) -> (fst e, add_loc_opt ?loc (snd e))
  | Some (loc, Some msg) ->
    (EvaluatedError (msg, Some (fst e)), add_loc_opt ?loc (snd e))
