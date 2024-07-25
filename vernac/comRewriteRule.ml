(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names

let maybe_error_many_udecls = function
| ({CAst.loc;v=id}, Some _) ->
  CErrors.user_err ?loc
    Pp.(strbrk "When declaring multiple symbols in one command, " ++
        strbrk "only the first is allowed a universe binder " ++
        strbrk "(which will be shared by the whole block).")
| (_, None) -> ()

let preprocess_symbols l =
  let open Vernacexpr in
  if Global.sections_are_opened () then
    CErrors.user_err Pp.(str "Declaring a symbol is not allowed in sections.");
  let udecl = match l with
    | (coe, ((id, udecl)::rest, c))::rest' ->
      List.iter maybe_error_many_udecls rest;
      List.iter (fun (coe, (idl, c)) -> List.iter maybe_error_many_udecls idl) rest';
      udecl
    | (_, ([], _))::_ | [] -> assert false
  in
  let no_coercion_msg = Pp.(str "Cannot deal with coercions in symbols") in
  List.iter (function AddCoercion, (({CAst.loc; _}, _) :: _, _) -> CErrors.user_err ?loc no_coercion_msg | AddCoercion, _ -> assert false | _ -> ()) l;
  udecl, List.concat_map (fun (coe, (idl, c)) -> List.map (fun (id, _) -> id, c) idl) l

let do_symbol ~poly ~unfold_fix udecl (id, typ) =
  if Dumpglob.dump () then Dumpglob.dump_definition id false "symb";
  let id = id.CAst.v in
  let env = Global.env () in
  let evd, udecl = Constrintern.interp_univ_decl_opt env udecl in
  let evd, (typ, impls) =
    Constrintern.(interp_type_evars_impls ~impls:empty_internalization_env)
      env evd typ
  in
  Pretyping.check_evars_are_solved ~program_mode:false env evd;
  let evd = Evd.minimize_universes evd in
  let _qvars, uvars = EConstr.universes_of_constr evd typ in
  let evd = Evd.restrict_universe_context evd uvars in
  let typ = EConstr.to_constr evd typ in
  let univs = Evd.check_univ_decl ~poly evd udecl in
  let entry = Declare.symbol_entry ~univs ~unfold_fix typ in
  let kn = Declare.declare_constant ~name:id ~kind:Decls.IsSymbol (Declare.SymbolEntry entry) in
  let () = Impargs.maybe_declare_manual_implicits false (GlobRef.ConstRef kn) impls in
  let () = Declare.assumption_message id in
  ()

let do_symbols ~poly ~unfold_fix l =
  let env = Global.env () in
  if not @@ Environ.rewrite_rules_allowed env then raise Environ.(RewriteRulesNotAllowed Symb);
  let udecl, l = preprocess_symbols l in
  List.iter (do_symbol ~poly ~unfold_fix udecl) l



open Declarations


let warn_rewrite_rules_break_SR = "rewrite-rules-break-SR"

let rewrite_rules_break_SR_warning =
  CWarnings.create_warning ~name:warn_rewrite_rules_break_SR ~default:CWarnings.Enabled ()

let rewrite_rules_break_SR_msg = CWarnings.create_msg rewrite_rules_break_SR_warning ()
let warn_rewrite_rules_break_SR ~loc reason =
  CWarnings.warn rewrite_rules_break_SR_msg ?loc reason
let () = CWarnings.register_printer rewrite_rules_break_SR_msg
  (fun reason -> Pp.(str "This rewrite rule breaks subject reduction (" ++ reason ++ str ")."))

let interp_rule (pattern, rhs) =
  let env = Global.env () in
  let evd = Evd.from_env env in

  let pattern_loc = pattern.CAst.loc in
  let rhs_loc = rhs.CAst.loc in

  let pattern = Constrintern.(intern_gen WithoutTypeConstraint env evd pattern) in
  let evd, (Info rr_info as info), pattern, j_pat = RRPretyping.eval_pretyper_pattern env evd pattern in

  let () = Rewrite_rules_ops.check_pattern_redex env pattern in

  let uctx_pre =
    (* let evd = Evd.minimize_universes evd in *)
    (* let qvars, uvars = EConstr.universes_of_constr evd @@ EConstr.of_constr (Environ.j_val j_pat) in *)
    (* let qvars', uvars' = EConstr.universes_of_constr evd @@ EConstr.of_constr (Environ.j_type j_pat) in *)
    (* let qvars = Sorts.QVar.Set.union qvars qvars' in *)
    (* let uvars = Univ.Level.Set.union uvars uvars' in *)
    (* let evd = Evd.restrict_universe_context evd uvars in *)
    (* let evd = Evd.restrict_sort_variables evd qvars in *)
    Evd.ustate evd
  in

  let evd = Evd.allow_failures evd in
  let evd = Evd.freeze_sort_variables evd in
  let evd = Evd.fix_undefined_variables evd in

  (* 3. Read right hand side *)
  (* The udecl constraints (or, if none, the lhs constraints) must imply those of the rhs *)
  let rhs = Constrintern.(intern_gen WithoutTypeConstraint env evd rhs) in
  let flags = { Pretyping.no_classes_no_fail_inference_flags with rrpat_evars_abstract = true } in
  let evd, rhs =
    try Pretyping.understand_tcc ~flags env evd ~expected_type:(OfType (EConstr.of_constr @@ Environ.j_type j_pat)) rhs
    with Type_errors.TypeError _ | Pretype_errors.PretypeError _ ->
      warn_rewrite_rules_break_SR ~loc:rhs_loc (Pp.str "the replacement term doesn't have the type of the pattern");
      Pretyping.understand_tcc ~flags env evd rhs
  in


  (* let qvars', uvars' = EConstr.universes_of_constr evd rhs in *)
  (* let qvars = Sorts.QVar.Set.union qvars qvars' in *)
  (* let uvars = Univ.Level.Set.union uvars uvars' in *)
  (* let evd = Evd.restrict_universe_context evd uvars in *)
  (* let evd = Evd.restrict_sort_variables evd qvars in *)

  let checker = let open UnivProblem in function
    | UEq (s1, s2) -> Rewrite_rules_ops.check_ucstr_slow env info (s1, CONV, s2)
    | ULe (s1, s2) -> Rewrite_rules_ops.check_ucstr_slow env info (s1, CUMUL, s2)
    | QEq _ | QLeq _ -> false (* Cannot find better results *)
    | ULub _ | UWeak _ -> assert false
  in

  let fail pp = warn_rewrite_rules_break_SR ~loc:rhs_loc Pp.(str "universe inconsistency, missing constraints: " ++ pp) in
  let evd = Evd.recheck_failures ~fail checker evd in

  let evd = Evd.minimize_universes evd in

  let fail pp = warn_rewrite_rules_break_SR ~loc:rhs_loc Pp.(str "universe inconsistency, missing constraints: " ++ pp) in
  let () = UState.check_uctx_impl ~fail uctx_pre (Evd.ustate evd) in

  let rhs = EConstr.Unsafe.to_constr (Evarutil.nf_evar evd rhs) in
  (* Remaining evars are either substituted or caught by the [translate_pattern] function *)

  let rule = { pattern; replacement = rhs; info = Info rr_info } in

  let _ =
    match Rewrite_rules_ops.translate_rewrite_rule env rule with
    | r -> r
    | exception Rewrite_rules_ops.PatternTranslationError Rewrite_rules_ops.NoHeadSymbol ->
      CErrors.user_err ?loc:pattern_loc Pp.(str "Head head-pattern is not a symbol.")
    | exception Rewrite_rules_ops.PatternTranslationError Rewrite_rules_ops.UnknownEvar ->
      let pr_unresolved_evar (e, b) =
        Pp.(hov 2 (str"- " ++ Printer.pr_existential_key env evd e ++  str ": " ++
          if b then
            Pp.(str "This anonymous pattern variable appears in the replacement term.")
          else
          Himsg.explain_pretype_error env evd (Pretype_errors.UnsolvableImplicit (e,None))))
      in
      let rhs = EConstr.of_constr rhs in
      let evars = Evar.Set.elements @@ Evarutil.undefined_evars_of_term evd rhs in
      let evars = List.filter_map (fun evk ->
        let evi = Evd.find_undefined evd evk in
        match snd (Evd.evar_source evi) with
        | RewriteRulePattern Anonymous -> Some (evk, true)
        | RewriteRulePattern Name _ -> None
        | _ -> Some (evk, false))
        evars
      in
      CErrors.user_err ?loc:rhs_loc Pp.(hov 0 begin
        str "The replacement term contains unresolved implicit arguments:"++ fnl () ++
        str "  " ++ Printer.pr_econstr_env env evd rhs ++ fnl () ++
        str "More precisely: " ++ fnl () ++
        v 0 (prlist_with_sep cut pr_unresolved_evar evars)
      end)
    | exception Rewrite_rules_ops.PatternTranslationError UnknownQVar q ->
      CErrors.user_err ?loc:rhs_loc
        Pp.(str "Sort variable " ++ Termops.pr_evd_qvar evd q ++ str " appears in the replacement but does not appear in the pattern.")
    | exception Rewrite_rules_ops.PatternTranslationError UnknownLevel lvl ->
      CErrors.user_err ?loc:rhs_loc
        Pp.(str "Universe level " ++ Termops.pr_evd_level evd lvl ++ str " appears in the replacement but does not appear in the pattern.")
    | exception Rewrite_rules_ops.PatternTranslationError DuplicateQVar (q, i, j) ->
      CErrors.user_err ?loc:pattern_loc
        Pp.(str "Sort variable " ++ Termops.pr_evd_qvar evd q ++ str " appears twice in the pattern, at positions " ++ int i ++ str " and " ++ int j ++ str".")
    | exception Rewrite_rules_ops.PatternTranslationError DuplicateUVar (lvl, i, j) ->
      CErrors.user_err ?loc:pattern_loc
        Pp.(str "Universe level " ++ Termops.pr_evd_level evd lvl ++ str " appears twice in the pattern, at positions " ++ int i ++ str " and " ++ int j ++ str".")
  in

  rule

let do_rules id rules =
  let env = Global.env () in
  if not @@ Environ.rewrite_rules_allowed env then raise Environ.(RewriteRulesNotAllowed Rule);
  let body = { rewrules_rules = List.map interp_rule rules } in
  Global.add_rewrite_rules id body
