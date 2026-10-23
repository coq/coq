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
  let loc = id.CAst.loc in
  let id = id.CAst.v in
  let env = Global.env () in
  let evd, udecl = Constrintern.interp_univ_decl_opt env udecl in
  let flags = { Pretyping.all_no_fail_flags with poly } in
  let evd, (typ, impls) =
    Constrintern.(interp_type_evars_impls ~flags ~impls:empty_internalization_env)
      env evd typ
  in
  Pretyping.check_evars_are_solved ~program_mode:false env evd;
  let evd = Evd.minimize_universes ~poly evd in
  let _qvars, uvars = EConstr.universes_of_constr evd typ in
  let evd = Evd.restrict_ustate evd uvars in
  let typ = EConstr.to_constr evd typ in
  let univs = Evd.check_univ_decl ~poly evd udecl in
  let entry = Declare.symbol_entry ~univs ~unfold_fix typ in
  let kn = Declare.declare_constant ?loc ~name:id ~kind:Decls.IsSymbol (Declare.SymbolEntry entry) in
  let () = Impargs.maybe_declare_manual_implicits false (GlobRef.ConstRef kn) impls in
  let () = Declare.assumption_message id in
  ()

let do_symbols ~poly ~unfold_fix l =
  let env = Global.env () in
  if not @@ Environ.rewrite_rules_allowed env then raise Environ.(RewriteRulesNotAllowed Symb);
  let udecl, l = preprocess_symbols l in
  List.iter (do_symbol ~poly ~unfold_fix udecl) l


open Declarations

let warn_rewrite_rules_break_SR =
  CWarnings.create ~name:"rewrite-rules-break-SR" ~category:CWarnings.CoreCategories.rewrite_rules
    Pp.(fun reason ->
        str "This rewrite rule breaks subject reduction" ++ spc() ++ reason)


let err_unknown_evar env evd ?loc evars rhs =
  let pr_unresolved_evar (e, b) =
    Pp.(hov 2 (str"- " ++ Printer.pr_existential_key env evd e ++  str ": " ++
      if b then
        Pp.(str "This anonymous pattern variable appears in the replacement term.")
      else
      Himsg.explain_pretype_error env evd (Pretype_errors.UnsolvableImplicit (e,None))))
  in
  let evars = Evar.Set.elements evars in
  let evars = List.map (fun evk ->
    let evi = Evd.find_undefined evd evk in
    match snd (Evd.evar_source evi) with
    | RewriteRulePattern Anonymous -> (evk, true)
    | RewriteRulePattern Name _ -> assert false
    | _ -> (evk, false))
    evars
  in
  CErrors.user_err ?loc Pp.(hov 0 begin
    str "The replacement term contains unresolved implicit arguments:"++ fnl () ++
    str "  " ++ Printer.pr_econstr_env env evd rhs ++ fnl () ++
    str "More precisely: " ++ fnl () ++
    v 0 (prlist_with_sep cut pr_unresolved_evar evars)
  end)


let interp_rule (pattern, rhs) =
  let env = Global.env () in
  let evd = Evd.from_env env in

  let pattern_loc = pattern.CAst.loc in
  let rhs_loc = rhs.CAst.loc in

  let pattern = Constrintern.(intern_gen WithoutTypeConstraint env evd pattern) in
  let names, (esubst, usubst), evd, cstrs, pattern, j_pat = RRPretyping.eval_pretyper_pattern env evd pattern in
  let ty = EConstr.of_constr (Environ.j_type j_pat) in

  let evd_cheat = Evd.set_ustate evd (UState.disable_checks (Evd.ustate evd)) in
  let evd_cheat = Evd.add_univ_constraints evd_cheat (Sorts.QVar.Map.fold (fun _ -> Univ.UnivConstraints.union) cstrs Univ.UnivConstraints.empty) in

  let rhs = Constrintern.(intern_gen WithoutTypeConstraint env evd_cheat rhs) in
  let flags = Pretyping.no_classes_no_fail_inference_flags in
  let (evd_rhs, rhs), well_typed =
    try Pretyping.understand_tcc ~flags env evd_cheat ~expected_type:(OfType ty) rhs, true
    with Pretype_errors.PretypeError (env', evd', e) ->
      let evdrhs = Pretyping.understand_tcc ~flags env evd_cheat rhs in
      warn_rewrite_rules_break_SR ?loc:rhs_loc
        Pp.(surround (str "the replacement term doesn't have the type of the pattern") ++ str "." ++ fnl () ++ Himsg.explain_pretype_error env' evd' e);
      evdrhs, false
  in

  let evd_rhs = Evd.minimize_universes evd_rhs in
  let rhs = Evarutil.nf_evar evd_rhs rhs in

  let evars = Evarutil.undefined_evars_of_term evd_rhs rhs in
  if not (Evar.Set.for_all (fun evk -> Evd.mem evd evk) evars) then
    err_unknown_evar env evd_rhs evars rhs;

  let (quals, univs) = Vars.sort_and_universes_of_constr (EConstr.Unsafe.to_constr rhs) in
  let quals = Sorts.Quality.Set.diff quals (QGraph.domain (Environ.qualities env)) in
  let quals = Sorts.Quality.(Set.fold (fun q qset -> match q with QVar q -> Sorts.QVar.Set.add q qset | _ -> assert false)) quals Sorts.QVar.Set.empty in
  let quals = Sorts.QVar.Set.diff quals (Sorts.QVar.Map.domain (fst usubst)) in
  let univs = Univ.Level.Set.diff univs (UGraph.domain (Environ.universes env)) in
  let univs = Univ.Level.Set.diff univs (Univ.Level.Map.domain (snd usubst)) in

  let rhs, well_typed = if Sorts.QVar.Set.is_empty quals && Univ.Level.Set.is_empty univs then
    rhs, well_typed
  else begin
    warn_rewrite_rules_break_SR ?loc:rhs_loc Pp.(surround (str "unbound sort and/or levels, defaulting to Type/0") ++ str ".");
    let qsubst = Sorts.QVar.(Set.fold (fun q qmap -> Map.add q Sorts.Quality.qtype qmap) quals Map.empty) in
    let usubst = Univ.Level.(Set.fold (fun l lmap -> Univ.Level.Map.add l set lmap) univs Map.empty) in
    EConstr.Vars.subst_univs_level_constr (qsubst, usubst) rhs, false
    end
  in

  (* The pattern constraints must imply those of the rhs *)
  let well_typed = if well_typed then try
      let evd_boost = Evd.add_univ_constraints evd (Sorts.QVar.Map.fold (fun _ -> Univ.UnivConstraints.union) cstrs Univ.UnivConstraints.empty) in
      let evd' = Typing.check env evd_boost rhs ty in
      let fail pp = warn_rewrite_rules_break_SR ?loc:rhs_loc Pp.(surround (str "universe inconsistency, missing constraints: " ++ pp) ++ str ".") in
      let () = UState.check_uctx_impl ~fail (Evd.ustate evd_boost) (Evd.ustate evd') in
      true
    with Pretype_errors.PretypeError (env, evd, err) ->
      warn_rewrite_rules_break_SR ?loc:rhs_loc
        Pp.(surround (str "universe inconsistency, missing constraints to typecheck the replacement term") ++ str":"
          ++ fnl() ++ Himsg.explain_pretype_error env evd err);
      false
    else false
  in
  let () = if well_typed then try
    let evd' = Typing.check env evd rhs ty in
    let fail pp = warn_rewrite_rules_break_SR ?loc:rhs_loc Pp.(surround (str "possible universe inconsistency, these constraints might not hold: " ++ pp) ++ str ".") in
    let () = UState.check_uctx_impl ~fail (Evd.ustate evd) (Evd.ustate evd') in
    ()
    with Pretype_errors.PretypeError (env, evd, err) ->
      warn_rewrite_rules_break_SR ?loc:rhs_loc
        Pp.(surround (str "possible universe inconsistency, constraints to typecheck the replacement term might not hold") ++ str ":"
          ++ fnl() ++ Himsg.explain_pretype_error env evd err)
  in

  let replacement = EConstr.to_constr ~abort_on_undefined_evars:false evd (EConstr.Vars.subst_univs_level_constr usubst rhs) in

  let rule = { rr_evars = names.evar_names; rr_uctx = { quals = names.sort_names; univs = names.level_names }; esubst; pattern; replacement } in

  let machine =
    match Rewrite_rules_ops.translate_rewrite_rule env evd rule with
    | r -> r
    | exception Rewrite_rules_ops.LocalPatternTranslationError Rewrite_rules_ops.NoHeadSymbol ->
      CErrors.user_err ?loc:pattern_loc Pp.(str "Head head-pattern is not a symbol.")
    | exception Rewrite_rules_ops.LocalPatternTranslationError Rewrite_rules_ops.UnknownEvar _ -> assert false
    | exception Rewrite_rules_ops.LocalPatternTranslationError UnknownQuality q ->
      CErrors.user_err ?loc:rhs_loc
        Pp.(str "Sort " ++ Termops.pr_evd_quality evd q ++ str " appears in the replacement but does not appear in the pattern.")
    | exception Rewrite_rules_ops.LocalPatternTranslationError UnknownLevel lvl ->
      CErrors.user_err ?loc:rhs_loc
        Pp.(str "Universe level " ++ Termops.pr_evd_level evd lvl ++ str " appears in the replacement but does not appear in the pattern.")
  in

  rule, machine

let do_rules id rules =
  let env = Global.env () in
  if not @@ Environ.rewrite_rules_allowed env then raise Environ.(RewriteRulesNotAllowed Rule);
  let rules = List.map interp_rule rules in
  let rewrules_rules, rewrules_machine = List.split rules in
  Global.add_rewrite_rules id { rewrules_rules; rewrules_machine }
