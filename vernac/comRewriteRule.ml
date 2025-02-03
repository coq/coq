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



open Util
open Constr
open Declarations

type state = (int * int Evar.Map.t) * (int * int Int.Map.t) * (int * int Int.Map.t)

let rec is_rel_inst k = function
  | SList.Nil -> true
  | SList.Default _ -> false
  | SList.Cons (t, l) -> kind t = Rel k && is_rel_inst (succ k) l

let update_invtbl ~loc env evd evk (curvar, tbl) =
  curvar, (succ curvar, tbl |> Evar.Map.update evk @@ function
  | None -> Some curvar
  | Some k as c when k = curvar -> c
  | Some k ->
      CErrors.user_err ?loc
        Pp.(str "Variable "
          ++ Termops.pr_existential_key env evd evk
          ++ str" is bound multiple times in the pattern (holes number "
          ++ int k ++ str" and " ++ int curvar ++ str")."))

let update_invtblu1 ~loc evd lvlold lvl (curvaru, tbl) =
  succ curvaru, tbl |> Int.Map.update lvl @@ function
    | None -> Some curvaru
    | Some k as c when k = curvaru -> c
    | Some k ->
        CErrors.user_err ?loc
          Pp.(str "Universe variable "
            ++ Termops.pr_evd_level evd lvlold
            ++ str" is bound multiple times in the pattern (holes number "
            ++ int k ++ str" and " ++ int curvaru ++ str").")

let update_invtblq1 ~loc evd qold qvar (curvarq, tbl) =
  succ curvarq, tbl |> Int.Map.update qvar @@ function
    | None -> Some curvarq
    | Some k as c when k = curvarq -> c
    | Some k ->
        CErrors.user_err ?loc
          Pp.(str "Sort variable "
            ++ Sorts.Quality.pr (Termops.pr_evd_qvar evd) qold
            ++ str" is bound multiple times in the pattern (holes number "
            ++ int k ++ str" and " ++ int curvarq ++ str").")

let safe_quality_pattern_of_quality ~loc evd qsubst stateq q =
  match Sorts.Quality.(subst (subst_fn qsubst) q) with
  | QConstant qc -> stateq, PQConstant qc
  | QVar qv ->
    let qio = Sorts.QVar.var_index qv in
    let stateq = Option.fold_right (update_invtblq1 ~loc evd q) qio stateq in
    stateq, PQVar qio

let update_invtblu ~loc evd (qsubst, usubst) (state, stateq, stateu : state) u : state * _ =
  let (q, u) = u |> UVars.Instance.to_array in
  let stateq, maskq = Array.fold_left_map (safe_quality_pattern_of_quality ~loc evd qsubst) stateq q
  in
  let stateu, masku = Array.fold_left_map (fun stateu lvlold ->
      let lvlnew = Univ.Level.var_index @@ Univ.subst_univs_level_level usubst lvlold in
      Option.fold_right (update_invtblu1 ~loc evd lvlold) lvlnew stateu, lvlnew
    ) stateu u
  in
  (state, stateq, stateu), (maskq, masku)

let universe_level_subst_var_index usubst u =
  match Univ.Universe.level u with
    | None -> None
    | Some lvlold ->
        let lvl = Univ.subst_univs_level_level usubst lvlold in
        Option.map (fun lvl -> lvlold, lvl) @@ Univ.Level.var_index lvl

let safe_sort_pattern_of_sort ~loc evd (qsubst, usubst) (st, sq, su as state) s =
  let open Sorts in
  match s with
  | Type u ->
      begin match universe_level_subst_var_index usubst u with
      | None -> state, PSType None
      | Some (lvlold, lvl) ->
        (st, sq, update_invtblu1 ~loc evd lvlold lvl su), PSType (Some lvl)
      end
  | SProp -> state, PSSProp
  | Prop -> state, PSProp
  | Set -> state, PSSet
  | QSort (qold, u) ->
      let sq, bq =
        match Sorts.Quality.(var_index @@ subst_fn qsubst qold) with
        | Some q -> update_invtblq1 ~loc evd (QVar qold) q sq, Some q
        | None -> sq, None
      in
      let su, ba =
        match universe_level_subst_var_index usubst u with
        | Some (lvlold, lvl) -> update_invtblu1 ~loc evd lvlold lvl su, Some lvl
        | None -> su, None
      in
      (st, sq, su), PSQSort (bq, ba)


let warn_irrelevant_pattern =
  CWarnings.create ~name:"irrelevant-pattern" ~category:CWarnings.CoreCategories.rewrite_rules
    Pp.(fun () -> str "This subpattern is irrelevant and can never be matched against.")

let warn_eta_in_pattern =
  CWarnings.create ~name:"eta-in-pattern" ~category:CWarnings.CoreCategories.rewrite_rules Fun.id

let warn_redex_in_rewrite_rules =
  CWarnings.create ~name:"redex-in-rewrite-rules" ~category:CWarnings.CoreCategories.rewrite_rules
  Pp.(fun redex -> str "This pattern contains a" ++ redex ++ str " which may prevent this rule from being triggered.")

let rec check_may_eta ~loc env evd t =
  match EConstr.kind evd (Reductionops.whd_all env evd t) with
  | Prod _ ->
      warn_eta_in_pattern ?loc
        Pp.(str "This subpattern has a product type, but pattern-matching is not done modulo eta, so this rule may not trigger at required times.")
  | Sort _ -> ()
  | Ind (ind, u) ->
      let specif = Inductive.lookup_mind_specif env ind in
      if not @@ Inductive.is_primitive_record specif then () else
        warn_eta_in_pattern ?loc
          Pp.(str "This subpattern has a primitive record type, but pattern-matching is not done modulo eta, so this rule may not trigger at required times.")
  | App (i, _) -> check_may_eta ~loc env evd i
  | _ ->
      warn_eta_in_pattern ?loc
        Pp.(str "This subpattern has a yet unknown type, which may be a product type, but pattern-matching is not done modulo eta, so this rule may not trigger at required times.")

let test_may_eta ~loc env evd constr =
  let t = Retyping.get_type_of env evd constr in
  let () = check_may_eta ~loc env evd t in
  ()


let rec safe_pattern_of_constr_aux ~loc env evd usubst depth state t = Constr.kind t |> function
  | App (f, args) ->
      let state, (head, elims) = safe_pattern_of_constr_aux ~loc env evd usubst depth state f in
      let state, pargs = Array.fold_left_map (safe_arg_pattern_of_constr ~loc env evd usubst depth) state args in
      state, (head, elims @ [PEApp pargs])
  | Case (ci, u, params, (ret, _), _, c, brs) ->
      let mib, mip = Inductive.lookup_mind_specif env ci.ci_ind in

      let state, mask = update_invtblu ~loc evd usubst state u in
      let state, (head, elims) = safe_pattern_of_constr_aux ~loc env evd usubst depth state c in

      let paramdecl = Vars.subst_instance_context u mib.mind_params_ctxt in
      let paramsubst = Vars.subst_of_rel_context_instance paramdecl params in

      let state, pret =
        let (nas, p) = ret in
        let realdecls, _ = List.chop mip.mind_nrealdecls mip.mind_arity_ctxt in
        let self =
          let args = Context.Rel.instance mkRel 0 mip.mind_arity_ctxt in
          let inst = UVars.Instance.(abstract_instance (length u)) in
          mkApp (mkIndU (ci.ci_ind, inst), args)
        in
        let na = Context.make_annot Anonymous mip.mind_relevance in
        let realdecls = Context.Rel.Declaration.LocalAssum (na, self) :: realdecls in
        let realdecls =
          Inductive.instantiate_context u paramsubst nas realdecls
        in
        let p_env = Environ.push_rel_context realdecls env in
        safe_arg_pattern_of_constr ~loc p_env evd usubst (depth + Array.length nas) state p
      in
      let do_one_branch i state (nas, br) =
        let (ctx, cty) = mip.mind_nf_lc.(i) in
        let bctx, _ = List.chop mip.mind_consnrealdecls.(i) ctx in
        let bctx = Inductive.instantiate_context u paramsubst nas bctx in
        let br_env = Environ.push_rel_context bctx env in
        safe_arg_pattern_of_constr ~loc br_env evd usubst (depth + Array.length nas) state br
      in
      let state, pbrs = Array.fold_left_map_i do_one_branch state brs in
      state, (head, elims @ [PECase (ci.ci_ind, mask, pret, pbrs)])
  | Proj (p, _, c) ->
      let state, (head, elims) = safe_pattern_of_constr_aux ~loc env evd usubst depth state c in
      state, (head, elims @ [PEProj (Projection.repr p)])
  | _ ->
      let state, head = safe_head_pattern_of_constr ~loc env evd usubst depth state t in
      state, (head, [])

and safe_pattern_of_constr ~loc env evd usubst depth state t =
  begin match EConstr.ERelevance.kind evd @@ Retyping.relevance_of_term env evd (EConstr.of_constr t) with
  | Sorts.Irrelevant -> warn_irrelevant_pattern ?loc ()
  | Sorts.RelevanceVar _ -> () (* FIXME *)
  | Sorts.Relevant -> ()
  end;
  safe_pattern_of_constr_aux ~loc env evd usubst depth state t

and safe_head_pattern_of_constr ~loc env evd usubst depth state t = Constr.kind t |> function
  | Const (c, u) when Environ.is_symbol env c ->
    let state, mask = update_invtblu ~loc evd usubst state u in
    state, PHSymbol (c, mask)
  | Rel i ->
    assert (i <= depth);
    state, PHRel i
  | Sort s ->
    let state, ps = safe_sort_pattern_of_sort ~loc evd usubst state s in
    state, PHSort ps
  | Ind (ind, u) ->
    let state, mask = update_invtblu ~loc evd usubst state u in
    state, PHInd (ind, mask)
  | Construct (c, u) ->
    let state, mask = update_invtblu ~loc evd usubst state u in
    state, PHConstr (c, mask)
  | Int i -> state, PHInt i
  | Float f -> state, PHFloat f
  | String s -> state, PHString s
  | Lambda _ ->
    let (ntys, b) = Term.decompose_lambda t in
    let tys = Array.rev_of_list ntys in
    let (state, env), ptys = Array.fold_left_map_i
      (fun i (state, env) (na, ty) ->
          let state, p = safe_arg_pattern_of_constr ~loc env evd usubst (depth+i) state ty in
          (state, Environ.push_rel (LocalAssum (na, ty)) env), p)
        (state, env) tys
    in
    let state, pbod = safe_arg_pattern_of_constr ~loc env evd usubst (depth + Array.length tys) state b in
    state, PHLambda (ptys, pbod)
  | Prod _ ->
    let (ntys, b) = Term.decompose_prod t in
    let tys = Array.rev_of_list ntys in
    let (state, env), ptys = Array.fold_left_map_i
      (fun i (state, env) (na, ty) ->
          let state, p = safe_arg_pattern_of_constr ~loc env evd usubst (depth+i) state ty in
          (state, Environ.push_rel (LocalAssum (na, ty)) env), p)
        (state, env) tys
    in
    let state, pbod = safe_arg_pattern_of_constr ~loc env evd usubst (depth + Array.length tys) state b in
    state, PHProd (ptys, pbod)
  | _ ->
    CErrors.user_err ?loc Pp.(str "Subterm not recognised as pattern: " ++ Printer.safe_pr_lconstr_env env evd t)

and safe_arg_pattern_of_constr ~loc env evd usubst depth (st, stateq, stateu as state) t = Constr.kind t |> function
  | Evar (evk, inst) ->
    let EvarInfo evi = Evd.find evd evk in
    (match snd (Evd.evar_source evi) with
    | Evar_kinds.MatchingVar (Evar_kinds.FirstOrderPatVar id) ->
      let holei, st = update_invtbl ~loc env evd evk st in
      if not @@ is_rel_inst 1 inst then
        CErrors.user_err ?loc
          Pp.(str "In " ++ Printer.safe_pr_lconstr_env env evd (of_kind (Evar (evk, inst)))
            ++ str ", variable "
            ++ Termops.pr_existential_key env evd evk
            ++ str" appears with a non-trivial instantiation.");
      if Evd.evar_hyps evi |> Environ.named_context_of_val |> Context.Named.length <> SList.length inst then
        CErrors.user_err ?loc Pp.(str "Pattern variable cannot access the whole context: " ++ Printer.safe_pr_lconstr_env env evd t);
      (st, stateq, stateu), EHole holei
    | Evar_kinds.NamedHole _ -> CErrors.user_err ?loc Pp.(str "Named holes are not supported, you must use regular evars: " ++ Printer.safe_pr_lconstr_env env evd t)
    | _ ->
      if Option.is_empty @@ Evd.evar_ident evk evd then state, EHoleIgnored else
        CErrors.user_err ?loc Pp.(str "Named evar in unsupported context: " ++ Printer.safe_pr_lconstr_env env evd t)
    )
  | _ ->
    test_may_eta ~loc env evd (EConstr.of_constr t);
    let state, p = safe_pattern_of_constr ~loc env evd usubst depth state t in
    state, ERigid p


(* relocation of evars into de Bruijn indices *)
let rec evar_subst evmap evd k t =
  match EConstr.kind evd t with
  | Evar (evk, inst) -> begin
    match Evar.Map.find_opt evk evmap with
    | None -> t
    | Some (n, vars) ->
        let head = EConstr.mkRel (n + k) in
        let Evd.EvarInfo evi = Evd.find evd evk in
        let body = EConstr.mkApp (head, vars) in
        let inst = inst |> SList.Smart.map (evar_subst evmap evd k) in
        Evd.instantiate_evar_array evd evi body inst
    end
  | _ -> EConstr.map_with_binders evd succ (evar_subst evmap evd) k t

let test_projection_apps env evd ~loc ind args =
  let specif = Inductive.lookup_mind_specif env ind in
  if not @@ Inductive.is_primitive_record specif then () else
  if Array.for_all_i (fun i arg ->
    match arg with
    | EHole _ | EHoleIgnored -> true
    | ERigid (_, []) -> false
    | ERigid (_, elims) ->
      match List.last elims with
      | PEProj p -> Environ.QInd.equal env (Projection.Repr.inductive p) ind && Projection.Repr.arg p = i
      | _ -> false
  ) 0 args then
    warn_redex_in_rewrite_rules ?loc Pp.(str " subpattern compatible with an eta-long form for " ++ Id.print (snd specif).mind_typename ++ str"," )

let rec test_pattern_redex env evd ~loc = function
  | PHLambda _, PEApp _ :: _ -> warn_redex_in_rewrite_rules ?loc (Pp.str " beta redex")
  | PHConstr _, (PECase _ | PEProj _) :: _ -> warn_redex_in_rewrite_rules ?loc (Pp.str " iota redex")
  | PHConstr _, PEApp _ :: (PECase _ | PEProj _) :: _ -> warn_redex_in_rewrite_rules ?loc (Pp.str " iota redex")
  | PHLambda _, _ -> warn_redex_in_rewrite_rules ?loc (Pp.str " lambda pattern")
  | PHConstr (c, _) as head, PEApp args :: elims -> test_projection_apps env evd ~loc (fst c) args; Array.iter (test_pattern_redex_aux env evd ~loc) args; test_pattern_redex env evd ~loc (head, elims)
  | head, PEApp args :: elims -> Array.iter (test_pattern_redex_aux env evd ~loc) args; test_pattern_redex env evd ~loc (head, elims)
  | head, PECase (_, _, ret, brs) :: elims -> test_pattern_redex_aux env evd ~loc ret; Array.iter (test_pattern_redex_aux env evd ~loc) brs; test_pattern_redex env evd ~loc (head, elims)
  | head, PEProj _ :: elims -> test_pattern_redex env evd ~loc (head, elims)
  | PHProd (tys, bod), [] -> Array.iter (test_pattern_redex_aux env evd ~loc) tys; test_pattern_redex_aux env evd ~loc bod
  | (PHRel _ | PHInt _ | PHFloat _ | PHString _ | PHSort _ | PHInd _ | PHConstr _ | PHSymbol _), [] -> ()
and test_pattern_redex_aux env evd ~loc = function
  | EHole _ | EHoleIgnored -> ()
  | ERigid p -> test_pattern_redex env evd ~loc p


let warn_rewrite_rules_break_SR =
  CWarnings.create ~name:"rewrite-rules-break-SR" ~category:CWarnings.CoreCategories.rewrite_rules
    Pp.(fun reason ->
        str "This rewrite rule breaks subject reduction" ++ spc() ++
        surround reason ++ str ".")

let interp_rule (udecl, lhs, rhs: Constrexpr.universe_decl_expr option * _ * _) =
  let env = Global.env () in
  let evd = Evd.from_env env in

  (* 1. Read universe level binders, leaving out the constraints for now *)
  (* Inlined the relevant part of Constrintern.interp_univ_decl *)
  let evd, udecl =
    let open CAst in let open UState in
    match udecl with
    | None -> evd, default_univ_decl
    | Some udecl ->
    let evd, qualities = List.fold_left_map (fun evd lid ->
        Evd.new_quality_variable ?loc:lid.loc ~name:lid.v evd)
        evd
        udecl.univdecl_qualities
    in
    let evd, instance = List.fold_left_map (fun evd lid ->
        Evd.new_univ_level_variable ?loc:lid.loc univ_rigid ~name:lid.v evd)
        evd
        udecl.univdecl_instance
    in
    let cstrs =
      udecl.univdecl_constraints |> List.to_seq
      |> Seq.map (Constrintern.interp_univ_constraint evd)
      |> Univ.Constraints.of_seq
    in
    let decl = {
      univdecl_qualities = qualities;
      univdecl_extensible_qualities = udecl.univdecl_extensible_qualities;
      univdecl_instance = instance;
      univdecl_extensible_instance = udecl.univdecl_extensible_instance;
      univdecl_constraints = cstrs;
      univdecl_extensible_constraints = udecl.univdecl_extensible_constraints;
    } in
    evd, decl
  in
  let nvarqs = List.length udecl.univdecl_qualities in
  let nvarus = List.length udecl.univdecl_instance in


  (* 2. Read left hand side, into a pattern *)
  (* The udecl constraints must be implied by the lhs (and not the reverse) *)

  let lhs_loc = lhs.CAst.loc in
  let rhs_loc = rhs.CAst.loc in

  let lhs = Constrintern.(intern_gen WithoutTypeConstraint env evd lhs) in
  let flags = { Pretyping.no_classes_no_fail_inference_flags with undeclared_evars_patvars = true; patvars_abstract = true; expand_evars = false; solve_unification_constraints = false } in
  let evd, lhs, typ = Pretyping.understand_tcc_ty ~flags env evd lhs in

  let evd = Evd.minimize_universes evd in
  let _qvars, uvars = EConstr.universes_of_constr evd lhs in
  let evd = Evd.restrict_universe_context evd uvars in
  let uctx, uctx' = UState.check_univ_decl_rev (Evd.ustate evd) udecl in

  let usubst =
    let inst, auctx = UVars.abstract_universes uctx' in
    UVars.make_instance_subst inst
  in

  let ((nvars', invtbl), (nvarqs', invtblq), (nvarus', invtblu)), (head_pat, elims) =
    safe_pattern_of_constr ~loc:lhs_loc env evd usubst 0 ((1, Evar.Map.empty), (0, Int.Map.empty), (0, Int.Map.empty)) (EConstr.Unsafe.to_constr lhs)
  in
  let () = test_pattern_redex env evd ~loc:lhs_loc (head_pat, elims) in

  let head_symbol, head_umask = match head_pat with PHSymbol (symb, mask) -> symb, mask | _ ->
    CErrors.user_err ?loc:lhs_loc
    Pp.(str "Head head-pattern is not a symbol.")
  in
  if nvarus <> nvarus' then begin
    assert (nvarus' < nvarus);
    CErrors.user_err ?loc:lhs_loc
      Pp.(str "Not all universe level variables appear in the pattern.")
  end;
  if nvarqs <> nvarqs' then begin
    assert (nvarqs' < nvarqs);
    CErrors.user_err ?loc:lhs_loc
      Pp.(str "Not all sort variables appear in the pattern.")
  end;

  let update_invtbl evd evk n =
    let Evd.EvarInfo evi = Evd.find evd evk in
    let vars = Evd.evar_hyps evi |> Environ.named_context_of_val |> Context.Named.instance EConstr.mkVar in
    (n, vars)
  in

  let invtbl = Evar.Map.mapi (update_invtbl evd) invtbl in

  (* 3. Read right hand side *)
  (* The udecl constraints (or, if none, the lhs constraints) must imply those of the rhs *)
  let evd = Evd.set_universe_context evd uctx in
  let rhs = Constrintern.(intern_gen WithoutTypeConstraint env evd rhs) in
  let flags = { Pretyping.no_classes_no_fail_inference_flags with patvars_abstract = true } in
  let evd', rhs =
    try Pretyping.understand_tcc ~flags env evd ~expected_type:(OfType typ) rhs
    with Type_errors.TypeError _ | Pretype_errors.PretypeError _ ->
      warn_rewrite_rules_break_SR ?loc:rhs_loc (Pp.str "the replacement term doesn't have the type of the pattern");
      Pretyping.understand_tcc ~flags env evd rhs
  in

  let evd' = Evd.minimize_universes evd' in
  let _qvars', uvars' = EConstr.universes_of_constr evd' rhs in
  let evd' = Evd.restrict_universe_context evd' (Univ.Level.Set.union uvars uvars') in
  let fail pp = warn_rewrite_rules_break_SR ?loc:rhs_loc Pp.(str "universe inconsistency, missing constraints: " ++ pp) in
  let () = UState.check_uctx_impl ~fail (Evd.ustate evd) (Evd.ustate evd') in
  let evd = evd' in

  let rhs =
    let rhs' = evar_subst invtbl evd 0 rhs in
    match EConstr.to_constr_opt evd rhs' with
    | Some rhs -> rhs
    | None ->
      let pr_unresolved_evar e =
        Pp.(hov 2 (str"- " ++ Printer.pr_existential_key env evd e ++  str ": " ++
          Himsg.explain_pretype_error env evd (Pretype_errors.UnsolvableImplicit (e,None))))
      in
      CErrors.user_err ?loc:rhs_loc Pp.(hov 0 begin
        str "The replacement term contains unresolved implicit arguments:"++ fnl () ++
        str "  " ++ Printer.pr_econstr_env env evd rhs ++ fnl () ++
        str "More precisely: " ++ fnl () ++
        v 0 (prlist_with_sep cut pr_unresolved_evar (Evar.Set.elements (Evarutil.undefined_evars_of_term evd rhs')))
      end)
  in

  let rhs = Vars.subst_univs_level_constr usubst rhs in

  let test_qvar q =
    match Sorts.QVar.var_index q with
    | Some -1 ->
        CErrors.user_err ?loc:rhs_loc
          Pp.(str "Sort variable " ++ Termops.pr_evd_qvar evd q ++ str " appears in the replacement but does not appear in the pattern.")
    | Some n when n < 0 || n > nvarqs' -> CErrors.anomaly Pp.(str "Unknown sort variable in rewrite rule.")
    | Some _ -> ()
    | None ->
        if not @@ Sorts.QVar.Set.mem q (evd |> Evd.sort_context_set |> fst |> fst) then
          CErrors.user_err ?loc:rhs_loc
            Pp.(str "Sort variable " ++ Termops.pr_evd_qvar evd q ++ str " appears in the replacement but does not appear in the pattern.")
  in

  let test_level ?(alg_ok=false) lvl =
    match Univ.Level.var_index lvl with
    | Some -1 ->
        CErrors.user_err ?loc:rhs_loc
          Pp.(str "Universe level variable " ++ Termops.pr_evd_level evd lvl ++ str " appears in the replacement but does not appear in the pattern.")
    | Some n when n < 0 || n > nvarus' -> CErrors.anomaly Pp.(str "Unknown universe level variable in rewrite rule")
    | Some _ -> ()
    | None ->
      match UGraph.check_declared_universes (Environ.universes env) (Univ.Level.Set.singleton lvl) with
      | Ok () -> ()
      | Error l ->
        let l = Univ.Level.Set.elements l in
        CErrors.user_err ?loc:rhs_loc
          Pp.(str "Universe level " ++
              prlist_with_sep spc (Termops.pr_evd_level evd) l ++
              str " appears in the replacement but does not appear in the pattern.")
  in

  let () =
    let qs, us = Vars.sort_and_universes_of_constr rhs in
    Sorts.QVar.Set.iter test_qvar qs;
    Univ.Level.Set.iter test_level us
  in

  head_symbol, { nvars = (nvars' - 1, nvarqs', nvarus'); lhs_pat = head_umask, elims; rhs }

let do_rules id rules =
  let env = Global.env () in
  if not @@ Environ.rewrite_rules_allowed env then raise Environ.(RewriteRulesNotAllowed Rule);
  let body = { rewrules_rules = List.map interp_rule rules } in
  Global.add_rewrite_rules id body
