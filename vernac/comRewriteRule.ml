(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
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

type state = (int * int Evar.Map.t) * (int * int Int.Map.t) * (int * (int * bool) Int.Map.t)

let update_invtbl ~loc env evd evk (curvar, tbl) =
  succ curvar, tbl |> Evar.Map.update evk @@ function
  | None -> Some curvar
  | Some k as c when k = curvar -> c
  | Some k ->
      CErrors.user_err ?loc
        Pp.(str "Variable "
          ++ Printer.safe_pr_lconstr_env env evd (of_kind (Evar (evk, SList.empty)))
          ++ str" already taken for hole " ++ int k
          ++ str" but used here for hole " ++ int curvar
          ++ str".")

let update_invtblu1 ~loc ~(alg:bool) evd lvl (curvaru, tbl) =
  succ curvaru, tbl |> Int.Map.update lvl @@ function
    | None -> Some (curvaru, alg)
    | Some (k, alg') as c when k = curvaru && alg = alg' -> c
    | Some (k, _) ->
        CErrors.user_err ?loc
          Pp.(str "Universe variable "
            ++ Termops.pr_evd_level evd (Univ.Level.var lvl)
            ++ str" already taken for hole " ++ int k
            ++ str" but used here for hole " ++ int curvaru
            ++ str".")

let update_invtblq1 ~loc evd q (curvarq, tbl) =
  succ curvarq, tbl |> Int.Map.update q @@ function
    | None -> Some curvarq
    | Some k as c when k = curvarq -> c
    | Some k ->
        CErrors.user_err ?loc
          Pp.(str "Sort variable "
            ++ Termops.pr_evd_qvar evd (Sorts.QVar.make_var q)
            ++ str" already taken for hole " ++ int k
            ++ str" but used here for hole " ++ int curvarq
            ++ str".")

let update_invtblu ~loc evd (state, stateq, stateu : state) u : state * _ =
  let (q, u) = u |> UVars.Instance.to_array in
  let stateq, maskq = Array.fold_left_map (fun stateq qvar ->
    match Sorts.Quality.var_index qvar with
    | Some lvl -> update_invtblq1 ~loc evd lvl stateq, true
    | None -> stateq, false
  ) stateq q
  in
  let stateu, masku = Array.fold_left_map (fun stateu lvl ->
      match Univ.Level.var_index lvl with
      | Some lvl -> update_invtblu1 ~loc ~alg:false evd lvl stateu, true
      | None -> stateu, false
    ) stateu u
  in
  let mask = if Array.exists Fun.id maskq || Array.exists Fun.id masku then Some (maskq, masku) else None in
  (state, stateq, stateu), mask

let universe_level_var_index u =
  match Univ.Universe.level u with
    | None -> None
    | Some lvl -> Univ.Level.var_index lvl

let safe_sort_pattern_of_sort ~loc evd (st, sq, su as state) s =
  let open Sorts in
  match s with
  | Type u ->
      begin match universe_level_var_index u with
      | None -> state, PSType false
      | Some lvl ->
        (st, sq, update_invtblu1 ~loc ~alg:true evd lvl su), PSType true
      end
  | SProp -> state, PSSProp
  | Prop -> state, PSProp
  | Set -> state, PSSet
  | QSort (q, u) ->
      let sq, bq =
        match Sorts.QVar.var_index q with
        | Some q -> update_invtblq1 ~loc evd q sq, true
        | None -> sq, false
      in
      let su, ba =
        match universe_level_var_index u with
        | Some lvl -> update_invtblu1 ~loc ~alg:true evd lvl su, true
        | None -> su, false
      in
      (st, sq, su), PSQSort (bq, ba)


let rec safe_pattern_of_constr ~loc env depth state t = Constr.kind t |> function
  | App (f, args) ->
      let state, (head, elims) = safe_pattern_of_constr ~loc env depth state f in
      let state, pargs = Array.fold_left_map (safe_arg_pattern_of_constr ~loc env depth) state args in
      state, (head, elims @ [PEApp pargs])
  | Case (ci, u, _, (ret, _), _, c, brs) ->
      let state, mask = update_invtblu ~loc (snd env) state u in
      let state, (head, elims) = safe_pattern_of_constr ~loc env depth state c in
      let state, pret = safe_deep_pattern_of_constr ~loc env depth state ret in
      let state, pbrs = Array.fold_left_map (safe_deep_pattern_of_constr ~loc env depth) state brs in
      state, (head, elims @ [PECase (ci.ci_ind, mask, pret, pbrs)])
  | Proj (p, _, c) ->
      let state, (head, elims) = safe_pattern_of_constr ~loc env depth state c in
      state, (head, elims @ [PEProj p])
  | _ ->
      let state, head = safe_head_pattern_of_constr ~loc env depth state t in
      state, (head, [])

and safe_head_pattern_of_constr ~loc env depth state t = Constr.kind t |> function
  | Const (c, u) when Environ.is_symbol (fst env) c ->
    let state, mask = update_invtblu ~loc (snd env) state u in
    state, PHSymbol (c, mask)
  | Rel i ->
    assert (i <= depth);
    state, PHRel i
  | Sort s ->
    let state, ps = safe_sort_pattern_of_sort ~loc (snd env) state s in
    state, PHSort ps
  | Ind (ind, u) ->
    let state, mask = update_invtblu ~loc (snd env) state u in
    state, PHInd (ind, mask)
  | Construct (c, u) ->
    let state, mask = update_invtblu ~loc (snd env) state u in
    state, PHConstr (c, mask)
  | Int i -> state, PHInt i
  | Float f -> state, PHFloat f
  | Lambda _ ->
    let (ntys, b) = Term.decompose_lambda t in
    let tys = Array.of_list (List.rev_map snd ntys) in
    let state, ptys = Array.fold_left_map_i (fun i state ty -> safe_arg_pattern_of_constr ~loc env (depth+i) state ty) state tys in
    let state, pbod = safe_arg_pattern_of_constr ~loc env (depth + Array.length tys) state b in
    state, PHLambda (ptys, pbod)
  | Prod _ ->
    let (ntys, b) = Term.decompose_prod t in
    let tys = Array.of_list (List.rev_map snd ntys) in
    let state, ptys = Array.fold_left_map_i (fun i state ty -> safe_arg_pattern_of_constr ~loc env (depth+i) state ty) state tys in
    let state, pbod = safe_arg_pattern_of_constr ~loc env (depth + Array.length tys) state b in
    state, PHProd (ptys, pbod)
  | _ ->
    CErrors.user_err ?loc Pp.(str "Subterm not recognised as pattern: " ++ Printer.safe_pr_lconstr_env (fst env) (snd env) t)

and safe_arg_pattern_of_constr ~loc (env, evd as envevd) depth (st, stateq, stateu as state) t = Constr.kind t |> function
  | Evar (evk, inst) ->
    let EvarInfo evi = Evd.find evd evk in
    (match snd (Evd.evar_source evi) with
    | Evar_kinds.MatchingVar (Evar_kinds.FirstOrderPatVar id) ->
      if Evd.evar_hyps evi |> Environ.named_context_of_val |> Context.Named.length <> depth then
        CErrors.user_err ?loc Pp.(str "Pattern variable cannot access the whole context : " ++ Printer.safe_pr_lconstr_env env evd t);
      let st = update_invtbl ~loc env evd evk st in
      (st, stateq, stateu), EHole
    | Evar_kinds.NamedHole _ -> CErrors.user_err ?loc Pp.(str "Named hole are not supported, you must use regular evars: " ++ Printer.safe_pr_lconstr_env env evd t)
    | _ ->
      if Option.is_empty @@ Evd.evar_ident evk evd then state, EHoleIgnored else
        CErrors.user_err ?loc Pp.(str "Named evar in unsupported context: " ++ Printer.safe_pr_lconstr_env env evd t)
    )
  | _ ->
    let state, p = safe_pattern_of_constr ~loc envevd depth state t in
    state, ERigid p

and safe_deep_pattern_of_constr ~loc env depth state p = safe_arg_pattern_of_constr ~loc env (depth + Array.length (fst p)) state (snd p)

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

let warn_redex_in_rewrite_rules = "redex-in-rewrite-rules"

let redex_in_rewrite_rules_warning =
  CWarnings.create_warning ~name:warn_redex_in_rewrite_rules ~default:CWarnings.Enabled ()

let redex_in_rewrite_rules_msg = CWarnings.create_msg redex_in_rewrite_rules_warning ()
let warn_redex_in_rewrite_rules ~loc redex =
  CWarnings.warn redex_in_rewrite_rules_msg ?loc redex
let () = CWarnings.register_printer redex_in_rewrite_rules_msg
  (fun redex -> Pp.(str "This pattern contains a" ++ redex ++ str " which may prevent this rule from being triggered"))

let test_projection_apps env evd ~loc ind args =
  let specif = Inductive.lookup_mind_specif env ind in
  if not @@ Inductive.is_primitive_record specif then () else
  if Array.for_all_i (fun i arg ->
    match arg with
    | EHole | EHoleIgnored -> true
    | ERigid (_, []) -> false
    | ERigid (_, elims) ->
      match List.last elims with
      | PEProj p -> Ind.CanOrd.equal (Projection.inductive p) ind && Projection.arg p = i
      | _ -> false
  ) 0 args then
    warn_redex_in_rewrite_rules ~loc Pp.(str " subpattern compatible with an eta-long form for " ++ Id.print (snd specif).mind_typename ++ str"," )

let rec test_pattern_redex env evd ~loc = function
  | PHLambda _, PEApp _ :: _ -> warn_redex_in_rewrite_rules ~loc (Pp.str " beta redex")
  | PHConstr _, (PECase _ | PEProj _) :: _ -> warn_redex_in_rewrite_rules ~loc (Pp.str " iota redex")
  | PHLambda _, _ -> warn_redex_in_rewrite_rules ~loc (Pp.str " lambda pattern")
  | PHConstr (c, _) as head, PEApp args :: elims -> test_projection_apps env evd ~loc (fst c) args; Array.iter (test_pattern_redex_aux env evd ~loc) args; test_pattern_redex env evd ~loc (head, elims)
  | head, PEApp args :: elims -> Array.iter (test_pattern_redex_aux env evd ~loc) args; test_pattern_redex env evd ~loc (head, elims)
  | head, PECase (_, _, ret, brs) :: elims -> test_pattern_redex_aux env evd ~loc ret; Array.iter (test_pattern_redex_aux env evd ~loc) brs; test_pattern_redex env evd ~loc (head, elims)
  | head, PEProj _ :: elims -> test_pattern_redex env evd ~loc (head, elims)
  | PHProd (tys, bod), [] -> Array.iter (test_pattern_redex_aux env evd ~loc) tys; test_pattern_redex_aux env evd ~loc bod
  | (PHRel _ | PHInt _ | PHFloat _ | PHSort _ | PHInd _ | PHConstr _ | PHSymbol _), [] -> ()
and test_pattern_redex_aux env evd ~loc = function
  | EHole | EHoleIgnored -> ()
  | ERigid p -> test_pattern_redex env evd ~loc p

let interp_rule (udecl, lhs, rhs) =
  let env = Global.env () in
  let poly = Option.has_some udecl in
  let evd, udecl = Constrintern.interp_univ_decl_opt env udecl in

  let lhs_loc = lhs.CAst.loc in
  let rhs_loc = rhs.CAst.loc in

  let lhs = Constrintern.(intern_gen WithoutTypeConstraint ~pattern_mode:true env evd lhs) in
  let flags = { Pretyping.no_classes_no_fail_inference_flags with unify_patvars = false; expand_evars = false; solve_unification_constraints = false } in
  let evd, lhs = Pretyping.understand_tcc ~flags env evd lhs in
  (* let evd, lhs, typ = Pretyping.understand_tcc_ty ~flags env evd lhs in *)
  (* let patvars, lhs = Constrintern.intern_constr_pattern env evd lhs in *)

  let evd = Evd.minimize_universes evd in
  let _qvars, uvars = EConstr.universes_of_constr evd lhs in
  let evd = Evd.restrict_universe_context evd uvars in
  let univs = Evd.check_univ_decl ~poly evd udecl in

  let (nvarqs, nvarus), usubst =
    match fst univs with
    | Monomorphic_entry _ -> (0, 0), UVars.empty_sort_subst
    | Polymorphic_entry ctx ->
        UVars.UContext.size ctx,
        let inst, auctx = UVars.abstract_universes ctx in
        UVars.make_instance_subst inst
  in

  let lhs = Vars.subst_univs_level_constr usubst (EConstr.Unsafe.to_constr lhs) in

  let ((nvars', invtbl), (nvarqs', invtblq), (nvarus', invtblu)), (head_pat, elims) =
    safe_pattern_of_constr ~loc:lhs_loc (env, evd) 0 ((1, Evar.Map.empty), (0, Int.Map.empty), (0, Int.Map.empty)) lhs
  in
  let () = test_pattern_redex env evd ~loc:lhs_loc (head_pat, elims) in
  let _inv_tbl_dbg = Evar.Map.bindings invtbl in
  let head_symbol, head_umask = match head_pat with PHSymbol (symb, mask) -> symb, mask | _ ->
    CErrors.user_err ?loc:lhs_loc
    Pp.(str "Head pattern is not a symbol.")
  in
  if nvarus <> nvarus' then begin
    assert (nvarus' < nvarus);
    CErrors.user_err ?loc:lhs_loc
      Pp.(str "Not all universe level variables appear in the lhs")
  end;
  if nvarqs <> nvarqs' then begin
    assert (nvarqs' < nvarqs);
    CErrors.user_err ?loc:lhs_loc
      Pp.(str "Not all sort variables appear in the lhs")
  end;

  let update_invtbl evd evk n invtbl =
    let Evd.EvarInfo evi = Evd.find evd evk in
    let vars = Evd.evar_hyps evi |> Environ.named_context_of_val |> Context.Named.instance EConstr.mkVar in
    Evar.Map.add evk (n, vars) invtbl
  in

  let rhs = Constrintern.(intern_gen WithoutTypeConstraint env evd rhs) in
  let flags = { Pretyping.no_classes_no_fail_inference_flags with unify_patvars = false } in
  let evd, rhs = Pretyping.understand_tcc ~flags env evd (* ~expected_type:(OfType typ) *) rhs in
  let invtbl = Evar.Map.fold (update_invtbl evd) invtbl Evar.Map.empty in

  let rhs = evar_subst invtbl evd 0 rhs in
  let rhs = match EConstr.to_constr_opt evd rhs with
    | Some rhs -> rhs
    | None ->
    CErrors.user_err ?loc:rhs_loc
      Pp.(str "Some variable appears in rhs (" ++ Printer.pr_leconstr_env env evd rhs ++ str") but does not appear in the pattern.")
  in

  let rhs = Vars.subst_univs_level_constr usubst rhs in

  let qvars, uvars = Vars.sort_and_universes_of_constr rhs in
  qvars |> Sorts.QVar.Set.iter (fun lvl -> lvl |> Sorts.QVar.var_index |> Option.iter (fun lvli ->
    if not (Int.Map.mem lvli invtblu) then
      CErrors.user_err ?loc:rhs_loc
        Pp.(str "Sort quality variable" ++ Termops.pr_evd_qvar evd lvl ++ str " appears in rhs but does not appear in the pattern.")
  ));
  uvars |> Univ.Level.Set.iter (fun lvl -> lvl |> Univ.Level.var_index |> Option.iter (fun lvli ->
    if not (Int.Map.mem lvli invtblu) then
      CErrors.user_err ?loc:rhs_loc
        Pp.(str "Universe level variable " ++ Termops.pr_evd_level evd lvl ++ str " appears in rhs but does not appear in the pattern.")
  ));
  let usubst = UVars.Instance.of_array
    (Array.init nvarqs (fun i -> Sorts.Quality.var (Option.default i (Int.Map.find_opt i invtblq))),
     Array.init nvarus (fun i -> Univ.Level.var (Option.cata fst i (Int.Map.find_opt i invtblu))))
  in
  let rhs = Vars.subst_instance_constr usubst rhs in

  let test_level lvl =
    match Univ.Level.var_index lvl with
    | Some n ->
      let i = Int.Map.bindings invtblu |> List.find_map (fun (i, (a, b)) -> if a = n && b then Some i else None) in
      Option.iter (fun i ->
      CErrors.user_err ?loc:rhs_loc
        Pp.(str "Algebraic universe variable" ++ Termops.pr_evd_level evd (Univ.Level.var i) ++ str " appears in rhs as a universe level variable.")
      ) i
    | _ -> ()
  in

  let test_universe u =
    match universe_level_var_index u with
    | Some _ -> ()
    | None -> Univ.Universe.repr u |> List.iter (fun (lvl, _) -> test_level lvl)
  in

  let () = Vars.iter_on_instance (fun u -> UVars.Instance.to_array u |> snd |> Array.iter test_level) test_universe rhs in

  head_symbol, { lhs_pat = head_umask, elims; rhs }

let do_rules id rules =
  let env = Global.env () in
  if not @@ Environ.rewrite_rules_allowed env then raise Environ.(RewriteRulesNotAllowed Rule);
  let body = { rewrules_rules = List.map interp_rule rules } in
  Global.add_rewrite_rules id body
