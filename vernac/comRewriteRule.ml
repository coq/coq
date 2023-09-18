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
  let udecl, l = preprocess_symbols l in
  List.iter (do_symbol ~poly ~unfold_fix udecl) l



open Util
open Constr
open Declarations

type state = (int * int Evar.Map.t) * (int * int Int.Map.t) * Evd.evar_map

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

let update_invtblu1 ~loc evd lvl (curvaru, tbl) =
  succ curvaru, tbl |> Int.Map.update lvl @@ function
    | None -> Some curvaru
    | Some k as c when k = curvaru -> c
    | Some k ->
        CErrors.user_err ?loc
          Pp.(str "Universe variable "
            ++ Termops.pr_evd_level evd (Univ.Level.var lvl)
            ++ str" already taken for hole " ++ int k
            ++ str" but used here for hole " ++ int curvaru
            ++ str".")

let update_invtblu ~loc (state, stateu, evd : state) u : state * _ =
  let u = u |> UVars.Instance.to_array |> snd in
  let stateu, mask = Array.fold_left_map (fun stateu lvl ->
      match Univ.Level.var_index lvl with
      | Some lvl -> update_invtblu1 ~loc evd lvl stateu, true
      | None -> stateu, false
    ) stateu u
  in
  let mask = if Array.exists Fun.id mask then Some mask else None in
  (state, stateu, evd), mask

let safe_sort_pattern_of_sort ~loc s =
  let open Sorts in
  match s with
  | Type u -> InType
  | SProp -> InSProp
  | Prop -> InProp
  | Set -> InSet
  | QSort _ -> CErrors.user_err ?loc Pp.(str "Unsupported qsort level in pattern.")


let rec safe_pattern_of_constr ~loc env depth state t = Constr.kind t |> function
  | App (f, args) ->
      let state, (head, elims) = safe_pattern_of_constr ~loc env depth state f in
      let state, pargs = Array.fold_left_map (safe_arg_pattern_of_constr ~loc env depth) state args in
      state, (head, elims @ [PEApp pargs])
  | Case (ci, u, _, (ret, _), _, c, brs) ->
      let state, mask = update_invtblu ~loc state u in
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
  | Const (c, u) when Environ.is_symbol env c ->
    let state, mask = update_invtblu ~loc state u in
    state, PHSymbol (c, mask)
  | Rel i ->
    assert (i <= depth);
    state, PHRel i
  | Sort s ->
    let ps = safe_sort_pattern_of_sort ~loc s in
    state, PHSort ps
  | Ind (ind, u) ->
    let state, mask = update_invtblu ~loc state u in
    state, PHInd (ind, mask)
  | Construct (c, u) ->
    let state, mask = update_invtblu ~loc state u in
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
    let (_, _, evd) = state in
    CErrors.user_err ?loc Pp.(str "Subterm not recognised as pattern: " ++ Printer.safe_pr_lconstr_env env evd t)

and safe_arg_pattern_of_constr ~loc env depth (st, stateu, evd as state) t = Constr.kind t |> function
  | Evar (evk, inst) ->
    let EvarInfo evi = Evd.find evd evk in
    (match snd (Evd.evar_source evi) with
    | Evar_kinds.MatchingVar (Evar_kinds.FirstOrderPatVar id) ->
      let st = update_invtbl ~loc env evd evk st in
      (match Evd.evar_key id evd with exception Not_found -> () | _ ->
        CErrors.user_err ?loc Pp.(str "Pattern name " ++ Id.print id ++ str" already in use.")
      );
      let evd = Evd.rename evk id evd in
      (st, stateu, evd), EHole
    | Evar_kinds.NamedHole _ -> CErrors.user_err ?loc Pp.(str "Named hole are not supported, you must use regular evars: " ++ Printer.safe_pr_lconstr_env env evd t)
    | _ ->
      if Option.is_empty @@ Evd.evar_ident evk evd then state, EHoleIgnored else
        CErrors.user_err ?loc Pp.(str "Named evar in unsupported context: " ++ Printer.safe_pr_lconstr_env env evd t)
    )
  | _ ->
    let state, p = safe_pattern_of_constr ~loc env depth state t in
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


let interp_rule (udecl, lhs, rhs) =
  let env = Global.env () in
  let poly = Option.has_some udecl in
  let evd, udecl = Constrintern.interp_univ_decl_opt env udecl in

  let lhs_loc = lhs.CAst.loc in
  let rhs_loc = rhs.CAst.loc in

  let lhs = Constrintern.(intern_gen WithoutTypeConstraint ~pattern_mode:true env evd lhs) in
  let flags = { Pretyping.no_classes_no_fail_inference_flags with expand_evars = false; solve_unification_constraints = false } in
  let evd, lhs = Pretyping.understand_tcc ~flags env evd lhs in
  (* let evd, lhs, typ = Pretyping.understand_tcc_ty ~flags env evd lhs in *)
  (* let patvars, lhs = Constrintern.intern_constr_pattern env evd lhs in *)

  let evd = Evd.minimize_universes evd in
  let _qvars, uvars = EConstr.universes_of_constr evd lhs in
  let evd = Evd.restrict_universe_context evd uvars in
  let univs = Evd.check_univ_decl ~poly evd udecl in

  let nvarus, usubst =
    match fst univs with
    | Monomorphic_entry _ -> 0, UVars.empty_sort_subst
    | Polymorphic_entry ctx ->
        snd @@ UVars.UContext.size ctx,
        let inst, auctx = UVars.abstract_universes ctx in
        UVars.make_instance_subst inst
  in

  let lhs = Vars.subst_univs_level_constr usubst (EConstr.Unsafe.to_constr lhs) in

  let ((nvars', invtbl), (nvarus', invtblu), evd), (head_pat, elims) =
    safe_pattern_of_constr ~loc:lhs_loc env 0 ((1, Evar.Map.empty), (0, Int.Map.empty), evd) lhs
  in
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

  let rec find_last_alias evd evk =
    if Evd.is_undefined evd evk then evk else
      match Evd.is_aliased_evar evd evk with
      | Some evk -> find_last_alias evd evk
      | None ->
        CErrors.user_err ?loc:lhs_loc
          Pp.(str "A variable (#" ++ Evar.print evk ++ str") got unified with a term.")
  in
  let update_invtbl evd evk n invtbl =
    let Evd.EvarInfo evi = Evd.find evd evk in
    let vars = Evd.evar_hyps evi |> Environ.named_context_of_val |> Context.Named.instance EConstr.mkVar in
    let evk = find_last_alias evd evk in
    Evar.Map.add evk (n, vars) invtbl
  in

  let rhs = Constrintern.(intern_gen WithoutTypeConstraint env evd rhs) in
  let flags = Pretyping.no_classes_no_fail_inference_flags in
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

  Vars.universes_of_constr rhs |> Univ.Level.Set.iter (fun lvl -> lvl |> Univ.Level.var_index |> Option.iter (fun lvli ->
    if not (Int.Map.mem lvli invtblu) then
      CErrors.user_err ?loc:rhs_loc
        Pp.(str "Universe level variable " ++ Termops.pr_evd_level evd lvl ++ str " appears in rhs but does not appear in the pattern.")
  ));
  let usubst = UVars.Instance.of_array ([||], Array.init nvarus (fun i -> Univ.Level.var (Option.default i (Int.Map.find_opt i invtblu)))) in
  let rhs = Vars.subst_instance_constr usubst rhs in

  head_symbol, { lhs_pat = head_umask, elims; rhs }

let do_rules id rules =
  let body = { rewrules_rules = List.map interp_rule rules } in
  Global.add_rewrite_rules id body
