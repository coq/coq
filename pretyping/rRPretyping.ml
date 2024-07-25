(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open CErrors
open Util
open Names
open Evd
module CVars = Vars
open Context
open Termops
open Environ
open EConstr
open Constr
open Inductiveops
open Evarutil
open Pretype_errors
open Glob_term
open Glob_ops
open GlobEnv
open Declarations
open Rewrite_rules_ops

let (!!) env = GlobEnv.env env

let level_name ?loc evd sigma = function
  | GSProp | GProp | GSet -> None
  | GUniv u -> Some (evd, sigma, (u, true))
  | GRawUniv u ->
    user_err ?loc Pp.(str "Unsupported quality: " ++ Termops.pr_evd_level evd u ++ str" (raw universe).")
  | GLocalUniv {v=id; loc} ->
    try Some (evd, sigma, (Evd.universe_of_name evd id, true))
    with Not_found ->
      let evd, l = new_univ_level_variable ?loc ~name:id univ_rigid evd in
      let sigma = ExtraEnv.add_universe l ~bound:true sigma in
      Some (evd, sigma, (l, true))

let glob_level ?loc evd sigma : glob_level -> _ = function
  | UAnonymous {rigid} ->
    assert (rigid <> UnivFlexible true);
    let evd, l = new_univ_level_variable ?loc univ_rigid evd in
    let sigma = ExtraEnv.add_universe l ~bound:false sigma in
    evd, sigma, (l, false)
  | UNamed s ->
    match level_name ?loc evd sigma s with
    | None ->
      user_err ?loc
        (str "Universe instances cannot contain non-Set small levels," ++ spc() ++
          str "polymorphic universe instances must be greater or equal to Set.");
    | Some r -> r

let glob_qvar ?loc evd sigma : glob_qvar -> _ = function
  | GRawQVar q ->
    user_err ?loc Pp.(str "Unsupported quality: " ++ Termops.pr_evd_qvar evd q ++ str" (raw qvar).")
  | GQVar q -> evd, sigma, (q, true)
  | GLocalQVar {v=Anonymous} ->
      let evd, q = new_quality_variable ?loc evd in
      let sigma = ExtraEnv.add_quality q ~bound:false sigma in
      evd, sigma, (q, false)
  | GLocalQVar {v=Name id; loc} ->
    try evd, sigma, (Evd.quality_of_name evd id, true)
    with Not_found ->
      let evd, q = new_quality_variable ?loc ~name:id evd in
      let sigma = ExtraEnv.add_quality q ~bound:true sigma in
      evd, sigma, (q, true)

let glob_quality ?loc evd sigma = function
  | GQConstant q -> evd, sigma, PQConstant q
  | GQualVar q ->
    let evd, sigma, q = glob_qvar ?loc evd sigma q in
    evd, sigma, PQVar q

let sort_info ?loc evd sigma q l =
  let l = match l with
  | [] -> assert false
  | _ :: _ :: _ ->
    user_err ?loc
      (str "Unsupported algebraic expressions.")
  | [l, 0] -> l
  | [_, n] ->
      user_err ?loc
        (str "Cannot interpret universe increment +" ++ int n ++ str ".")
  in
  match l with
  | GSProp -> assert (Option.is_empty q); evd, sigma, Sorts.PSSProp, Sorts.sprop
  | GProp -> assert (Option.is_empty q); evd, sigma, Sorts.PSProp, Sorts.prop
  | GSet ->
    begin match q with
    | None -> evd, sigma, Sorts.PSSet, Sorts.set
    | Some q ->
      let evd, sigma, q = glob_qvar ?loc evd sigma q in
      user_err ?loc
        (str "Unsupported level Set in sort with quality variable" ++ Termops.pr_evd_qvar evd (fst q) ++ str".")
    end
  | u ->
    let (evd, sigma, u) = match level_name evd sigma u with
    | Some (evd, sigma, u) -> (evd, sigma, u)
    | None ->
      user_err ?loc
        (str "Non-Set small universes cannot be used in algebraic expressions.")
    in
    match q with
      | None -> evd, sigma, Sorts.PSType u, Sorts.sort_of_univ (Univ.Universe.make (fst u))
      | Some q ->
        let evd, sigma, q = glob_qvar ?loc evd sigma q in
        evd, sigma, Sorts.PSQSort (q, u), Sorts.qsort (fst q) (Univ.Universe.make (fst u))


let quality_of_quality_mask =
  let open Sorts.Quality in
  function
  | PQConstant q -> QConstant q
  | PQVar (q, _) -> QVar q

let instance_of_mask (qs, us : _ instance_mask) =
  let qs = Array.map quality_of_quality_mask qs in
  let us = Array.map (fun (l, _) -> l) us in
  UVars.Instance.of_array (qs, us)

let mask_of_fresh_instance sigma u : _ * _ instance_mask =
  let qs, us = UVars.Instance.to_array u in
  let sigma, qs = Array.fold_left_map (fun sigma -> function Sorts.Quality.QVar q -> ExtraEnv.add_quality q ~bound:false sigma, PQVar (q, false) | _ -> assert false) sigma qs in
  let sigma, us = Array.fold_left_map (fun sigma l -> ExtraEnv.add_universe l ~bound:false sigma, (l, false)) sigma us in
  sigma, (qs, us)

let pretype_instance_mask ?loc evd sigma (ql,ul) : evar_map * _ * _ instance_mask * UVars.Instance.t =
  let (evd, sigma), ql' = List.fold_left_map (fun (evd, sigma) q -> let evd, sigma, q = glob_quality ?loc evd sigma q in (evd, sigma), q) (evd, sigma) ql in
  let (evd, sigma), ul' = List.fold_left_map (fun (evd, sigma) u -> let evd, sigma, u = glob_level ?loc evd sigma u in (evd, sigma), u) (evd, sigma) ul in
  let mask = Array.of_list ql', Array.of_list ul' in
  evd, sigma, mask, instance_of_mask mask

let pretype_instance env evd sigma ?loc ref u =
  let auctx = Environ.universes_of_global !!env ref in
  match u with
  | None ->
    let u, (_, cstrs as ctx) = UnivGen.fresh_instance auctx in
    let evd = Evd.merge_sort_context_set ?loc univ_rigid evd ctx in
    let sigma, mask = mask_of_fresh_instance sigma u in
    let sigma = ExtraEnv.enforce_constraints sigma cstrs in
    evd, sigma, mask, u
  | Some l ->
    let evd, sigma, mask, u = pretype_instance_mask ?loc evd sigma l in
    let () =
      let open UVars in
      let actual = Instance.length u
      and expect = AbstractContext.size auctx
      in
      if not (UVars.eq_sizes actual expect) then
        Loc.raise ?loc (UnivGen.UniverseLengthMismatch { gref = ref; actual; expect })
    in
    let cstrs = UVars.AbstractContext.instantiate u auctx in
    let evd = Evd.add_constraints evd cstrs in
    let sigma = ExtraEnv.enforce_constraints sigma cstrs in
    evd, sigma, mask, u


let sort ?loc evd sigma : glob_sort -> _ = function
  | None, UAnonymous _ ->
    let evd, l = new_univ_level_variable ?loc univ_rigid evd in
    let sigma = ExtraEnv.add_universe l ~bound:false sigma in
    evd, sigma, PSType (l, false), Sorts.sort_of_univ (Univ.Universe.make l)
  | Some q, UAnonymous _ ->
    let evd, l = new_univ_level_variable ?loc univ_rigid evd in
    let sigma = ExtraEnv.add_universe l ~bound:false sigma in
    let evd, sigma, q = glob_qvar ?loc evd sigma q in
    evd, sigma, PSQSort (q, (l, false)), Sorts.sort_of_univ (Univ.Universe.make l)
  | q, UNamed l ->
    sort_info ?loc evd sigma q l

let new_type_evar env evd sigma ?loc () =
  let naming = Namegen.IntroAnonymous in
  let knd = Evar_kinds.InternalHole in
  let evd, q = new_quality_variable ?loc evd in
  let evd, u = new_univ_level_variable ?loc (UnivFlexible true) evd in
  let sigma = ExtraEnv.add_quality q ~bound:false sigma in
  let sigma = ExtraEnv.add_universe u ~bound:false sigma in
  let s = mkSort (Sorts.qsort q (Univ.Universe.make u)) in
  let evd, c = GlobEnv.new_evar env evd ~src:(loc, knd) ~naming (EConstr.of_constr s) in
  let evk, _ = EConstr.destEvar evd c in
  let sigma = ExtraEnv.add_evar evk (Environ.rel_context !!env) s Relevant Anonymous sigma in
  evd, sigma, q, u, evk

let new_universe env evd sigma ?loc () =
  let evd, u = new_univ_level_variable ?loc (UnivFlexible true) evd in
  let sigma = ExtraEnv.add_universe u ~bound:false sigma in
  evd, sigma, u

let new_sort env evd sigma ?loc () =
  let evd, q = new_quality_variable ?loc evd in
  let evd, u = new_univ_level_variable ?loc (UnivFlexible true) evd in
  let sigma = ExtraEnv.add_quality q ~bound:false sigma in
  let sigma = ExtraEnv.add_universe u ~bound:false sigma in
  evd, sigma, q, u

let new_typed_evar env evd sigma ?loc ido (ty, rel) =
  let naming =
    match ido with
    | Name id -> Namegen.IntroIdentifier id
    | Anonymous -> Namegen.IntroAnonymous
  in
  let knd = Evar_kinds.RewriteRulePattern ido in
  let evd, c = GlobEnv.new_evar env evd ~src:(loc, knd) ~naming (EConstr.of_constr ty) in
  let evk, _ = EConstr.destEvar evd c in
  let sigma = ExtraEnv.add_evar evk (Environ.rel_context !!env) ty rel ido sigma in
  let inst = SList.of_full_list (List.init (Environ.nb_rel !!env) (fun i -> mkRel (i+1))) in
  evd, sigma, evk, inst, ty


let new_ind_annots env evd sigma ?loc ar_ctx (qs, us) =
  let evd, qannots = CArray.init_fold qs (fun _ evd -> new_quality_variable ?loc evd) evd in
  let evd, uannots = CArray.init_fold us (fun _ evd -> new_univ_level_variable ?loc (UnivFlexible false) evd) evd in
  let sigma = CArray.fold_left (fun sigma q -> ExtraEnv.add_quality q ~bound:false sigma) sigma qannots in
  let sigma = CArray.fold_left (fun sigma u -> ExtraEnv.add_universe u ~bound:false sigma) sigma uannots in

  let ctx = Environ.rel_context !!env in
  let instlen = Environ.nb_rel !!env in

  let rec apply_rec evd sigma ar_telescope subst args_annot =
    match ar_telescope with
    | Context.Rel.Declaration.LocalDef (_, b, _) :: l ->
      let b = CVars.substl subst b in
      apply_rec evd sigma l (b :: subst) args_annot
    | Context.Rel.Declaration.LocalAssum (na, ty) :: l ->
      let ty = CVars.substl subst ty in
      let evd, c = GlobEnv.new_evar env evd ~src:(loc, InternalHole) (EConstr.of_constr ty) in
      let evk, _ = EConstr.destEvar evd c in
      let sigma = ExtraEnv.add_evar evk ctx ty na.Context.binder_relevance Anonymous sigma in
      let ev = mkEvar (evk, SList.of_full_list (List.init instlen (fun i -> mkRel (i+1)))) in
      apply_rec evd sigma l (ev :: subst) (evk :: args_annot)
    | [] -> evd, sigma, Array.rev_of_list args_annot
  in
  let evd, sigma, args_annot = apply_rec evd sigma (List.rev ar_ctx) [] [] in
  evd, sigma, (qannots, uannots, args_annot)


let pretype_case pretype_argpattern env evd sigma ?loc ind ind_annots pc jc (na, po) io brs =

  let sigma, (u, args) = reduce_to_appind !!env sigma ind ind_annots (j_type jc) in
  let (mib, mip) = Inductive.lookup_mind_specif !!env ind in

  let (params, realargs) = Array.chop mib.mind_nparams args in
  let paramdecl = CVars.subst_instance_context u mib.mind_params_ctxt in
  let paramsubst = CVars.subst_of_rel_context_instance paramdecl params in

  let instantiate_context u subst nas (ctx : rel_context) : rel_context =
    let open Context.Rel.Declaration in
    let open Context in
    let open CVars in
    let instantiate_relevance i na =
      let na = { na with binder_relevance = UVars.subst_instance_relevance u na.binder_relevance } in
      Option.cata (fun nas -> { na with binder_name = nas.(i)}) na nas
    in
    let rec instantiate i ctx = match ctx with
    | [] -> assert (Int.equal i (-1)); []
    | LocalAssum (na, ty) :: ctx ->
      let ctx = instantiate (pred i) ctx in
      let ty = substnl subst i (subst_instance_constr u ty) in
      let na = instantiate_relevance i na in
      LocalAssum (na, ty) :: ctx
    | LocalDef (na, ty, bdy) :: ctx ->
      let ctx = instantiate (pred i) ctx in
      let ty = substnl subst i (subst_instance_constr u ty) in
      let bdy = substnl subst i (subst_instance_constr u bdy) in
      let na = instantiate_relevance i na in
      LocalDef (na, ty, bdy) :: ctx
    in
    instantiate (List.length ctx - 1) ctx
  in

  let pctx =
    let nas = Option.map (fun i -> Array.of_list (snd i.CAst.v @ [na])) io in
    let realdecls, _ = List.chop mip.mind_nrealdecls mip.mind_arity_ctxt in
    let self =
      let args = Context.Rel.instance mkRel 0 mip.mind_arity_ctxt in
      let inst = UVars.Instance.(abstract_instance (length u)) in
      mkApp (mkIndU (ind, inst), args)
    in
    let realdecls = Context.Rel.Declaration.LocalAssum (Context.make_annot na mip.mind_relevance, self) :: realdecls in
    instantiate_context u paramsubst nas realdecls
  in

  let evd, sigma, qr, ur = new_sort env evd sigma ?loc () in
  let sr = Sorts.qsort qr (Univ.Universe.make ur) in

  let (evd, sigma, pp, p) =
    let hypnaming = RenameExistingBut (VarSet.variables (Global.env ())) in
    let pctx, p_env = GlobEnv.push_rel_context ~hypnaming evd (EConstr.of_rel_context pctx) env in
    let ret = Option.default (DAst.make ?loc (GHole GInternalHole)) po in
    let evd, sigma, pp, j_p = pretype_argpattern (mkSort sr, Sorts.Relevant) p_env evd sigma ret in
    let pp = (Array.map_of_list Context.Rel.Declaration.get_name pctx, pp) in
    let p = Array.map_of_list (Context.Rel.Declaration.get_annot %> Context.map_annot_relevance_het (ERelevance.kind evd)) pctx, j_val j_p in
    (evd, sigma, pp, p)
  in
  let rp = Sorts.RelevanceVar qr in

  let build_one_branch i (evd, sigma) (loc, brnas, br) =
    let brnas = Option.map Array.of_list brnas in
    let (ctx, cty) = mip.mind_nf_lc.(i) in

    if Option.cata (fun a -> Array.length a <> mip.mind_consnrealdecls.(i)) false brnas then
      anomaly ?loc Pp.(str"Invalid pattern (wrong number of arguments).")
    else

    let bctx, _ = List.chop mip.mind_consnrealdecls.(i) ctx in
    let bctx = instantiate_context u paramsubst brnas bctx in
    let hypnaming = RenameExistingBut (VarSet.variables (Global.env ())) in
    let bctx, br_env = GlobEnv.push_rel_context ~hypnaming evd (EConstr.of_rel_context bctx) env in
    let cty = CVars.substnl paramsubst mip.mind_consnrealdecls.(i) (CVars.subst_instance_constr u cty) in

    let (_, retargs) = Inductive.find_rectype !!br_env cty in

    let params = Array.map (fun c -> lift mip.mind_consnrealdecls.(i) c) params in
    let cargs = Context.Rel.instance mkRel 0 bctx in
    let cstr = mkApp (mkConstructU ((ind, i + 1), u), Array.append params cargs) in
    let indices = List.lastn mip.mind_nrealargs retargs in
    let subst = instantiate (List.rev pctx) (indices @ [cstr]) (Esubst.subs_shft (mip.mind_consnrealdecls.(i), Esubst.subs_id 0)) in

    let brty = CVars.esubst CVars.lift_substituend subst (snd p) in

    let evd, sigma, pbr, j_br = pretype_argpattern (brty, rp) br_env evd sigma br in
    let pbr = Array.map_of_list Context.Rel.Declaration.get_name bctx, pbr in
    let br = Array.map_of_list (Context.Rel.Declaration.get_annot %> Context.map_annot_relevance_het (ERelevance.kind evd)) bctx, j_val j_br in
    (evd, sigma), (pbr, br)
  in
  let (evd, sigma), brs = Array.fold_left_map_i build_one_branch (evd, sigma) brs in
  let pbrs, brs = Array.split brs in

  let ci = make_case_info !!env ind RegularStyle in
  let body = mkCase (ci, u, params, (p, rp), NoInvert, j_val jc, brs) in

  let ty =
    let subst = CVars.subst_of_rel_context_instance_list pctx (CArray.to_list realargs @ [j_val jc]) in
    CVars.substl subst (snd p)
  in

  evd, sigma, PCase (pc, ind, ind_annots, (pp, (qr, ur)), pbrs), make_judge body ty


let rec eval_pretyper_pattern env evd sigma t : _ * _ * _ * _ =
  let loc = t.CAst.loc in
  match DAst.get t with
  | GRef (ref,u) ->
    pretype_ref (ref, u) ?loc env evd sigma
  | GVar id ->
    pretype_var id ?loc env evd sigma
  | GEvar (evk, args) ->
    user_err ?loc Pp.(str"Invalid pattern: " ++ Id.print evk.CAst.v ++ str" (unknown evar type).")
  | GPatVar _ ->
    assert false
  | GApp (c, args) ->
    pretype_app (c, args) ?loc env evd sigma
  | GProj (hd, args, c) ->
    pretype_proj (hd, args, c) ?loc env evd sigma
  | GLambda (na, _, bk, t, c) ->
    pretype_lambda (na, bk, t, c) ?loc env evd sigma
  | GProd (na, _, bk, t, c) ->
    pretype_prod (na, bk, t, c) ?loc env evd sigma
  | GLetIn (na, _, b, t, c) ->
    pretype_letin (na, b, t, c) ?loc env evd sigma
  | GCases (st, c, tm, cl) ->
    pretype_cases (st, c, tm, cl) ?loc env evd sigma
  | GLetTuple (na, b, t, c) ->
    pretype_lettuple (na, b, t, c) ?loc env evd sigma
  | GIf (c, r, t1, t2) ->
    pretype_if (c, r, t1, t2) ?loc env evd sigma
  | GRec (knd, nas, decl, c, t) ->
    pretype_rec (knd, nas, decl, c, t) ?loc env evd sigma
  | GSort s ->
    pretype_sort s ?loc env evd sigma
  | GHole _ ->
    user_err ?loc Pp.(str"Invalid pattern: _ (unknown evar type).")
  | GGenarg arg ->
    pretype_genarg arg ?loc env evd sigma
  | GCast (c, k, t) ->
    pretype_cast (c, k, t) ?loc env evd sigma
  | GInt n ->
    pretype_int n ?loc env evd sigma
  | GFloat f ->
    pretype_float f ?loc env evd sigma
  | GString s ->
    pretype_string s ?loc env evd sigma
  | GArray (u,t,def,ty) ->
    pretype_array (u,t,def,ty) ?loc env evd sigma

and eval_pretyper_arg_pattern tycon env evd sigma t =
  let loc = t.CAst.loc in
  match DAst.get t with
  | GEvar (evk, args) ->
    pretype_evar (evk, args) ?loc tycon env evd sigma
  | GHole _ ->
    pretype_hole ?loc tycon env evd sigma
  | _ ->
    let evd, sigma, pat, j = eval_pretyper_pattern env evd sigma t in
    let sigma = Rewrite_rules_ops.cumul_lax !!env sigma j.uj_type (fst tycon) in
    let sigma = ExtraEnv.add_pattern_relevance (Relevanceops.relevance_of_term !!env (j_val j)) sigma in
    evd, sigma, Pat pat, j


and pretype_ref (ref, u) =
  fun ?loc env evd sigma ->
  let evd, sigma, mask, u = pretype_instance env evd sigma ?loc ref u in
  let sigma, p, j =
    match ref with
    | IndRef ind ->
        let sigma, j = judge_of_inductive !!env sigma (ind, u) in
        sigma, PInd (ind, mask), j
    | ConstructRef c ->
        let sigma, j = judge_of_constructor !!env sigma (c, u) in
        sigma, PConstr (c, mask), j
    | ConstRef c ->
        if not @@ Environ.is_symbol !!env c then user_err ?loc Pp.(str"Invalid pattern: " ++ GlobRef.print ref ++ str".");
        let sigma, j = judge_of_constant !!env sigma (c, u) in
        sigma, PSymbol (c, mask), j
    | VarRef _ -> user_err ?loc Pp.(str"Invalid pattern: " ++ GlobRef.print ref ++ str".")
  in
  evd, sigma, p, j

and pretype_var id =
  fun ?loc env evd sigma ->
  match lookup_rel_id id (Environ.rel_context !!env) with
  | (n, _, typ) ->
    evd, sigma, PRel n, make_judge (mkRel n) (Constr.lift n typ)
  | exception Not_found ->
    (* [id] not found, standard error message *)
    error_var_not_found ?loc !!env evd id

and pretype_evar (CAst.{v=id;loc=locid}, inst) ?loc tycon env evd sigma =
  let id = interp_ltac_id env id in
  match Evd.evar_key id evd with
  | exception Not_found ->
    if not @@ List.is_empty inst then
      user_err ?loc Pp.(str"Invalid pattern: " ++ Id.print id ++ str" (nonempty instance).");
    let evd, sigma, evk, inst, ty = new_typed_evar env evd sigma ?loc (Name id) tycon in
    let j = make_judge (mkEvar (evk, inst)) ty in
    evd, sigma, PVar (evk, Name id), j

  | evk -> user_err ?loc Pp.(str"Invalid pattern: " ++ Id.print id ++ str" (nonlinearity).")
  (* let EvarInfo evi = Evd.find evd evk in
  let hyps = evar_filtered_context evi in
  let evd, args = pretype_instance default_pretyper ~flags env evd loc hyps evk inst in
  let args = SList.map EConstr.to_constr args (but evars in sigma are still allowed) in
  let c = mkLEvar evd (evk, args) in
  let j = Retyping.get_judgment_of !!env evd c in
  evd, sigma, PTermEq (evk, Some id), j *)

and pretype_hole ?loc tycon env evd sigma =
  let evd, sigma, evk, inst, ty = new_typed_evar env evd sigma ?loc Anonymous tycon in
  evd, sigma, PVar (evk, Anonymous), (make_judge (mkEvar (evk, inst)) ty)

and pretype_genarg arg ?loc tycon env sigma =
  user_err ?loc Pp.(str"Invalid pattern (genarg patterns not supported).")

and pretype_rec (fixkind, names, bl, lar, vdef) =
  fun ?loc env sigma ->
  user_err ?loc Pp.(str"Invalid pattern (fixpoint/cofixpoint patterns not supported).")

and pretype_sort s =
  fun ?loc env evd sigma ->
  let evd, sigma, ps, s = sort ?loc evd sigma s in
  let evd, sigma, u = new_universe env ?loc evd sigma () in
  let sigma = ExtraEnv.enforce_super_level s u sigma in
  let j = make_judge (mkSort s) (mkSort @@ Sorts.sort_of_univ (Univ.Universe.make u)) in
  evd, sigma, PSort (ps, u), j

and pretype_app (f, args) =
  fun ?loc env evd sigma ->
  (* Test for primitive projections *)
  match DAst.get f with
  | GRef (ConstRef p, u) when Structures.PrimitiveProjections.mem p ->
    let c, args = List.sep_last args in
    pretype_proj ((p, u), args, c) ?loc env evd sigma
  | _ ->
  let evd, sigma, pf, fj = eval_pretyper_pattern env evd sigma f in

  let one_app env evd sigma pf fj arg =
    let evd, sigma, qty, uty, evkty = new_type_evar env evd sigma ?loc () in
    let open Context.Rel.Declaration in
    let binder = Context.make_annot Anonymous (ERelevance.make @@ Sorts.RelevanceVar qty) in
    let decl = LocalAssum (binder, EConstr.mkEvar (evkty, SList.of_full_list (List.init (Environ.nb_rel !!env) (fun i -> EConstr.mkRel (i+1))))) in
    let hypnaming = RenameExistingBut (VarSet.variables (Global.env ())) in
    let evd, sigma, qret, uret, evkret = new_type_evar (snd @@ push_rel ~hypnaming evd decl env) evd sigma ?loc () in

    let sigma, (argty, argrel, retty) = reduce_to_prod !!env sigma ((evkty, qty, uty), (evkret, qret, uret)) (j_type fj) in

    let evd, sigma, parg, jarg = eval_pretyper_arg_pattern (argty, argrel) env evd sigma arg in

    let retty = CVars.subst1 (j_val jarg) retty in
    let head = mkApp (j_val fj, [|j_val jarg|]) in
    evd, sigma, PApp (pf, parg, (evkty, qty, uty), (evkret, qret, uret)), make_judge head retty
  in

  List.fold_left (fun (evd, sigma, pf, fj) arg -> one_app env evd sigma pf fj arg) (evd, sigma, pf, fj) args


and pretype_proj ((f,us), args, c) =
  fun ?loc env evd sigma ->
  let evd, sigma, _, u = pretype_instance env evd sigma ?loc (ConstRef f) us in
  match Structures.PrimitiveProjections.find_opt_with_relevance (f, EInstance.make u) with
  | None ->
      pretype_app (DAst.make ?loc (GRef (GlobRef.ConstRef f,us)), args @ [c])
        ?loc env evd sigma
  | Some (p, rel) ->

    let evd, sigma, pc, jc = eval_pretyper_pattern env evd sigma c in

    let ind = Projection.Repr.inductive p in
    let (mib, mip) = Inductive.lookup_mind_specif !!env ind in
    let evd, sigma, annots = new_ind_annots env evd sigma ?loc mip.mind_arity_ctxt (UVars.Instance.length u) in

    let sigma, (u, args) = reduce_to_appind !!env sigma ind annots (j_type jc) in

    let p' = Projection.make p false in

    let pr, pty = lookup_projection p' !!env in
    let pr = UVars.subst_instance_relevance u pr in
    let ty = CVars.subst_instance_constr u pty in
    let bod = mkProj (p', pr, j_val jc) in
    evd, sigma, PProj (pc, p, annots), make_judge bod (CVars.substl (j_val jc :: CArray.rev_to_list args) ty)


and pretype_lambda (name, bk, c1, c2) =
  fun ?loc env evd sigma ->

  let evd, sigma, q, u = new_sort env evd sigma ?loc () in
  let s = Sorts.qsort q (Univ.Universe.make u) in
  let evd, sigma, pty, jty = eval_pretyper_arg_pattern (mkSort s, Sorts.Relevant) env evd sigma c1 in

  let open Context.Rel.Declaration in
  let binder = {binder_name = name; binder_relevance = ERelevance.make @@ Sorts.RelevanceVar q} in
  let var = LocalAssum (binder, EConstr.of_constr jty.uj_val) in
  let vars = VarSet.variables (Global.env ()) in
  let hypnaming = RenameExistingBut vars in
  let var',env' = push_rel ~hypnaming evd var env in
  let binder = {binder_name = get_name var'; binder_relevance = Sorts.RelevanceVar q} in

  let evd, sigma, pb, jb = eval_pretyper_pattern env' evd sigma c2 in
  let resj = make_judge (mkLambda (binder, jty.uj_val, jb.uj_val)) (mkProd (binder, jty.uj_val, jb.uj_type)) in
  evd, sigma, PLambda (binder.binder_name, pty, (q, u), pb), resj

and pretype_prod (name, bk, c1, c2) =
  fun ?loc env evd sigma ->

  let evd, sigma, qdom, udom = new_sort env evd sigma ?loc () in
  let sdom = Sorts.qsort qdom (Univ.Universe.make udom) in
  let evd, sigma, pdom, jdom = eval_pretyper_arg_pattern (mkSort sdom, Sorts.Relevant) env evd sigma c1 in

  let open Context.Rel.Declaration in
  let binder = {binder_name = name; binder_relevance = ERelevance.make @@ Sorts.RelevanceVar qdom} in
  let var = LocalAssum (binder, EConstr.of_constr jdom.uj_val) in
  let vars = VarSet.variables (Global.env ()) in
  let hypnaming = RenameExistingBut vars in
  let var',env' = push_rel ~hypnaming evd var env in
  let binder = {binder_name = get_name var'; binder_relevance = Sorts.RelevanceVar qdom} in

  let evd, sigma, qcod, ucod = new_sort env evd sigma ?loc () in
  let scod = Sorts.qsort qcod (Univ.Universe.make ucod) in

  let evd, sigma, pcod, jcod = eval_pretyper_arg_pattern (mkSort scod, Sorts.Relevant) env' evd sigma c2 in

  let evd, sigma, retu = new_universe env ?loc evd sigma () in
  let sigma = ExtraEnv.enforce_product_level !!env sdom scod retu sigma in
  let resj = make_judge (mkProd (binder, jdom.uj_val, jcod.uj_val)) (mkSort @@ Sorts.make (Sorts.quality scod) (Univ.Universe.make retu)) in
  evd, sigma, PProd (binder.binder_name, pdom, (qdom, udom), pcod, (qcod, ucod), retu), resj

and pretype_letin (name, c1, t, c2) =
  fun ?loc env sigma ->
  user_err ?loc Pp.(str"Invalid pattern (let-definitions are not patterns).")

and pretype_lettuple (nal, (na, po), c, d) =
  fun ?loc env evd sigma ->
  let evd, sigma, pc, jc = eval_pretyper_pattern env evd sigma c in
  let sigma = ExtraEnv.add_pattern_relevance (Relevanceops.relevance_of_term !!env (j_val jc)) sigma in

  let ind =
    match Inductive.find_rectype !!env (j_type jc) with
    | (ind, _), _ -> ind
    | exception Not_found -> user_err ?loc Pp.(str "Cannot guess inductive.")
  in
  let (mib, mip) = Inductive.lookup_mind_specif !!env ind in
  let ar_ctx = mip.mind_arity_ctxt in
  let uisize = match mib.mind_universes with Monomorphic -> (0, 0) | Polymorphic uctx -> UVars.AbstractContext.size uctx in
  let evd, sigma, ind_annots = new_ind_annots env evd sigma ?loc ar_ctx uisize in

  let brs =
    if Array.length mip.mind_consnrealdecls <> 1 then
      user_err ?loc Pp.(str "Wrong number of constructors for an let destruction pattern");
    [| None, Some nal, d |]
  in

  pretype_case eval_pretyper_arg_pattern env evd sigma ?loc ind ind_annots pc jc (na, po) None brs

and pretype_cases (sty, po, tml, eqns) =
  fun ?loc env evd sigma ->

  let c, na, io = match tml with
  | [] -> assert false
  | _ :: _ :: _ -> user_err ?loc Pp.(str"Invalid pattern (match constructions with more than one scrutinee not supported).")
  | [c, (na, io)] -> c, na, io
  in

  let evd, sigma, pc, jc = eval_pretyper_pattern env evd sigma c in
  let sigma = ExtraEnv.add_pattern_relevance (Relevanceops.relevance_of_term !!env (j_val jc)) sigma in

  let module RelDecl = Context.Rel.Declaration in
  let evd, sigma, ind, ind_annots, nb_brs =
    match io with
    | Some ({ CAst.v=(ind, nas); loc}) ->
      let (mib, mip) = Inductive.lookup_mind_specif !!env ind in
      if List.length nas <> mip.mind_nrealdecls then
        user_err ?loc Pp.(str "Ill-formed 'in' clause in cases.");
      let ar_ctx = List.map2 RelDecl.set_name (List.map RelDecl.get_name mib.mind_params_ctxt @ nas) mip.mind_arity_ctxt in
      let uisize = match mib.mind_universes with Monomorphic -> (0, 0) | Polymorphic uctx -> UVars.AbstractContext.size uctx in
      let evd, sigma, annots = new_ind_annots env evd sigma ?loc ar_ctx uisize in
      evd, sigma, ind, annots, Array.length mip.mind_nf_lc
    | None ->
      let ind = match List.find_map (function { CAst.v=(_, [pat], _); _ } -> (match DAst.get pat with PatCstr (cstr, _, _) -> Some (fst cstr) | _ -> None) | _ -> None) eqns with
      | Some ind -> ind
      | None -> match Inductive.find_rectype !!env (j_type jc) with
        | (ind, _), _ -> ind
        | exception Not_found -> user_err ?loc Pp.(str "Cannot guess inductive.")
      in
      let (mib, mip) = Inductive.lookup_mind_specif !!env ind in
      let ar_ctx = mip.mind_arity_ctxt in
      let uisize = match mib.mind_universes with Monomorphic -> (0, 0) | Polymorphic uctx -> UVars.AbstractContext.size uctx in
      let evd, sigma, annots = new_ind_annots env evd sigma ?loc ar_ctx uisize in
      evd, sigma, ind, annots, Array.length mip.mind_nf_lc
  in

  let brs = NoDupArray.make nb_brs in

  let brs = List.fold_left (fun brs eqn ->
    match eqn with
    | { CAst.v = (ids, [pat], rhs); loc } ->
      begin match DAst.get pat with
      | PatVar na ->
        if not @@ Name.equal na Anonymous then user_err ?loc Pp.(str"Invalid pattern (alias not supported).")
        else NoDupArray.fill_remaining (loc, None, rhs) brs
      | PatCstr (cstr, pats, na) ->
        let (ind', i) = cstr in
        let i = i-1 in
        if not @@ Ind.CanOrd.equal ind ind' then user_err ?loc Pp.(str"Invalid pattern (wrong constructor).")
        else
        if not @@ Name.equal na Anonymous then user_err ?loc Pp.(str"Invalid pattern (alias not supported).")
        else
        if NoDupArray.is_filled i brs then user_err ?loc Pp.(str"Redundant branch.")
        else
        let inner_vars = List.map (fun pat ->
            match DAst.get pat with
            | PatVar na -> na
            | PatCstr _ -> user_err ?loc Pp.(str"Invalid pattern (deep pattern-matching not supported).")) pats
        in
        NoDupArray.add i (loc, Some inner_vars, rhs) brs
      end
    | { CAst.loc; _ } -> user_err ?loc Pp.(str"Invalid pattern (match constructions with more than one scrutinee not supported)."))
    brs eqns
  in

  let brs =
    match NoDupArray.to_array_opt brs with
    | Some brs -> brs
    | None -> user_err ?loc Pp.(str"Invalid pattern (missing a branch).")
  in

  pretype_case eval_pretyper_arg_pattern env evd sigma ?loc ind ind_annots pc jc (na, po) io brs

and pretype_if (c, (na, po), b1, b2) =
  fun ?loc env evd sigma ->

  let evd, sigma, pc, jc = eval_pretyper_pattern env evd sigma c in
  let sigma = ExtraEnv.add_pattern_relevance (Relevanceops.relevance_of_term !!env (j_val jc)) sigma in

  let ind =
    match Inductive.find_rectype !!env (j_type jc) with
    | (ind, _), _ -> ind
    | exception Not_found -> user_err ?loc Pp.(str "Cannot guess inductive.")
  in
  let (mib, mip) = Inductive.lookup_mind_specif !!env ind in
  let ar_ctx = mip.mind_arity_ctxt in
  let uisize = match mib.mind_universes with Monomorphic -> (0, 0) | Polymorphic uctx -> UVars.AbstractContext.size uctx in
  let evd, sigma, ind_annots = new_ind_annots env evd sigma ?loc ar_ctx uisize in

  let brs =
    let () = match mip.mind_consnrealdecls with
    | [| 0; 0 |] -> ()
    | [| _; _ |] -> user_err ?loc Pp.(str "Cannot support constructors with arguments in if pattern")
    | _ -> user_err ?loc Pp.(str "Wrong number of constructors for an if pattern")
    in
    [| None, None, b1; None, None, b2 |]
  in

  pretype_case eval_pretyper_arg_pattern env evd sigma ?loc ind ind_annots pc jc (na, po) None brs

and pretype_cast (c, k, t) =
  fun ?loc env sigma ->
    user_err ?loc Pp.(str"Invalid pattern (casts cannot be enforced).")

and pretype_int i =
  fun ?loc env evd sigma ->
  let resj = make_judge (mkInt i) (Typeops.type_of_int !!env) in
  evd, sigma, PInt i, resj

and pretype_float f =
  fun ?loc env evd sigma ->
  let resj = make_judge (mkFloat f) (Typeops.type_of_float !!env) in
  evd, sigma, PFloat f, resj

and pretype_string s =
  fun ?loc env evd sigma ->
  let resj = make_judge (mkString s) (Typeops.type_of_string !!env) in
  evd, sigma, PString s, resj

and pretype_array (u,t,def,ty) =
  fun ?loc env sigma ->
  user_err ?loc Pp.(str"Invalid pattern (array patterns not supported).")



let push_constraints env evd sigma =
  let push_evar_definitions evd sigma defs =
    Evar.Map.fold (fun evk eqs (evd, sigma, defs, flag) ->
      let (ctx, _, _, na) = Evar.Map.find evk sigma.evar_map in
      if Name.is_name na then evd, sigma, defs, flag else
      match List.find_opt (fun (pb, c) -> pb = EQ && noccur_evar (Environ.push_rel_context ctx env) sigma defs evk c) eqs with
      | Some (_, def) ->
        let sigma, defs = add_evar_definition env sigma defs evk (EQUAL, def) in
        evd, sigma, defs, true
      | None ->
        let filter (pb, c) =
          if pb = EQ then None else
          if not @@ noccur_evar (Environ.push_rel_context ctx env) sigma defs evk c then None else
          let evdref = ref evd in
          let univ_gen sigma () =
            let evd, sigma, u = new_universe env !evdref sigma () in
            evdref := evd;
            sigma, u
          in
          let (let*) = Option.bind in
          let* (sigma, def) = imitate env sigma defs univ_gen pb c in
          Some (!evdref, sigma, def)
        in
        match List.find_map filter eqs with
        | Some (evd, sigma, def) ->
            let sigma, defs = add_evar_definition env sigma defs evk def in
            evd, sigma, defs, true
        | None -> evd, sigma, defs, flag

      ) sigma.evar_candidates (evd, sigma, defs, false)
  in
  let push_equalities sigma defs =
    let sigma, equalities = { sigma with equalities = [] }, sigma.equalities in
    List.fold_left (fun (evd, flag) eq ->
      let sigma, b = push_equality env evd defs eq in
      sigma, flag || b
      ) (sigma, false) equalities
  in
  let push_qconstraints sigma =
    let qgraph, qcstrs = QGraph.merge_qconstraints sigma.qcstrs sigma.qgraph in
    { sigma with qgraph; qcstrs }, Sorts.QConstraints.(cardinal qcstrs <> cardinal sigma.qcstrs)
  in

  let rec round evd sigma defs =
    let evd, sigma, defs, b1 = push_evar_definitions evd sigma defs in

    let sigma, b2 = push_qconstraints sigma in

    let sigma, b3 = push_equalities sigma defs in

    if b1 || b2 || b3 then
      round evd sigma defs
    else
      evd, sigma, defs
  in
  let evd, sigma, defs = round evd sigma Evar.Map.empty in
  let ustate = List.fold_left (fun ucstrs cstr -> push_uconstraint sigma.qgraph cstr ucstrs) sigma.ulcstrs sigma.ucstrs in
  evd, sigma, defs, ustate

let merge_into_evd evd defs qcstrs ucstrs =
  let evd = Evd.add_quconstraints evd (qcstrs, ucstrs) in

  let evd = Evar.Map.fold (fun evk (_, def) evd ->
    let evi = Evd.find_undefined evd evk in
    let ctx = Evd.evar_filtered_context evi in
    let invsubst = List.rev_map (fun decl -> mkVar (Context.Named.Declaration.get_id decl)) ctx in

    let def = EConstr.of_constr @@ CVars.substl invsubst def in
    let evd = Evd.define evk def evd in
    evd
    ) defs evd
  in
  evd


let eval_pretyper_pattern env evd c =
  let open Rewrite_rules_ops in
  let vars = VarSet.variables (Global.env ()) in
  let hypnaming = RenameExistingBut vars in
  let env = GlobEnv.make ~hypnaming env evd empty_lvar in
  let sigma = ExtraEnv.empty in
  let evd, sigma, p, j = eval_pretyper_pattern env evd sigma c in

  let evd, sigma, defs, ucstrs = push_constraints !!env evd sigma in
  let (qgraph, qabove_prop) = QGraph.to_pair sigma.qgraph in
  let qcstrs = QGraph.to_qconstraints sigma.qgraph in
  let () = check_pattern_relevances sigma (Relevanceops.relevance_of_term !!env (j_val j)) in

  let evd = merge_into_evd evd defs qcstrs ucstrs in
  let evar_map = nf_evar_map sigma.evar_list sigma.qgraph defs sigma.evar_map in
  evd, Declarations.Info { qualities = sigma.qualities; univs = sigma.univs; evars = sigma.evar_list; qgraph; qabove_prop; full_qcstrs = sigma.qcstrs; full_ucstrs = sigma.ucstrs; ucstrs; evar_map; evar_defs = defs}, p, j
