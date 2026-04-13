(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
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
open Pretype_errors
open Glob_term
open Glob_ops
open GlobEnv
open Declarations
open Rewrite_rules_ops

let (!!) env = GlobEnv.env env

let level_name ?loc evd = function
  | GSProp | GProp | GSet -> None
  | GUniv u ->
    user_err ?loc
      (str "Universe " ++ Termops.pr_evd_level (State.evar_map evd) u  ++ str" cannot be matched against," ++ spc() ++ str"only captured or ignored.")
  | GRawUniv u ->
    user_err ?loc Pp.(str "Unsupported universe: " ++ Termops.pr_evd_level (State.evar_map evd) u ++ str" (raw universe).")
  | GLocalUniv {v=id; loc} ->
    Some (State.add_level ?loc ~name:id evd)

let glob_level ?loc evd : glob_level -> _ = function
  | UAnonymous {rigid} ->
    assert (rigid <> UnivFlexible true);
    State.add_level ?loc evd
  | UNamed s ->
    match level_name ?loc evd s with
    | None ->
      user_err ?loc
        (str "Universes cannot be matched against," ++ spc() ++ str"only captured or ignored.");
    | Some r -> r

let glob_quality ?loc evd : glob_quality -> _ = function
  | GRawQVar q ->
    user_err ?loc Pp.(str "Unsupported quality: " ++ Termops.pr_evd_qvar (State.evar_map evd) q ++ str" (raw qvar).")
  | GQuality QConstant q ->
    evd, (PQConstant q, Sorts.Quality.QConstant q)
  | GQuality QGlobal g ->
    evd, (PQGlobal g, Sorts.Quality.QGlobal g)
  | GQuality QVar q ->
    user_err ?loc
      (str "Quality " ++ Termops.pr_evd_qvar (State.evar_map evd) q  ++ str" cannot be matched against (local qvar).")
  | GLocalQVar {v=Anonymous} ->
    State.add_quality ?loc evd
  | GLocalQVar {v=Name id; loc} ->
    State.add_quality ?loc ~name:id evd

let sort_info ?loc evd q l =
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
  | GSProp -> assert (Option.is_empty q); evd, Sorts.PSSProp, Sorts.sprop
  | GProp -> assert (Option.is_empty q); evd, Sorts.PSProp, Sorts.prop
  | GSet ->
    begin match q with
    | None -> evd, Sorts.PSSet, Sorts.set
    | Some q ->
      let evd, (_, q) = glob_quality ?loc evd q in
      user_err ?loc
        (str "Unsupported level Set in sort with quality " ++ Termops.pr_evd_quality (State.evar_map evd) q ++ str".")
    end
  | u ->
    let evd, i, u = match level_name evd u with
    | Some (evd, (i, u)) -> evd, i, u
    | None ->
      user_err ?loc
        (str "Non-Set small universes cannot be used in algebraic expressions.")
    in
    match q with
    | None -> evd, Sorts.PSType i, Sorts.sort_of_univ (Univ.Universe.make u)
    | Some q ->
      let evd, (iq, q) = glob_quality ?loc evd q in
      evd, Sorts.make_pattern iq i, Sorts.make q (Univ.Universe.make u)

let fresh_instance_mask ?loc evd auctx : _ * _ instance_mask * UVars.Instance.t =
  let qlen, ulen = UVars.AbstractContext.size auctx in
  let evd, qs = Array.init_fold qlen (fun _ evd -> State.add_quality ?loc evd) evd in
  let qmask, qinst = Array.split qs in
  let evd, us = Array.init_fold ulen (fun _ evd -> State.add_level ?loc evd) evd in
  let umask, uinst = Array.split us in
  let mask = (qmask, umask) in
  let inst = UVars.Instance.of_array (qinst, uinst) in
  let cstrs = UVars.AbstractContext.instantiate inst auctx in
  State.enforce_constraints evd cstrs, mask, inst

let pretype_instance_mask ?loc evd (ql,ul) : _ * _ instance_mask * UVars.Instance.t =
  let evd, ql' = List.fold_left_map (glob_quality ?loc) evd ql in
  let evd, ul' = List.fold_left_map (glob_level ?loc) evd ul in
  let mask = Array.map_of_list fst ql', Array.map_of_list fst ul' in
  let inst = Array.map_of_list snd ql', Array.map_of_list snd ul' in
  evd, mask, UVars.Instance.of_array inst

let pretype_instance env evd ?loc ref u =
  let auctx = Environ.universes_of_global !!env ref in
  match u with
  | None -> fresh_instance_mask evd auctx
  | Some glob_inst ->
    let evd, mask, inst = pretype_instance_mask ?loc evd glob_inst in
    let () =
      let open UVars in
      let actual = Instance.length inst
      and expect = AbstractContext.size auctx
      in
      if not (UVars.eq_sizes actual expect) then
        Loc.raise ?loc (UnivGen.UniverseLengthMismatch { gref = ref; actual; expect })
    in
    let cstrs = UVars.AbstractContext.instantiate inst auctx in
    State.enforce_constraints evd cstrs, mask, inst


let sort ?loc evd : glob_sort -> _ = function
  | None, UAnonymous _ ->
    let evd, (i, l) = State.add_level ?loc evd in
    evd, PSType i, Sorts.sort_of_univ (Univ.Universe.make l)
  | Some q, UAnonymous _ ->
    let evd, (iq, q) = glob_quality ?loc evd q in
    let evd, (il, l) = State.add_level ?loc evd in
    evd, Sorts.make_pattern iq il, Sorts.make q (Univ.Universe.make l)
  | q, UNamed l ->
    sort_info ?loc evd q l


let pretype_case_helper pretype_argpattern env evd ?loc ind pc jc (pna, po) pnas brs =
  let p = Option.default (DAst.make ?loc (GHole GInternalHole)) po in
  let pretype_argpattern env evd tyrel c =
    let evd, pat, j = pretype_argpattern tyrel env evd c in
    evd, (pat, j_val j)
  in
  let push_rel_context evd : Constr.rel_context -> _ -> Constr.rel_context * _ =
    let Refl, Refl = Unsafe.eq, Unsafe.relevance_eq in
    GlobEnv.push_rel_context ?force_names:None (State.evar_map evd)
  in
  let evd, case, ty = Rewrite_rules_ops.indtyping_helper pretype_argpattern snd push_rel_context (!!) env evd jc ind ?pnas ~pna p brs in

  let (ci, u, pms, ((pnas, (pp, p)), pr), iv, c, brs) = case in
  let pbrs = Array.map (fun (brctx, br) -> Array.map Context.binder_name brctx, fst br) brs in
  let brs = Array.map (fun (brctx, br) -> brctx, snd br) brs in
  let body = mkCase (ci, u, pms, ((pnas, p), pr), iv, c, brs) in
  evd, PCase (pc, ind, (Array.map Context.binder_name pnas, pp), pbrs), make_judge body ty


let rec eval_pretyper_pattern env evd t : _ * _ * _ =
  let loc = t.CAst.loc in
  match DAst.get t with
  | GRef (ref,u) ->
    pretype_ref (ref, u) ?loc env evd
  | GVar id ->
    pretype_var id ?loc env evd
  | GEvar (evk, args) ->
    user_err ?loc Pp.(str"Invalid pattern: " ++ Id.print evk.CAst.v ++ str" (unknown evar type).")
  | GPatVar _ ->
    assert false
  | GApp (c, args) ->
    pretype_app (c, args) ?loc env evd
  | GProj (hd, args, c) ->
    pretype_proj (hd, args, c) ?loc env evd
  | GLambda (na, _, bk, t, c) ->
    pretype_lambda (na, bk, t, c) ?loc env evd
  | GProd (na, _, bk, t, c) ->
    pretype_prod (na, bk, t, c) ?loc env evd
  | GLetIn (na, _, b, t, c) ->
    pretype_letin (na, b, t, c) ?loc env evd
  | GCases (st, c, tm, cl) ->
    pretype_cases (st, c, tm, cl) ?loc env evd
  | GLetTuple (na, b, t, c) ->
    pretype_lettuple (na, b, t, c) ?loc env evd
  | GIf (c, r, t1, t2) ->
    pretype_if (c, r, t1, t2) ?loc env evd
  | GRec (knd, nas, decl, c, t) ->
    pretype_rec (knd, nas, decl, c, t) ?loc env evd
  | GSort s ->
    pretype_sort s ?loc env evd
  | GHole _ ->
    user_err ?loc Pp.(str"Invalid pattern: _ (unknown evar type).")
  | GGenarg arg ->
    pretype_genarg arg ?loc env evd
  | GCast (c, k, t) ->
    pretype_cast (c, k, t) ?loc env evd
  | GInt n ->
    pretype_int n ?loc env evd
  | GFloat f ->
    pretype_float f ?loc env evd
  | GString s ->
    pretype_string s ?loc env evd
  | GArray (u,t,def,ty) ->
    pretype_array (u,t,def,ty) ?loc env evd

and eval_pretyper_arg_pattern tycon env evd t =
  let loc = t.CAst.loc in
  match DAst.get t with
  | GEvar (evk, args) ->
    pretype_evar (evk, args) ?loc tycon env evd
  | GHole _ ->
    pretype_hole ?loc tycon env evd
  | _ ->
    let evd, pat, j = eval_pretyper_pattern env evd t in
    let evd = Rewrite_rules_ops.cumul_lax !!env evd j.uj_type (fst tycon) in
    let evd = State.add_pattern_relevance (Relevanceops.relevance_of_term !!env (j_val j)) evd in
    evd, Pat pat, j


and pretype_ref (ref, u) =
  fun ?loc env evd ->
  let evd, mask, u = pretype_instance env evd ?loc ref u in
  let evd, p, j =
    match ref with
    | IndRef ind ->
        let evd, j = judge_of_inductive !!env evd (ind, u) in
        evd, PInd (ind, mask), j
    | ConstructRef c ->
        let evd, j = judge_of_constructor !!env evd (c, u) in
        evd, PConstr (c, mask), j
    | ConstRef c ->
        if not @@ Environ.is_symbol !!env c then user_err ?loc Pp.(str"Invalid pattern: " ++ GlobRef.print ref ++ str".");
        let evd, j = judge_of_constant !!env evd (c, u) in
        evd, PSymbol (c, mask), j
    | VarRef _ -> user_err ?loc Pp.(str"Invalid pattern: " ++ GlobRef.print ref ++ str".")
  in
  evd, p, j

and pretype_var id =
  fun ?loc env evd ->
  match lookup_rel_id id (Environ.rel_context !!env) with
  | (n, _, typ) ->
    evd, PRel n, make_judge (mkRel n) (Constr.lift n typ)
  | exception Not_found ->
    (* [id] not found, standard error message *)
    error_var_not_found ?loc !!env (State.evar_map evd) id

and pretype_evar (CAst.{v=id;loc=locid}, inst) ?loc (ty, rel) env evd =
  let id = interp_ltac_id env id in
  match Evd.evar_key (Libnames.make_qualid DirPath.empty id) (State.evar_map evd) with
  | exception Not_found ->
    if not @@ List.is_empty inst then
      user_err ?loc Pp.(str"Invalid pattern: " ++ Id.print id ++ str" (nonempty instance).");
    let evd, (i, ev) = State.add_patvar ?loc ~name:(Name id) !!env evd ty rel Rigid in
    let j = make_judge ev ty in
    evd, PVar i, j

  | evk -> user_err ?loc Pp.(str"Invalid pattern: " ++ Id.print id ++ str" (nonlinearity).")
  (* let EvarInfo evi = Evd.find evd evk in
  let hyps = evar_filtered_context evi in
  let evd, args = pretype_instance default_pretyper ~flags env evd loc hyps evk inst in
  let args = SList.map EConstr.to_constr args (but evars in evd are still allowed) in
  let c = mkLEvar evd (evk, args) in
  let j = Retyping.get_judgment_of !!env evd c in
  evd, PTermEq (evk, Some id), j *)

and pretype_hole ?loc (ty, rel) env evd =
  let evd, (i, ev) = State.add_patvar ?loc ~name:(Anonymous) !!env evd ty rel Freestanding in
  evd, PVar i, make_judge ev ty

and pretype_genarg arg ?loc env evd =
  user_err ?loc Pp.(str"Invalid pattern (genarg patterns not supported).")

and pretype_rec (fixkind, names, bl, lar, vdef) =
  fun ?loc env evd ->
  user_err ?loc Pp.(str"Invalid pattern (fixpoint/cofixpoint patterns not supported).")

and pretype_sort s =
  fun ?loc env evd ->
  let evd, ps, s = sort ?loc evd s in
  let evd, sup = State.create_super_sort !!env evd s in
  let j = make_judge (mkSort s) (mkSort sup) in
  evd, PSort ps, j

and pretype_app (f, args) =
  fun ?loc env evd ->
  (* Test for primitive projections *)
  match DAst.get f with
  | GRef (ConstRef p, u) when Structures.PrimitiveProjections.mem p ->
    let c, args = List.sep_last args in
    pretype_proj ((p, u), args, c) ?loc env evd
  | _ ->
  let evd, pf, fj = eval_pretyper_pattern env evd f in

  let one_app env evd pf fj arg =
    let evd, (argty, argrel, retty) = reduce_to_prod !!env evd (j_type fj) in

    let evd, parg, jarg = eval_pretyper_arg_pattern (argty, argrel) env evd arg in

    let retty = CVars.subst1 (j_val jarg) retty in
    let head = mkApp (j_val fj, [|j_val jarg|]) in
    evd, PApp (pf, parg), make_judge head retty
  in

  List.fold_left (fun (evd, pf, fj) arg -> one_app env evd pf fj arg) (evd, pf, fj) args


and pretype_proj ((f,us), args, c) =
  fun ?loc env evd ->
  let evd, _, u = pretype_instance env evd ?loc (ConstRef f) us in
  match Structures.PrimitiveProjections.find_opt_with_relevance (f, EInstance.make u) with
  | None ->
      pretype_app (DAst.make ?loc (GRef (GlobRef.ConstRef f,us)), args @ [c])
        ?loc env evd
  | Some (p, rel) ->
    let evd, pc, jc = eval_pretyper_pattern env evd c in
    let ind = Projection.Repr.inductive p in
    let evd, (u, args) = reduce_to_appind !!env evd ind (j_type jc) in

    let p' = Projection.make p false in

    let pr, pty = lookup_projection p' !!env in
    let pr = UVars.subst_instance_relevance u pr in
    let ty = CVars.subst_instance_constr u pty in
    let bod = mkProj (p', pr, j_val jc) in
    let ty = CVars.substl (j_val jc :: CArray.rev_to_list args) ty in
    evd, PProj (pc, p), make_judge bod ty


and pretype_lambda (name, bk, cty, body) =
  fun ?loc env evd ->

  let evd, ty_sort = State.create_universe ?loc evd in
  let ty_rel = Sorts.relevance_of_sort ty_sort in
  let evd, pty, jty = eval_pretyper_arg_pattern (mkSort ty_sort, Sorts.Relevant) env evd cty in

  let open Context.Rel.Declaration in
  let Refl, Refl = Unsafe.eq, Unsafe.relevance_eq in
  let decl = Context.(Rel.Declaration.LocalAssum (make_annot name ty_rel, j_val jty)) in
  let decl, env = push_rel (State.evar_map evd) decl env in
  let binder = get_annot decl in

  let evd, pb, jb = eval_pretyper_pattern env evd body in
  let resj = make_judge (mkLambda (binder, jty.uj_val, jb.uj_val)) (mkProd (binder, jty.uj_val, jb.uj_type)) in
  evd, PLambda (binder.binder_name, pty, pb), resj

and pretype_prod (name, bk, c1, c2) =
  fun ?loc env evd ->

  let evd, dom_sort = State.create_universe evd in
  let domr = Sorts.relevance_of_sort dom_sort in
  let evd, pdom, jdom = eval_pretyper_arg_pattern (mkSort dom_sort, Sorts.Relevant) env evd c1 in

  let open Context.Rel.Declaration in
  let Refl, Refl = Unsafe.eq, Unsafe.relevance_eq in
  let decl = Context.(Rel.Declaration.LocalAssum (make_annot name domr, j_val jdom)) in
  let decl, env = push_rel (State.evar_map evd) decl env in
  let binder = get_annot decl in

  let evd, cod_sort = State.create_universe evd in
  let evd, pcod, jcod = eval_pretyper_arg_pattern (mkSort cod_sort, Sorts.Relevant) env evd c2 in

  let evd, ret_sort = State.create_product_sort !!env evd dom_sort cod_sort in
  let resj = make_judge (mkProd (binder, jdom.uj_val, jcod.uj_val)) (mkSort ret_sort) in
  evd, PProd (binder.binder_name, pdom, pcod), resj

and pretype_letin (name, c1, t, c2) =
  fun ?loc env evd ->
  user_err ?loc Pp.(str"Invalid pattern (let-definitions are not patterns).")

and pretype_lettuple (nal, (na, po), c, d) =
  fun ?loc env evd ->
  let evd, pc, jc = eval_pretyper_pattern env evd c in
  let evd = State.add_pattern_relevance (Relevanceops.relevance_of_term !!env (j_val jc)) evd in

  let ind =
    match Inductive.find_rectype !!env (j_type jc) with
    | (ind, _), _ -> ind
    | exception Not_found -> user_err ?loc Pp.(str "Cannot guess inductive.")
  in
  let (mib, mip) = Inductive.lookup_mind_specif !!env ind in

  let brs =
    if Array.length mip.mind_consnrealdecls <> 1 then
      user_err ?loc Pp.(str "Wrong number of constructors for an let destruction pattern");
    [| Some (Array.of_list nal), d |]
  in

  pretype_case_helper eval_pretyper_arg_pattern env evd ?loc ind pc jc (na, po) None brs

and pretype_cases (sty, po, tml, eqns) =
  fun ?loc env evd ->

  let c, na, io = match tml with
  | [] -> assert false
  | _ :: _ :: _ -> user_err ?loc Pp.(str"Invalid pattern (match constructions with more than one scrutinee not supported).")
  | [c, (na, io)] -> c, na, io
  in

  let evd, pc, jc = eval_pretyper_pattern env evd c in
  let evd = State.add_pattern_relevance (Relevanceops.relevance_of_term !!env (j_val jc)) evd in

  let ind, io, nb_brs =
    match io with
    | Some ({ CAst.v=(ind, nas); loc}) ->
      let (mib, mip) = Inductive.lookup_mind_specif !!env ind in
      if List.length nas <> mip.mind_nrealdecls then
        user_err ?loc Pp.(str "Ill-formed 'in' clause in cases.");
      ind, Some (Array.of_list (nas @ [na])), Array.length mip.mind_nf_lc
    | None ->
      let ind = match List.find_map (function { CAst.v=(_, [pat], _); _ } -> (match DAst.get pat with PatCstr (cstr, _, _) -> Some (fst cstr) | _ -> None) | _ -> None) eqns with
      | Some ind -> ind
      | None -> match Inductive.find_rectype !!env (j_type jc) with
        | (ind, _), _ -> ind
        | exception Not_found -> user_err ?loc Pp.(str "Cannot guess inductive.")
      in
      let (mib, mip) = Inductive.lookup_mind_specif !!env ind in
      ind, None, Array.length mip.mind_nf_lc
  in

  let brs = WriteOnceArray.make nb_brs in

  let brs = List.fold_left (fun brs eqn ->
    match eqn with
    | { CAst.v = (ids, [pat], rhs); loc } ->
      begin match DAst.get pat with
      | PatVar na ->
        if not @@ Name.equal na Anonymous then user_err ?loc Pp.(str"Invalid pattern (alias not supported).")
        else WriteOnceArray.fill_remaining (None, rhs) brs
      | PatCstr (cstr, pats, na) ->
        let (ind', i) = cstr in
        let i = i-1 in
        if not @@ Ind.CanOrd.equal ind ind' then user_err ?loc Pp.(str"Invalid pattern (wrong constructor).")
        else
        if not @@ Name.equal na Anonymous then user_err ?loc Pp.(str"Invalid pattern (alias not supported).")
        else
        if WriteOnceArray.is_filled i brs then user_err ?loc Pp.(str"Redundant branch.")
        else
        let inner_vars = Array.map_of_list (fun pat ->
            match DAst.get pat with
            | PatVar na -> na
            | PatCstr _ -> user_err ?loc Pp.(str"Invalid pattern (deep pattern-matching not supported).")) pats
        in
        WriteOnceArray.add i (Some inner_vars, rhs) brs
      end
    | { CAst.loc; _ } -> user_err ?loc Pp.(str"Invalid pattern (match constructions with more than one scrutinee not supported)."))
    brs eqns
  in

  let brs =
    match WriteOnceArray.to_array_opt brs with
    | Some brs -> brs
    | None -> user_err ?loc Pp.(str"Invalid pattern (missing a branch).")
  in

  pretype_case_helper eval_pretyper_arg_pattern env evd ?loc ind pc jc (na, po) io brs

and pretype_if (c, (na, po), b1, b2) =
  fun ?loc env evd ->

  let evd, pc, jc = eval_pretyper_pattern env evd c in
  let evd = State.add_pattern_relevance (Relevanceops.relevance_of_term !!env (j_val jc)) evd in

  let ind =
    match Inductive.find_rectype !!env (j_type jc) with
    | (ind, _), _ -> ind
    | exception Not_found -> user_err ?loc Pp.(str "Cannot guess inductive.")
  in
  let (mib, mip) = Inductive.lookup_mind_specif !!env ind in

  let brs =
    let () = match mip.mind_consnrealdecls with
    | [| 0; 0 |] -> ()
    | [| _; _ |] -> user_err ?loc Pp.(str "Cannot support constructors with arguments in if pattern")
    | _ -> user_err ?loc Pp.(str "Wrong number of constructors for an if pattern")
    in
    [| Some [||], b1; Some [||], b2 |]
  in

  pretype_case_helper eval_pretyper_arg_pattern env evd ?loc ind pc jc (na, po) None brs

and pretype_cast (c, k, t) =
  fun ?loc env evd ->
    user_err ?loc Pp.(str"Invalid pattern (casts cannot be enforced).")

and pretype_int i =
  fun ?loc env evd ->
  let resj = make_judge (mkInt i) (Typeops.type_of_int !!env) in
  evd, PInt i, resj

and pretype_float f =
  fun ?loc env evd ->
  let resj = make_judge (mkFloat f) (Typeops.type_of_float !!env) in
  evd, PFloat f, resj

and pretype_string s =
  fun ?loc env evd ->
  let resj = make_judge (mkString s) (Typeops.type_of_string !!env) in
  evd, PString s, resj

and pretype_array (u,t,def,ty) =
  fun ?loc env evd ->
  user_err ?loc Pp.(str"Invalid pattern (array patterns not supported).")


let eval_pretyper_pattern env evd c =
  let open Rewrite_rules_ops in
  let evd = State.make evd in
  let env = GlobEnv.make env (State.evar_map evd) empty_lvar in
  let evd, p, j = eval_pretyper_pattern env evd c in

  Rewrite_rules_ops.typecheck_finalize ~loc:c.loc !!env evd p j
