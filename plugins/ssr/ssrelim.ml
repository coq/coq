(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* This file is (C) Copyright 2006-2015 Microsoft Corporation and Inria. *)

open Util
open Names
open Printer
open Constr
open Context
open Termops
open Tactypes

open Ssrmatching_plugin
open Ssrmatching

open Ssrast
open Ssrprinters
open Ssrcommon

open Proofview.Notations

module RelDecl = Context.Rel.Declaration

(** The "case" and "elim" tactic *)

(* TASSI: given the type of an elimination principle, it finds the higher order
 * argument (index), it computes it's arity and the arity of the eliminator and
 * checks if the eliminator is recursive or not *)
let analyze_eliminator elimty env sigma =
  let open EConstr in
  let rec loop ctx t = match kind_of_type sigma t with
  | AtomicType (hd, args) when isRel sigma hd ->
    ctx, destRel sigma hd, not (Vars.noccurn sigma 1 t), Array.length args, t
  | CastType (t, _) -> loop ctx t
  | ProdType (x, ty, t) -> loop (RelDecl.LocalAssum (x, ty) :: ctx) t
  | LetInType (x,b,ty,t) -> loop (RelDecl.LocalDef (x, b, ty) :: ctx) (Vars.subst1 b t)
  | _ ->
    let env' = push_rel_context ctx env in
    let t' = Reductionops.whd_all env' sigma t in
    if not (eq_constr sigma t t') then loop ctx t' else
      errorstrm Pp.(str"The eliminator has the wrong shape."++spc()++
      str"A (applied) bound variable was expected as the conclusion of "++
      str"the eliminator's"++Pp.cut()++str"type:"++spc()++pr_econstr_env env' sigma elimty) in
  let ctx, pred_id, elim_is_dep, n_pred_args,concl = loop [] elimty in
  let n_elim_args = Context.Rel.nhyps ctx in
  let is_rec_elim =
     let count_occurn n term =
       let count = ref 0 in
       let rec occur_rec n c = match EConstr.kind sigma c with
         | Rel m -> if m = n then incr count
         | Evar (_, args) -> SList.Skip.iter (fun c -> occur_rec n c) args
         | _ -> EConstr.iter_with_binders sigma succ occur_rec n c
       in
       occur_rec n term; !count in
     let occurr2 n t = count_occurn n t > 1 in
     not (List.for_all_i
       (fun i (_,rd) -> pred_id <= i || not (occurr2 (pred_id - i) rd))
       1 (assums_of_rel_context ctx))
  in
  n_elim_args - pred_id, n_elim_args, is_rec_elim, elim_is_dep, n_pred_args,
  (ctx,concl)

let subgoals_tys sigma (relctx, concl) =
  let rec aux cur_depth acc = function
    | hd :: rest ->
        let ty = Context.Rel.Declaration.get_type hd in
        if EConstr.Vars.noccurn sigma cur_depth concl &&
           List.for_all_i (fun i -> function
             | Context.Rel.Declaration.LocalAssum(_, t) ->
                EConstr.Vars.noccurn sigma i t
             | Context.Rel.Declaration.LocalDef (_, b, t) ->
                EConstr.Vars.noccurn sigma i t && EConstr.Vars.noccurn sigma i b) 1 rest
        then aux (cur_depth - 1) (ty :: acc) rest
        else aux (cur_depth - 1) acc rest
    | [] -> Array.of_list (List.rev acc)
  in
    aux (List.length relctx) [] (List.rev relctx)

(* A case without explicit dependent terms but with both a view and an    *)
(* occurrence switch and/or an equation is treated as dependent, with the *)
(* viewed term as the dependent term (the occurrence switch would be      *)
(* meaningless otherwise). When both a view and explicit dependents are   *)
(* present, it is forbidden to put a (meaningless) occurrence switch on   *)
(* the viewed term.                                                       *)

(* This is both elim and case (defaulting to the former). If ~elim is omitted
 * the standard eliminator is chosen. The code is made of 4 parts:
 * 1. find the eliminator if not given as ~elim and analyze it
 * 2. build the patterns to be matched against the conclusion, looking at
 *    (occ, c), deps and the pattern inferred from the type of the eliminator
 * 3. build the new predicate matching the patterns, and the tactic to
 *    generalize the equality in case eqid is not None
 * 4. build the tactic handle instructions and clears as required in ipats and
 *    by eqid *)

let get_eq_type env sigma =
  Evd.fresh_global env sigma Rocqlib.(lib_ref "core.eq.type")

type elim_what =
| EConstr of
        Ssrast.ssrhyp list * Ssrmatching.occ *
          EConstr.constr
| EGen of
    ((Ssrast.ssrhyp list option *
      Ssrmatching.occ) *
      Ssrmatching.cpattern)

let check_elim sigma has_elim = function
| EConstr(_,_,t) when EConstr.isEvar sigma t ->
      anomaly "elim called on a constr evar"
| EGen (_, g) when not has_elim && is_wildcard g ->
      errorstrm Pp.(str"Indeterminate pattern and no eliminator")
| EGen ((Some clr,occ), g) when is_wildcard g ->
      Proofview.tclUNIT (None, clr, occ, None)
| EGen ((None, occ), g) when is_wildcard g ->
      Proofview.tclUNIT (None,[],occ,None)
| EGen ((_, occ), p as gen) ->
  Proofview.Goal.enter_one begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let concl = Proofview.Goal.concl gl in
    let sigma, (_, c, clr) = interp_gen env sigma ~concl true gen in
    Proofview.Unsafe.tclEVARS sigma <*> Proofview.tclUNIT (Some c, clr, occ, Some p)
  end
| EConstr (clr, occ, c) ->
      Proofview.tclUNIT (Some c, clr, occ, None)

let match_pat env sigma0 p occ h cl =
  debug_ssr (fun () -> Pp.(str"matching: " ++ pr_occ occ ++ pp_pattern env p));
  let (c,ucst), cl =
    fill_occ_pattern ~raise_NoMatch:true env sigma0 cl p occ h in
  debug_ssr (fun () -> Pp.(str"     got: " ++ pr_econstr_env env sigma0 c));
  c, cl, ucst

let fire_subst sigma t = Reductionops.nf_evar sigma t

let mkTpat env sigma0 (sigma, t) = (* takes a term, refreshes it and makes a T pattern *)
  let t, evs, ucst = abs_evars env sigma0 (sigma, fire_subst sigma t) in
  let t, _, _, sigma = saturate ~beta:true env sigma t (List.length evs) in
  { pat_sigma = Evd.merge_universe_context sigma ucst; pat_pat = T t }

let redex_of_pattern env p = match redex_of_pattern p with
| None -> CErrors.anomaly (Pp.str "pattern without redex.")
| Some (sigma, e) -> Evarutil.nf_evar sigma e, Evd.ustate sigma

let unif_redex env sigma0 nsigma p t = (* t is a hint for the redex of p *)
  let t, evs, ucst = abs_evars env sigma0 (nsigma, fire_subst nsigma t) in
  let t, _, _, sigma = saturate ~beta:true env p.pat_sigma t (List.length evs) in
  let sigma = Evd.merge_universe_context sigma ucst in
  match p.pat_pat with
  | X_In_T (e, p) -> { pat_sigma = sigma; pat_pat = E_As_X_In_T (t, e, p) }
  | _ ->
    try { p with pat_sigma = unify_HO env sigma t (fst (redex_of_pattern env p)) }
    with e when CErrors.noncritical e -> p

let get_nth_arg n args =
  List.find_map_exn (fun (i, x, _) -> if Int.equal i n then Some x else None) args

let find_eliminator env sigma ~concl ~is_case ?elim oc c_gen =
  match elim with
  | Some elim ->
    let sigma, elimty = Typing.type_of env sigma elim in
    let elimty =
      let rename_elimty r =
        EConstr.of_constr
          (Arguments_renaming.rename_type
            (EConstr.to_constr ~abort_on_undefined_evars:false sigma
              elimty) r) in
      match EConstr.kind sigma elim with
      | Constr.Var kn -> rename_elimty (GlobRef.VarRef kn)
      | Constr.Const (kn,_) -> rename_elimty (GlobRef.ConstRef kn)
      | _ -> elimty
    in
    let pred_id, n_elim_args, is_rec, elim_is_dep, n_pred_args,ctx_concl =
      analyze_eliminator elimty env sigma in
    let seed = subgoals_tys sigma ctx_concl in
    let elim, elimty, elim_args, sigma =
      saturate ~beta:is_case env sigma elim ~ty:elimty n_elim_args in
    let pred = get_nth_arg pred_id elim_args in
    let elimty = Reductionops.whd_all env sigma elimty in
    let cty, sigma =
      if Option.is_empty oc then None, sigma
      else
        let c = Option.get oc in
        let sigma, c_ty = Typing.type_of env sigma c in
        let pc = match c_gen with
          | Some p -> interp_cpattern env sigma p None
          | _ -> mkTpat env sigma (sigma, c) in
        Some(c, c_ty, pc), sigma in
    sigma, seed, cty, elim, elimty, elim_args, n_elim_args, elim_is_dep, is_rec, pred
  | None ->
    let c = Option.get oc in
    let sigma, c_ty = Typing.type_of env sigma c in
    let ((kn, i),_ as indu), unfolded_c_ty =
      Tacred.reduce_to_quantified_ind env sigma c_ty in
    let sort = Retyping.get_sort_of env sigma concl in
    let sigma, elim, elimty =
      if not is_case then
        let sigma, elim = Evd.fresh_global env sigma
            (Indrec.lookup_eliminator env (kn,i) (EConstr.ESorts.family sigma sort))
        in
        let elimty = Retyping.get_type_of env sigma elim in
        sigma, elim, elimty
      else
        let sigma, case = Indrec.build_case_analysis_scheme env sigma indu true sort in
        let (ind, indty) = Indrec.eval_case_analysis case in
        (sigma, ind, indty)
    in
    let pred_id,n_elim_args,is_rec,elim_is_dep,n_pred_args,ctx_concl =
      analyze_eliminator elimty env sigma in
    let seed =
      if is_case then
        let mind,indb = Inductive.lookup_mind_specif env (kn,i) in
        let tys = indb.Declarations.mind_nf_lc in
        let renamed_tys =
          Array.mapi (fun j (ctx, cty) ->
            let t = Term.it_mkProd_or_LetIn cty ctx in
                  debug_ssr (fun () -> Pp.(str "Search" ++ Printer.pr_constr_env env sigma t));
            let t = Arguments_renaming.rename_type t
              (GlobRef.ConstructRef((kn,i),j+1)) in
            debug_ssr (fun () -> Pp.(str"Done Search " ++ Printer.pr_constr_env env sigma t));
              t)
          tys
        in
        let drop_params x =
          snd @@ EConstr.decompose_prod_n_decls sigma
            mind.Declarations.mind_nparams (EConstr.of_constr x) in
        Array.map drop_params renamed_tys
      else
        subgoals_tys sigma ctx_concl
    in
    let rctx = fst (EConstr.decompose_prod_decls sigma unfolded_c_ty) in
    let n_c_args = Context.Rel.length rctx in
    let c, c_ty, t_args, sigma = saturate env sigma c ~ty:c_ty n_c_args in
    let elim, elimty, elim_args, sigma =
      saturate ~beta:is_case env sigma elim ~ty:elimty n_elim_args in
    let pred = get_nth_arg pred_id elim_args in
    let pc = match n_c_args, c_gen with
      | 0, Some p -> interp_cpattern env sigma p None
      | _ -> mkTpat env sigma (sigma, c) in
    let cty = Some (c, c_ty, pc) in
    let elimty = Reductionops.whd_all env sigma elimty in
    sigma, seed, cty, elim, elimty, elim_args, n_elim_args, elim_is_dep, is_rec, pred

let saturate_until env sigma c c_ty f =
  let rec loop n = try
    let c, c_ty, _, sigma = saturate env sigma c ~ty:c_ty n in
    let sigma' = f sigma c c_ty in
    Some (c, c_ty, sigma, sigma')
  with
  | NotEnoughProducts -> None
  | e when CErrors.noncritical e -> loop (n+1) in loop 0

let get_head_pattern env sigma elim_is_dep elim_args n_elim_args inf_deps_r cty = match cty with
| None -> sigma, true (* The user wrote elim: _ *)
| Some (c, c_ty, _) ->
  let rec first = function
    | [] ->
      errorstrm Pp.(str"Unable to apply the eliminator to the term"++
        spc()++pr_econstr_env env sigma c++spc())
    | x :: rest ->
      match x () with
      | None -> first rest
      | Some (sigma, b) -> sigma, b
  in
  (* Unify two terms if their heads are not applied unif variables, eg
    * not (?P x). The idea is to rule out cases where the problem is too
    * vague to drive the current heuristics. *)
  let unify_HO_rigid env sigma a b =
    let is_applied_evar x = match EConstr.kind sigma x with
      | App(x,_) -> EConstr.isEvar sigma x
      | _ -> false in
    if is_applied_evar a || is_applied_evar b then
      raise Evarconv.(UnableToUnify(sigma,
                Pretype_errors.ProblemBeyondCapabilities))
    else unify_HO env sigma a b in
  let try_c_last_arg () =
    (* we try to see if c unifies with the last arg of elim *)
    if elim_is_dep then None else
    let arg = get_nth_arg (n_elim_args - 1) elim_args in
    let sigma, arg_ty = Typing.type_of env sigma arg in
    match saturate_until env sigma c c_ty (fun sigma c c_ty ->
      unify_HO env (unify_HO_rigid env sigma c_ty arg_ty) arg c) with
    | Some (c, _, _, sigma) -> Some (sigma, false)
    | None -> None in
  let try_c_last_pattern () =
    (* we try to see if c unifies with the last inferred pattern *)
    if inf_deps_r = [] then None else
    let inf_arg = List.hd inf_deps_r in
    let sigma, inf_arg_ty = Typing.type_of env sigma inf_arg in
    match saturate_until env sigma c c_ty (fun sigma _ c_ty ->
            unify_HO_rigid env sigma c_ty inf_arg_ty) with
    | Some (c, _, _, sigma) -> Some(sigma, true)
    | None -> None in
  first [try_c_last_arg;try_c_last_pattern]

let check_pattern_instantiated env sigma patterns =
  let evars_of_term = Evarutil.undefined_evars_of_term sigma in
  let patterns = List.map (fun (_,_,t,_) -> Reductionops.nf_evar sigma t) patterns in
  let patterns_ev = List.map evars_of_term patterns in
  let ev = List.fold_left Evar.Set.union Evar.Set.empty patterns_ev in
  let ty_ev = Evar.Set.fold (fun i e ->
        let ex = i in
        let i_ty = Evd.evar_concl (Evd.find_undefined sigma ex) in
        Evar.Set.union e (evars_of_term i_ty))
    ev Evar.Set.empty in
  let inter = Evar.Set.inter ev ty_ev in
  if not (Evar.Set.is_empty inter) then begin
    let i = Evar.Set.choose inter in
    let pat = List.find (fun t -> Evar.Set.mem i (evars_of_term t)) patterns in
    errorstrm Pp.(str"Pattern"++spc()++pr_econstr_pat env sigma pat++spc()++
      str"was not completely instantiated and one of its variables"++spc()++
      str"occurs in the type of another non-instantiated pattern variable");
  end

let is_undef_pat { pat_sigma = sigma; pat_pat = pat } = match pat with
| T t -> EConstr.isEvar sigma t
| _ -> false

let generate_pred env sigma0 ~concl patterns predty eqid is_rec deps elim_args n_elim_args c_is_head_p clr sigma =
  let concl0 = concl in
  let error sigma t inf_t = errorstrm Pp.(str"The given pattern matches the term"++
    spc()++pr_econstr_env env sigma t++spc()++str"while the inferred pattern"++
    spc()++pr_econstr_pat env sigma (fire_subst sigma inf_t)++spc()++ str"doesn't") in
  let match_or_postpone (cl, sigma, post) (h, p, inf_t, occ) =
    let p = unif_redex env sigma0 sigma p inf_t in
    if is_undef_pat p then
      let () = debug_ssr (fun () -> Pp.(str"postponing " ++ pp_pattern env p)) in
      cl, sigma, post @ [h, p, inf_t, occ]
    else try
      let c, cl, ucst = match_pat env sigma0 p occ h cl in
      let sigma = Evd.merge_universe_context sigma ucst in
      let sigma = try unify_HO env sigma inf_t c
                with exn when CErrors.noncritical exn -> error sigma c inf_t in
      cl, sigma, post
    with
    | NoMatch | NoProgress ->
        let e, ucst = redex_of_pattern env p in
        let sigma = Evd.merge_universe_context sigma ucst in
        let e, evs, _ucst = abs_evars env sigma (p.pat_sigma, e) in
        let e, _, _, sigma = saturate ~beta:true env sigma e (List.length evs) in
        let sigma = try unify_HO env sigma inf_t e
                  with exn when CErrors.noncritical exn -> error sigma e inf_t in
        cl, sigma, post
  in
  let rec match_all concl sigma patterns =
    let concl, sigma, postponed =
      List.fold_left match_or_postpone (concl, sigma, []) patterns in
    if postponed = [] then concl, sigma
    else if List.length postponed = List.length patterns then
      errorstrm Pp.(str "Some patterns are undefined even after all"++spc()++
        str"the defined ones matched")
    else match_all concl sigma postponed in
  let concl, sigma = match_all concl sigma patterns in
  let pred_rctx, _ = EConstr.decompose_prod_decls sigma (fire_subst sigma predty) in
  let sigma, concl, gen_eq_tac, clr = match eqid with
  | Some (IPatId _) when not is_rec ->
      let k = List.length deps in
      let c = fire_subst sigma (get_nth_arg (n_elim_args - k - 1) elim_args) in
      let sigma, t = Typing.type_of env sigma c in
      let sigma, eq = get_eq_type env sigma in
      let sigma, gen_eq_tac, eq_ty =
        let refl = EConstr.mkApp (eq, [|t; c; c|]) in
        let new_concl = EConstr.mkArrow refl EConstr.ERelevance.relevant (EConstr.Vars.lift 1 concl0) in
        let new_concl = fire_subst sigma new_concl in
        let sigma, erefl = mkRefl env sigma t c in
        let erefl = fire_subst sigma erefl in
        let erefl_ty = Retyping.get_type_of env sigma erefl in
        let eq_ty = Retyping.get_type_of env sigma erefl_ty in
        let ucst = Evd.ustate sigma in
        let evds = Evar.Map.bind (Evd.find_undefined sigma) @@
          Evd.evars_of_term sigma new_concl in
        let gen_eq_tac =
          let open Proofview.Notations in
          Proofview.Goal.enter begin fun s ->
          let sigma = Proofview.Goal.sigma s in
          let sigma = Evd.merge_universe_context sigma ucst in
          let sigma, shelve = Evar.Map.fold (fun e info (sigma, shelve) ->
              if not @@ Evd.mem sigma e then
                Evd.add sigma e info, e::shelve else
                (sigma, shelve))
              evds (sigma, []) in
          Proofview.Unsafe.tclEVARS sigma <*>
          Proofview.shelve_goals @@ shelve <*>
          Tactics.apply_type ~typecheck:true new_concl [erefl]
          end
        in
        sigma, gen_eq_tac, eq_ty
      in
      let rel = k + if c_is_head_p then 1 else 0 in
      let sigma, src = mkProt env sigma eq_ty EConstr.(mkApp (eq,[|t; c; mkRel rel|])) in
      let concl = EConstr.mkArrow src EConstr.ERelevance.relevant (EConstr.Vars.lift 1 concl) in
      let clr = if deps <> [] then clr else [] in
      sigma, concl, gen_eq_tac, clr
  | _ -> sigma, concl, Tacticals.tclIDTAC, clr in
  let mk_lam t r = EConstr.mkLambda_or_LetIn r t in
  let concl = List.fold_left mk_lam concl pred_rctx in
  let sigma, concl =
    if eqid <> None && is_rec then
      let sigma, concls = Typing.type_of env sigma concl in
      let sigma, concl = mkProt env sigma concls concl in
      let sigma, _ = Typing.type_of env sigma concl in
      sigma, concl
    else sigma, concl in
  sigma, concl, gen_eq_tac, clr

let compute_patterns env sigma0 what c_is_head_p cty deps inf_deps_r occ orig_clr eqid sigma =
  let rec loop patterns clr i = function
    | [],[] -> patterns, clr, sigma
    | ((oclr, occ), t):: deps, inf_t :: inf_deps ->
        let p = interp_cpattern env sigma0 t None in
        let clr_t =
          interp_clr sigma (oclr,(tag_of_cpattern t, fst (redex_of_pattern env p))) in
        (* if we are the index for the equation we do not clear *)
        let clr_t = if deps = [] && eqid <> None then [] else clr_t in
        let p = if is_undef_pat p then mkTpat env sigma0 (sigma, inf_t) else p in
        loop (patterns @ [i, p, inf_t, occ])
          (clr_t @ clr) (i+1) (deps, inf_deps)
    | [], c :: inf_deps ->
        debug_ssr (fun () -> Pp.(str"adding inf pattern " ++ pr_econstr_pat env sigma c));
        loop (patterns @ [i, mkTpat env sigma0 (sigma, c), c, allocc])
          clr (i+1) ([], inf_deps)
    | _::_, [] -> errorstrm Pp.(str "Too many dependent abstractions") in
  let deps, head_p, inf_deps_r = match what, c_is_head_p, cty with
  | EConstr _, _, None -> anomaly "Simple elim with no term"
  | _, false, _ -> deps, [], inf_deps_r
  | EGen gen, true, None -> deps @ [gen], [], inf_deps_r
  | _, true, Some (c, _, pc) ->
        let occ = if occ = None then allocc else occ in
        let inf_p, inf_deps_r = List.hd inf_deps_r, List.tl inf_deps_r in
        deps, [1, pc, inf_p, occ], inf_deps_r in
  let patterns, clr, sigma =
    loop [] orig_clr (List.length head_p+1) (List.rev deps, inf_deps_r) in
  sigma, head_p @ patterns, Util.List.uniquize clr

let ssrelim ?(is_case=false) deps what ?elim eqid elim_intro_tac =
  let open Proofview.Notations in
  Proofview.tclEVARMAP >>= begin fun sigma ->
  (* some sanity checks *)
  check_elim sigma (Option.has_some elim) what end >>=

  fun (oc, orig_clr, occ, c_gen) ->
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let concl = Proofview.Goal.concl gl in
  let sigma0 = sigma in
  debug_ssr (fun () -> (Pp.str(if is_case then "==CASE==" else "==ELIM==")));
  (* finds the eliminator applies it to evars and c saturated as needed  *)
  (* obtaining "elim ??? (c ???)". pred is the higher order evar         *)
  (* cty is None when the user writes _ (hence we can't make a pattern *)
  (* `seed` represents the array of types from which we derive the name seeds
     for the block intro patterns *)
  let sigma, seed, cty, elim, elimty, elim_args, n_elim_args, elim_is_dep, is_rec, pred =
    find_eliminator env sigma ~concl ~is_case ?elim oc c_gen
  in
  let () =
    debug_ssr (fun () -> Pp.(str"elim= "++ pr_econstr_pat env sigma elim));
    debug_ssr (fun () -> Pp.(str"elimty= "++ pr_econstr_pat env sigma elimty)) in
  let open EConstr in
  let inf_deps_r = match kind_of_type sigma elimty with
    | AtomicType (_, args) -> List.rev (Array.to_list args)
    | _ -> assert false in
  (* Here we try to understand if the main pattern/term the user gave is
    * the first pattern to be matched (i.e. if elimty ends in P t1 .. tn,
    * wether tn is the t the user wrote in 'elim: t' *)
  let sigma, c_is_head_p = get_head_pattern env sigma elim_is_dep elim_args n_elim_args inf_deps_r cty in
  debug_ssr (fun () -> Pp.(str"c_is_head_p= " ++ bool c_is_head_p));
  let sigma, predty = Typing.type_of env sigma pred in
  (* Patterns for the inductive types indexes to be bound in pred are computed
   * looking at the ones provided by the user and the inferred ones looking at
   * the type of the elimination principle *)
  let sigma, patterns, clr = compute_patterns env sigma0 what c_is_head_p cty deps inf_deps_r occ orig_clr eqid sigma in
  let pp_pat (_,p,_,occ) = Pp.(pr_occ occ ++ pp_pattern env p) in
  let pp_inf_pat (_,_,t,_) = pr_econstr_pat env sigma (fire_subst sigma t) in
  debug_ssr (fun () -> Pp.(pp_concat (str"patterns=") (List.map pp_pat patterns)));
  debug_ssr (fun () -> Pp.(pp_concat (str"inf. patterns=") (List.map pp_inf_pat patterns)));
  (* Predicate generation, and (if necessary) tactic to generalize the
   * equation asked by the user *)
  let sigma, elim_pred, gen_eq_tac, clr =
    generate_pred env sigma0 ~concl patterns predty eqid is_rec deps elim_args n_elim_args c_is_head_p clr sigma
  in
  let sigma, pty = Typing.type_of env sigma elim_pred in
  let sigma = List.fold_left (fun sigma (_, arg, argty) -> Typing.check env sigma arg argty) sigma elim_args in
  debug_ssr (fun () -> Pp.(str"elim_pred=" ++ pr_econstr_env env sigma elim_pred));
  debug_ssr (fun () -> Pp.(str"elim_pred_ty=" ++ pr_econstr_env env sigma pty));
  let sigma = unify_HO env sigma pred elim_pred in
  let elim = fire_subst sigma elim in
  let sigma = resolve_typeclasses env sigma ~where:elim ~fail:false in
  (* check that the patterns do not contain non instantiated dependent metas *)
  let () = check_pattern_instantiated env sigma patterns in
  (* the elim tactic, with the eliminator and the predicated we computed *)
  let elim = sigma, elim in
  let seed =
    Array.map (fun ty ->
    let ctx,_ = EConstr.decompose_prod_decls sigma ty in
    CList.rev_map Context.Rel.Declaration.get_name ctx) seed in

  let elim_tac =
    Tacticals.tclTHENLIST [
      refine_with ~with_evars:false elim;
      cleartac clr] in
  Tacticals.tclTHENLIST [gen_eq_tac; elim_intro_tac ?seed:(Some seed) what eqid elim_tac is_rec clr]
  end

let elimtac x =
  let k ?seed:_ _what _eqid elim_tac _is_rec _clr = elim_tac in
  ssrelim ~is_case:false [] (EConstr ([],None,x)) None k

let casetac x k =
  let k ?seed _what _eqid elim_tac _is_rec _clr = k ?seed elim_tac in
  ssrelim ~is_case:true [] (EConstr ([],None,x)) None k

let rev_id = mk_internal_id "rev concl"
let injecteq_id = mk_internal_id "injection equation"

let revtoptac n0 =
  Proofview.Goal.enter begin fun gl ->
  let sigma = Proofview.Goal.sigma gl in
  let concl = Proofview.Goal.concl gl in
  let env = Proofview.Goal.env gl in
  let n = nb_prod sigma concl - n0 in
  let dc, cl = EConstr.decompose_prod_n_decls sigma n concl in
  let ty = EConstr.it_mkProd_or_LetIn cl (List.rev dc) in
  let dc' = dc @ [Context.Rel.Declaration.LocalAssum(make_annot (Name rev_id) EConstr.ERelevance.relevant, ty)] in
  Refine.refine ~typecheck:true begin fun sigma ->
    let f = EConstr.it_mkLambda_or_LetIn (mkEtaApp (EConstr.mkRel (n + 1)) (-n) 1) dc' in
    let sigma, ev = Evarutil.new_evar env sigma ty in
    sigma, (EConstr.mkApp (f, [|ev|]))
  end
  end

let nothing_to_inject =
   CWarnings.create ~name:"spurious-ssr-injection" ~category:CWarnings.CoreCategories.ssr
     (fun (sigma, env, ty) ->
         Pp.(str "SSReflect: cannot obtain new equations out of" ++ fnl() ++
             str"  " ++ Printer.pr_econstr_env env sigma ty ++ fnl() ++
             str "Did you write an extra [] in the intro pattern?"))

let equality_inj l b id c = Proofview.Goal.enter begin fun gl ->
  Proofview.tclORELSE (Equality.inj None ~injection_in_context:false l b None c)
    (function
    | (Equality.NothingToInject,_) ->
        let open Proofview.Notations in
        Ssrcommon.tacTYPEOF (EConstr.mkVar id) >>= fun ty ->
        nothing_to_inject (Proofview.Goal.sigma gl, Proofview.Goal.env gl, ty);
        discharge_hyp (id, (id, ""))
    | (e,info) -> Proofview.tclZERO ~info e)
  end

let injectidl2rtac id c =
  Proofview.Goal.enter begin fun gl ->
  let sigma = Proofview.Goal.sigma gl in
  let concl = Proofview.Goal.concl gl in
  Tacticals.tclTHEN (equality_inj None true id c) (revtoptac (nb_prod sigma concl))
  end

let injectl2rtac sigma c = match EConstr.kind sigma c with
| Var id -> injectidl2rtac id (EConstr.mkVar id, NoBindings)
| _ ->
  let id = injecteq_id in
  let xhavetac id c = Tactics.pose_proof (Name id) c in
  Tacticals.tclTHENLIST [xhavetac id c; injectidl2rtac id (EConstr.mkVar id, NoBindings); Tactics.clear [id]]

let is_injection_case env sigma c =
  let sigma, cty = Typing.type_of env sigma c in
  let (mind,_) = Tacred.eval_to_quantified_ind env sigma cty in
  Rocqlib.check_ref "core.eq.type" (GlobRef.IndRef mind)

let perform_injection c =
  let open Proofview.Notations in
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let sigma, cty = Typing.type_of env sigma c in
  let mind, t = Tacred.reduce_to_quantified_ind env sigma cty in
  let dc, eqt = EConstr.decompose_prod sigma t in
  if dc = [] then injectl2rtac sigma c else
  if not (EConstr.Vars.closed0 sigma eqt) then
    CErrors.user_err (Pp.str "can't decompose a quantified equality") else
  let cl = Proofview.Goal.concl gl in
  let n = List.length dc in
  let c_eq = mkEtaApp c n 2 in
  let cl1 = EConstr.mkLambda EConstr.(make_annot Anonymous ERelevance.relevant, mkArrow eqt ERelevance.relevant cl, mkApp (mkRel 1, [|c_eq|])) in
  let id = injecteq_id in
  let id_with_ebind = (EConstr.mkVar id, NoBindings) in
  let injtac = Tacticals.tclTHEN (introid id) (injectidl2rtac id id_with_ebind) in
  Proofview.Unsafe.tclEVARS sigma <*>
  Tacticals.tclTHENLAST (Tactics.apply (EConstr.it_mkLambda cl1 dc)) injtac
  end

let ssrscase_or_inj_tac c =
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  if is_injection_case env sigma c then perform_injection c
  else casetac c (fun ?seed:_ k -> k)
  end
