(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* This file is (C) Copyright 2006-2015 Microsoft Corporation and Inria. *)

open Util
open Names
open Printer
open Term
open Constr
open Termops
open Globnames
open Tactypes
open Tacmach

open Ssrmatching_plugin
open Ssrmatching

open Ssrast
open Ssrprinters
open Ssrcommon

module RelDecl = Context.Rel.Declaration

(** The "case" and "elim" tactic *)

(* TASSI: given the type of an elimination principle, it finds the higher order
 * argument (index), it computes it's arity and the arity of the eliminator and
 * checks if the eliminator is recursive or not *)
let analyze_eliminator elimty env sigma =
  let rec loop ctx t = match EConstr.kind_of_type sigma t with
  | AtomicType (hd, args) when EConstr.isRel sigma hd -> 
    ctx, EConstr.destRel sigma hd, not (EConstr.Vars.noccurn sigma 1 t), Array.length args, t
  | CastType (t, _) -> loop ctx t
  | ProdType (x, ty, t) -> loop (RelDecl.LocalAssum (x, ty) :: ctx) t
  | LetInType (x,b,ty,t) -> loop (RelDecl.LocalDef (x, b, ty) :: ctx) (EConstr.Vars.subst1 b t)
  | _ ->
    let env' = EConstr.push_rel_context ctx env in
    let t' = Reductionops.whd_all env' sigma t in
    if not (EConstr.eq_constr sigma t t') then loop ctx t' else
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
 * 4. build the tactic handle intructions and clears as required in ipats and
 *    by eqid *)
let ssrelim ?(ind=ref None) ?(is_case=false) deps what ?elim eqid elim_intro_tac gl =
  (* some sanity checks *)
  let oc, orig_clr, occ, c_gen, gl = match what with
  | `EConstr(_,_,t) when EConstr.isEvar (project gl) t ->
    anomaly "elim called on a constr evar"
  | `EGen (_, g) when elim = None && is_wildcard g ->
       errorstrm Pp.(str"Indeterminate pattern and no eliminator")
  | `EGen ((Some clr,occ), g) when is_wildcard g ->
       None, clr, occ, None, gl
  | `EGen ((None, occ), g) when is_wildcard g -> None,[],occ,None,gl
  | `EGen ((_, occ), p as gen) ->
       let _, c, clr,gl = pf_interp_gen gl true gen in
       Some c, clr, occ, Some p,gl
  | `EConstr (clr, occ, c) -> Some c, clr, occ, None,gl in
  let orig_gl, concl, env = gl, pf_concl gl, pf_env gl in
  ppdebug(lazy(Pp.str(if is_case then "==CASE==" else "==ELIM==")));
  let fire_subst gl t = Reductionops.nf_evar (project gl) t in
  let eq, gl = pf_fresh_global (Coqlib.build_coq_eq ()) gl in
  let eq = EConstr.of_constr eq in
  let is_undef_pat = function
  | sigma, T t -> EConstr.isEvar sigma (EConstr.of_constr t)
  | _ -> false in
  let match_pat env p occ h cl = 
    let sigma0 = project orig_gl in
    ppdebug(lazy Pp.(str"matching: " ++ pr_occ occ ++ pp_pattern p));
    let (c,ucst), cl =
      fill_occ_pattern ~raise_NoMatch:true env sigma0 (EConstr.Unsafe.to_constr cl) p occ h in
    ppdebug(lazy Pp.(str"     got: " ++ pr_constr_env env sigma0 c));
    c, EConstr.of_constr cl, ucst in
  let mkTpat gl t = (* takes a term, refreshes it and makes a T pattern *)
    let n, t, _, ucst = pf_abs_evars orig_gl (project gl, fire_subst gl t) in 
    let t, _, _, sigma = saturate ~beta:true env (project gl) t n in
    Evd.merge_universe_context sigma ucst, T (EConstr.Unsafe.to_constr t) in
  let unif_redex gl (sigma, r as p) t = (* t is a hint for the redex of p *)
    let n, t, _, ucst = pf_abs_evars orig_gl (project gl, fire_subst gl t) in 
    let t, _, _, sigma = saturate ~beta:true env sigma t n in
    let sigma = Evd.merge_universe_context sigma ucst in
    match r with
    | X_In_T (e, p) -> sigma, E_As_X_In_T (EConstr.Unsafe.to_constr t, e, p)
    | _ ->
       try unify_HO env sigma t (EConstr.of_constr (fst (redex_of_pattern env p))), r
       with e when CErrors.noncritical e -> p in
  (* finds the eliminator applies it to evars and c saturated as needed  *)
  (* obtaining "elim ??? (c ???)". pred is the higher order evar         *)
  (* cty is None when the user writes _ (hence we can't make a pattern *)
  let cty, elim, elimty, elim_args, n_elim_args, elim_is_dep, is_rec, pred, gl =
    match elim with
    | Some elim ->
      let gl, elimty = pf_e_type_of gl elim in
      let pred_id, n_elim_args, is_rec, elim_is_dep, n_pred_args,ctx_concl =
        analyze_eliminator elimty env (project gl) in
      ind := Some (0, subgoals_tys (project gl) ctx_concl);
      let elim, elimty, elim_args, gl =
        pf_saturate ~beta:is_case gl elim ~ty:elimty n_elim_args in
      let pred = List.assoc pred_id elim_args in
      let elimty = Reductionops.whd_all env (project gl) elimty in
      let cty, gl =
        if Option.is_empty oc then None, gl
        else
          let c = Option.get oc in let gl, c_ty = pfe_type_of gl c in
          let pc = match c_gen with
            | Some p -> interp_cpattern orig_gl p None
            | _ -> mkTpat gl c in
          Some(c, c_ty, pc), gl in
      cty, elim, elimty, elim_args, n_elim_args, elim_is_dep, is_rec, pred, gl
    | None ->
      let c = Option.get oc in let gl, c_ty = pfe_type_of gl c in
      let ((kn, i),_ as indu), unfolded_c_ty =
        pf_reduce_to_quantified_ind gl c_ty in
      let sort = Tacticals.elimination_sort_of_goal gl in
      let gl, elim =
        if not is_case then
          let t,gl= pf_fresh_global (Indrec.lookup_eliminator (kn,i) sort) gl in
          gl, t
        else
          Tacmach.pf_eapply (fun env sigma () ->
            let indu = (fst indu, EConstr.EInstance.kind sigma (snd indu)) in
            let (sigma, ind) = Indrec.build_case_analysis_scheme env sigma indu true sort in
            (sigma, ind)) gl () in
      let elim = EConstr.of_constr elim in
      let gl, elimty = pfe_type_of gl elim in
      let pred_id,n_elim_args,is_rec,elim_is_dep,n_pred_args,ctx_concl =
        analyze_eliminator elimty env (project gl) in
      if is_case then
       let mind,indb = Inductive.lookup_mind_specif env (kn,i) in
       ind := Some(mind.Declarations.mind_nparams,Array.map EConstr.of_constr indb.Declarations.mind_nf_lc);
      else
       ind := Some (0, subgoals_tys (project gl) ctx_concl);
      let rctx = fst (EConstr.decompose_prod_assum (project gl) unfolded_c_ty) in
      let n_c_args = Context.Rel.length rctx in
      let c, c_ty, t_args, gl = pf_saturate gl c ~ty:c_ty n_c_args in
      let elim, elimty, elim_args, gl =
        pf_saturate ~beta:is_case gl elim ~ty:elimty n_elim_args in
      let pred = List.assoc pred_id elim_args in
      let pc = match n_c_args, c_gen with
        | 0, Some p -> interp_cpattern orig_gl p None
        | _ -> mkTpat gl c in
      let cty = Some (c, c_ty, pc) in
      let elimty = Reductionops.whd_all env (project gl) elimty in
      cty, elim, elimty, elim_args, n_elim_args, elim_is_dep, is_rec, pred, gl
  in
  ppdebug(lazy Pp.(str"elim= "++ pr_constr_pat (EConstr.Unsafe.to_constr elim)));
  ppdebug(lazy Pp.(str"elimty= "++ pr_constr_pat (EConstr.Unsafe.to_constr elimty)));
  let inf_deps_r = match EConstr.kind_of_type (project gl) elimty with
    | AtomicType (_, args) -> List.rev (Array.to_list args)
    | _ -> assert false in
  let saturate_until gl c c_ty f =
    let rec loop n = try
      let c, c_ty, _, gl = pf_saturate gl c ~ty:c_ty n in
      let gl' = f c c_ty gl in
      Some (c, c_ty, gl, gl')
    with
    | NotEnoughProducts -> None
    | e when CErrors.noncritical e -> loop (n+1) in loop 0 in
  (* Here we try to understand if the main pattern/term the user gave is
   * the first pattern to be matched (i.e. if elimty ends in P t1 .. tn,
   * weather tn is the t the user wrote in 'elim: t' *)
  let c_is_head_p, gl = match cty with
    | None -> true, gl  (* The user wrote elim: _ *)
    | Some (c, c_ty, _) ->
    let res = 
      (* we try to see if c unifies with the last arg of elim *)
      if elim_is_dep then None else
      let arg = List.assoc (n_elim_args - 1) elim_args in
      let gl, arg_ty = pfe_type_of gl arg in
      match saturate_until gl c c_ty (fun c c_ty gl ->
        pf_unify_HO (pf_unify_HO gl c_ty arg_ty) arg c) with
      | Some (c, _, _, gl) -> Some (false, gl)
      | None -> None in
    match res with
    | Some x -> x
    | None ->
      (* we try to see if c unifies with the last inferred pattern *)
      let inf_arg = List.hd inf_deps_r in
      let gl, inf_arg_ty = pfe_type_of gl inf_arg in
      match saturate_until gl c c_ty (fun _ c_ty gl ->
              pf_unify_HO gl c_ty inf_arg_ty) with
      | Some (c, _, _,gl) -> true, gl
      | None ->
        errorstrm Pp.(str"Unable to apply the eliminator to the term"++
          spc()++pr_econstr_env env (project gl) c++spc()++str"or to unify it's type with"++
          pr_econstr_env env (project gl) inf_arg_ty) in
  ppdebug(lazy Pp.(str"c_is_head_p= " ++ bool c_is_head_p));
  let gl, predty = pfe_type_of gl pred in
  (* Patterns for the inductive types indexes to be bound in pred are computed
   * looking at the ones provided by the user and the inferred ones looking at
   * the type of the elimination principle *)
  let pp_pat (_,p,_,occ) = Pp.(pr_occ occ ++ pp_pattern p) in
  let pp_inf_pat gl (_,_,t,_) = pr_constr_pat (EConstr.Unsafe.to_constr (fire_subst gl t)) in
  let patterns, clr, gl =
    let rec loop patterns clr i = function
      | [],[] -> patterns, clr, gl
      | ((oclr, occ), t):: deps, inf_t :: inf_deps ->
          let p = interp_cpattern orig_gl t None in
          let clr_t =
            interp_clr (project gl) (oclr,(tag_of_cpattern t,EConstr.of_constr (fst (redex_of_pattern env p)))) in
          (* if we are the index for the equation we do not clear *)
          let clr_t = if deps = [] && eqid <> None then [] else clr_t in
          let p = if is_undef_pat p then mkTpat gl inf_t else p in
          loop (patterns @ [i, p, inf_t, occ]) 
            (clr_t @ clr) (i+1) (deps, inf_deps)
      | [], c :: inf_deps -> 
          ppdebug(lazy Pp.(str"adding inf pattern " ++ pr_constr_pat (EConstr.Unsafe.to_constr c)));
          loop (patterns @ [i, mkTpat gl c, c, allocc]) 
            clr (i+1) ([], inf_deps)
      | _::_, [] -> errorstrm Pp.(str "Too many dependent abstractions") in
    let deps, head_p, inf_deps_r = match what, c_is_head_p, cty with
    | `EConstr _, _, None -> anomaly "Simple elim with no term"
    | _, false, _ -> deps, [], inf_deps_r
    | `EGen gen, true, None -> deps @ [gen], [], inf_deps_r
    | _, true, Some (c, _, pc) ->
         let occ = if occ = None then allocc else occ in
         let inf_p, inf_deps_r = List.hd inf_deps_r, List.tl inf_deps_r in
         deps, [1, pc, inf_p, occ], inf_deps_r in
    let patterns, clr, gl = 
      loop [] orig_clr (List.length head_p+1) (List.rev deps, inf_deps_r) in
    head_p @ patterns, Util.List.uniquize clr, gl
  in
  ppdebug(lazy Pp.(pp_concat (str"patterns=") (List.map pp_pat patterns)));
  ppdebug(lazy Pp.(pp_concat (str"inf. patterns=") (List.map (pp_inf_pat gl) patterns)));
  (* Predicate generation, and (if necessary) tactic to generalize the
   * equation asked by the user *)
  let elim_pred, gen_eq_tac, clr, gl = 
    let error gl t inf_t = errorstrm Pp.(str"The given pattern matches the term"++
      spc()++pp_term gl t++spc()++str"while the inferred pattern"++
      spc()++pr_constr_pat (EConstr.Unsafe.to_constr (fire_subst gl inf_t))++spc()++ str"doesn't") in
    let match_or_postpone (cl, gl, post) (h, p, inf_t, occ) =
      let p = unif_redex gl p inf_t in
      if is_undef_pat p then
        let () = ppdebug(lazy Pp.(str"postponing " ++ pp_pattern p)) in
        cl, gl, post @ [h, p, inf_t, occ]
      else try
        let c, cl, ucst = match_pat env p occ h cl in
        let gl = pf_merge_uc ucst gl in
        let c = EConstr.of_constr c in
        let gl = try pf_unify_HO gl inf_t c
                 with exn when CErrors.noncritical exn -> error gl c inf_t in
        cl, gl, post
      with 
      | NoMatch | NoProgress ->
          let e, ucst = redex_of_pattern env p in
          let gl = pf_merge_uc ucst gl in
          let e = EConstr.of_constr e in
          let n, e, _, _ucst =  pf_abs_evars gl (fst p, e) in
          let e, _, _, gl = pf_saturate ~beta:true gl e n in 
          let gl = try pf_unify_HO gl inf_t e
                   with exn when CErrors.noncritical exn -> error gl e inf_t in
          cl, gl, post
    in        
    let rec match_all concl gl patterns =
      let concl, gl, postponed = 
        List.fold_left match_or_postpone (concl, gl, []) patterns in
      if postponed = [] then concl, gl
      else if List.length postponed = List.length patterns then
        errorstrm Pp.(str "Some patterns are undefined even after all"++spc()++
          str"the defined ones matched")
      else match_all concl gl postponed in
    let concl, gl = match_all concl gl patterns in
    let pred_rctx, _ = EConstr.decompose_prod_assum (project gl) (fire_subst gl predty) in
    let concl, gen_eq_tac, clr, gl = match eqid with 
    | Some (IPatId _) when not is_rec -> 
        let k = List.length deps in
        let c = fire_subst gl (List.assoc (n_elim_args - k - 1) elim_args) in
        let gl, t = pfe_type_of gl c in
        let gen_eq_tac, gl =
          let refl = EConstr.mkApp (eq, [|t; c; c|]) in
          let new_concl = EConstr.mkArrow refl (EConstr.Vars.lift 1 (pf_concl orig_gl)) in 
          let new_concl = fire_subst gl new_concl in
          let erefl, gl = mkRefl t c gl in
          let erefl = fire_subst gl erefl in
          apply_type new_concl [erefl], gl in
        let rel = k + if c_is_head_p then 1 else 0 in
        let src, gl = mkProt EConstr.mkProp EConstr.(mkApp (eq,[|t; c; mkRel rel|])) gl in
        let concl = EConstr.mkArrow src (EConstr.Vars.lift 1 concl) in
        let clr = if deps <> [] then clr else [] in
        concl, gen_eq_tac, clr, gl
    | _ -> concl, Tacticals.tclIDTAC, clr, gl in
    let mk_lam t r = EConstr.mkLambda_or_LetIn r t in
    let concl = List.fold_left mk_lam concl pred_rctx in
    let gl, concl = 
      if eqid <> None && is_rec then
        let gl, concls = pfe_type_of gl concl in
        let concl, gl = mkProt concls concl gl in
        let gl, _ = pfe_type_of gl concl in
        gl, concl
      else gl, concl in
    concl, gen_eq_tac, clr, gl in
  let gl, pty = pf_e_type_of gl elim_pred in
  ppdebug(lazy Pp.(str"elim_pred=" ++ pp_term gl elim_pred));
  ppdebug(lazy Pp.(str"elim_pred_ty=" ++ pp_term gl pty));
  let gl = pf_unify_HO gl pred elim_pred in
  let elim = fire_subst gl elim in
  let gl, _ = pf_e_type_of gl elim in
  (* check that the patterns do not contain non instantiated dependent metas *)
  let () = 
    let evars_of_term = Evarutil.undefined_evars_of_term (project gl) in
    let patterns = List.map (fun (_,_,t,_) -> fire_subst gl t) patterns in
    let patterns_ev = List.map evars_of_term patterns in 
    let ev = List.fold_left Evar.Set.union Evar.Set.empty patterns_ev in
    let ty_ev = Evar.Set.fold (fun i e ->
         let ex = i in
         let i_ty = Evd.evar_concl (Evd.find (project gl) ex) in
         Evar.Set.union e (evars_of_term i_ty))
      ev Evar.Set.empty in
    let inter = Evar.Set.inter ev ty_ev in
    if not (Evar.Set.is_empty inter) then begin
      let i = Evar.Set.choose inter in
      let pat = List.find (fun t -> Evar.Set.mem i (evars_of_term t)) patterns in
      errorstrm Pp.(str"Pattern"++spc()++pr_constr_pat (EConstr.Unsafe.to_constr pat)++spc()++
        str"was not completely instantiated and one of its variables"++spc()++
        str"occurs in the type of another non-instantiated pattern variable");
    end
  in
  (* the elim tactic, with the eliminator and the predicated we computed *)
  let elim = project gl, elim in 
  let elim_tac gl =
    Tacticals.tclTHENLIST [refine_with ~with_evars:false elim; old_cleartac clr] gl in
  Tacticals.tclTHENLIST [gen_eq_tac; elim_intro_tac what eqid elim_tac is_rec clr] orig_gl

let no_intro ?ist what eqid elim_tac is_rec clr = elim_tac

let elimtac x =
  Proofview.V82.tactic ~nf_evars:false
    (ssrelim ~is_case:false [] (`EConstr ([],None,x)) None no_intro)
let casetac x = ssrelim ~is_case:true [] (`EConstr ([],None,x)) None no_intro

let pf_nb_prod gl = nb_prod (project gl) (pf_concl gl)

let rev_id = mk_internal_id "rev concl"
let injecteq_id = mk_internal_id "injection equation"

let revtoptac n0 gl =
  let n = pf_nb_prod gl - n0 in
  let dc, cl = EConstr.decompose_prod_n_assum (project gl) n (pf_concl gl) in
  let dc' = dc @ [Context.Rel.Declaration.LocalAssum(Name rev_id, EConstr.it_mkProd_or_LetIn cl (List.rev dc))] in
  let f = EConstr.it_mkLambda_or_LetIn (mkEtaApp (EConstr.mkRel (n + 1)) (-n) 1) dc' in
  refine (EConstr.mkApp (f, [|Evarutil.mk_new_meta ()|])) gl

let equality_inj l b id c gl =
  let msg = ref "" in
  try Proofview.V82.of_tactic (Equality.inj None l b None c) gl
  with
    | Ploc.Exc(_,CErrors.UserError (_,s))
    | CErrors.UserError (_,s)
  when msg := Pp.string_of_ppcmds s;
       !msg = "Not a projectable equality but a discriminable one." ||
       !msg = "Nothing to inject." ->
    Feedback.msg_warning (Pp.str !msg);
    discharge_hyp (id, (id, "")) gl

let injectidl2rtac id c gl =
  Tacticals.tclTHEN (equality_inj None true id c) (revtoptac (pf_nb_prod gl)) gl

let injectl2rtac sigma c = match EConstr.kind sigma c with
| Var id -> injectidl2rtac id (EConstr.mkVar id, NoBindings)
| _ ->
  let id = injecteq_id in
  let xhavetac id c = Proofview.V82.of_tactic (Tactics.pose_proof (Name id) c) in
  Tacticals.tclTHENLIST [xhavetac id c; injectidl2rtac id (EConstr.mkVar id, NoBindings); Proofview.V82.of_tactic (Tactics.clear [id])]

let is_injection_case c gl =
  let gl, cty = pfe_type_of gl c in
  let (mind,_), _ = pf_reduce_to_quantified_ind gl cty in
  GlobRef.equal (IndRef mind) (Coqlib.build_coq_eq ())

let perform_injection c gl =
  let gl, cty = pfe_type_of gl c in
  let mind, t = pf_reduce_to_quantified_ind gl cty in
  let dc, eqt = EConstr.decompose_prod (project gl) t in
  if dc = [] then injectl2rtac (project gl) c gl else
  if not (EConstr.Vars.closed0 (project gl) eqt) then
    CErrors.user_err (Pp.str "can't decompose a quantified equality") else
  let cl = pf_concl gl in let n = List.length dc in
  let c_eq = mkEtaApp c n 2 in
  let cl1 = EConstr.mkLambda EConstr.(Anonymous, mkArrow eqt cl, mkApp (mkRel 1, [|c_eq|])) in
  let id = injecteq_id in
  let id_with_ebind = (EConstr.mkVar id, NoBindings) in
  let injtac = Tacticals.tclTHEN (introid id) (injectidl2rtac id id_with_ebind) in 
  Tacticals.tclTHENLAST (Proofview.V82.of_tactic (Tactics.apply (EConstr.compose_lam dc cl1))) injtac gl

let ssrscase_or_inj_tac c = Proofview.V82.tactic ~nf_evars:false (fun gl ->
  if is_injection_case c gl then perform_injection c gl
  else casetac c gl)

let ssrscasetac c =
  Proofview.V82.tactic ~nf_evars:false (fun gl -> casetac c gl)
