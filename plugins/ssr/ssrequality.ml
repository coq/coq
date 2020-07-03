(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* This file is (C) Copyright 2006-2015 Microsoft Corporation and Inria. *)

open Ltac_plugin
open Util
open Names
open Constr
open Context
open Vars
open Locus
open Printer
open Termops
open Tacinterp

open Ssrmatching_plugin
open Ssrmatching

open Ssrast
open Ssrprinters
open Ssrcommon
open Tacticals
open Tacmach

let ssroldreworder = Summary.ref ~name:"SSR:oldreworder" false
let () =
  Goptions.(declare_bool_option
    { optkey   = ["SsrOldRewriteGoalsOrder"];
      optread  = (fun _ -> !ssroldreworder);
      optdepr  = false;
      optwrite = (fun b -> ssroldreworder := b) })

(** The "simpl" tactic *)

(* We must avoid zeta-converting any "let"s created by the "in" tactical. *)

let tacred_simpl env =
  let simpl_expr =
    Genredexpr.(
      Simpl(Redops.make_red_flag[FBeta;FMatch;FZeta;FDeltaBut []],None)) in
  let esimpl, _ = Redexpr.reduction_of_red_expr env simpl_expr in
  let esimpl e sigma c =
    let (_,t) = esimpl e sigma c in
    t in
  let simpl env sigma c = (esimpl env sigma c) in
  simpl

let safe_simpltac n =
  if n = ~-1 then
    Proofview.Goal.enter begin fun gl ->
      let env = Proofview.Goal.env gl in
      let sigma = Proofview.Goal.sigma gl in
      let concl = Proofview.Goal.concl gl in
      let cl = red_safe (tacred_simpl env) env sigma concl in
      convert_concl_no_check cl
    end
  else
    ssr_n_tac "simpl" n

let simpltac = function
  | Simpl n -> safe_simpltac n
  | Cut n -> Tacticals.New.tclTRY (donetac n)
  | SimplCut (n,m) -> Tacticals.New.tclTHEN (safe_simpltac m) (Tacticals.New.tclTRY (donetac n))
  | Nop -> Tacticals.New.tclIDTAC

let simpltac s = Proofview.Goal.enter (fun _ -> simpltac s)

(** The "congr" tactic *)

let interp_congrarg_at ist gl n rf ty m =
  ppdebug(lazy Pp.(str"===interp_congrarg_at==="));
  let congrn, _ = mkSsrRRef "nary_congruence" in
  let args1 = mkRnat n :: mkRHoles n @ [ty] in
  let args2 = mkRHoles (3 * n) in
  let rec loop i =
    if i + n > m then None else
    try
      let rt = mkRApp congrn (args1 @  mkRApp rf (mkRHoles i) :: args2) in
      ppdebug(lazy Pp.(str"rt=" ++ Printer.pr_glob_constr_env (pf_env gl) rt));
      Some (interp_refine ist gl rt)
    with _ -> loop (i + 1) in
  loop 0

let pattern_id = mk_internal_id "pattern value"

let congrtac ((n, t), ty) ist gl =
  ppdebug(lazy (Pp.str"===congr==="));
  ppdebug(lazy Pp.(str"concl=" ++ Printer.pr_econstr_env (pf_env gl) (project gl) (Tacmach.pf_concl gl)));
  let sigma, _ as it = interp_term (pf_env gl) (project gl) ist t in
  let gl = pf_merge_uc_of sigma gl in
  let _, f, _, _ucst = pf_abs_evars gl it in
  let ist' = {ist with lfun =
    Id.Map.add pattern_id (Tacinterp.Value.of_constr f) Id.Map.empty } in
  let rf = mkRltacVar pattern_id in
  let m = pf_nbargs (pf_env gl) (project gl) f in
  let _, cf = if n > 0 then
    match interp_congrarg_at ist' gl n rf ty m with
    | Some cf -> cf
    | None -> errorstrm Pp.(str "No " ++ int n ++ str "-congruence with "
                         ++ pr_term t)
    else let rec loop i =
      if i > m then errorstrm Pp.(str "No congruence with " ++ pr_term t)
      else match interp_congrarg_at ist' gl i rf ty m with
      | Some cf -> cf
      | None -> loop (i + 1) in
      loop 1 in
  Proofview.V82.of_tactic Tacticals.New.(tclTHEN (refine_with cf) (tclTRY Tactics.reflexivity)) gl

let pf_typecheck t gl =
  let it = sig_it gl in
  let sigma,_  = pf_type_of gl t in
  re_sig [it] sigma

let newssrcongrtac arg ist =
  let open Proofview.Notations in
  Proofview.Goal.enter_one ~__LOC__ begin fun _g ->
    (Ssrcommon.tacMK_SSR_CONST "ssr_congr_arrow") end >>= fun arr ->
  Proofview.V82.tactic begin fun gl ->
  ppdebug(lazy Pp.(str"===newcongr==="));
  ppdebug(lazy Pp.(str"concl=" ++ Printer.pr_econstr_env (pf_env gl) (project gl) (pf_concl gl)));
  (* utils *)
  let fs gl t = Reductionops.nf_evar (project gl) t in
  let tclMATCH_GOAL (c, gl_c) proj t_ok t_fail gl =
    match try Some (pf_unify_HO gl_c (pf_concl gl) c)
          with exn when CErrors.noncritical exn -> None with
    | Some gl_c ->
        tclTHEN (Proofview.V82.of_tactic (convert_concl ~check:true (fs gl_c c)))
          (t_ok (proj gl_c)) gl
    | None -> t_fail () gl in
  let mk_evar gl ty =
    let env, sigma, si = pf_env gl, project gl, sig_it gl in
    let sigma = Evd.create_evar_defs sigma in
    let (sigma, x) = Evarutil.new_evar env sigma ty in
    x, re_sig si sigma in
  let ssr_congr lr = EConstr.mkApp (arr, lr) in
  let eq, gl = pf_fresh_global Coqlib.(lib_ref "core.eq.type") gl in
  (* here the two cases: simple equality or arrow *)
  let equality, _, eq_args, gl' = pf_saturate gl (EConstr.of_constr eq) 3 in
  tclMATCH_GOAL (equality, gl') (fun gl' -> fs gl' (List.assoc 0 eq_args))
  (fun ty -> congrtac (arg, Detyping.detype Detyping.Now false Id.Set.empty (pf_env gl) (project gl) ty) ist)
  (fun () ->
    let gl', t_lhs = pfe_new_type gl in
    let gl', t_rhs = pfe_new_type gl' in
    let lhs, gl' = mk_evar gl' t_lhs in
    let rhs, gl' = mk_evar gl' t_rhs in
    let arrow = EConstr.mkArrow lhs Sorts.Relevant (EConstr.Vars.lift 1 rhs) in
    tclMATCH_GOAL (arrow, gl') (fun gl' -> [|fs gl' lhs;fs gl' rhs|])
    (fun lr ->
      let a = ssr_congr lr in
      tclTHENLIST [ pf_typecheck a
                  ; Proofview.V82.of_tactic (Tactics.apply a)
                  ; congrtac (arg, mkRType) ist ])
    (fun _ _ -> errorstrm Pp.(str"Conclusion is not an equality nor an arrow")))
    gl
  end

(** 7. Rewriting tactics (rewrite, unlock) *)

(** Rewrite rules *)

type ssrwkind = RWred of ssrsimpl | RWdef | RWeq
type ssrrule = ssrwkind * ssrterm

(** Rewrite arguments *)

type ssrrwarg = (ssrdir * ssrmult) * ((ssrdocc * rpattern option) * ssrrule)

let notimes = 0
let nomult = 1, Once

let mkocc occ = None, occ
let noclr = mkocc None
let mkclr clr  = Some clr, None
let nodocc = mkclr []

let is_rw_cut = function RWred (Cut _) -> true | _ -> false

let mk_rwarg (d, (n, _ as m)) ((clr, occ as docc), rx) (rt, _ as r) : ssrrwarg =
 if rt <> RWeq then begin
   if rt = RWred Nop && not (m = nomult && occ = None && rx = None)
                     && (clr = None || clr = Some []) then
     anomaly "Improper rewrite clear switch";
   if d = R2L && rt <> RWdef then
     CErrors.user_err (Pp.str "Right-to-left switch on simplification");
   if n <> 1 && is_rw_cut rt then
     CErrors.user_err (Pp.str "Bad or useless multiplier");
   if occ <> None && rx = None && rt <> RWdef then
     CErrors.user_err (Pp.str "Missing redex for simplification occurrence")
 end; (d, m), ((docc, rx), r)

let norwmult = L2R, nomult
let norwocc = noclr, None

let simplintac occ rdx sim =
  let simptac m =
    Proofview.Goal.enter begin fun gl ->
    if m <> ~-1 then begin
      if rdx <> None then
        CErrors.user_err (Pp.str "Custom simpl tactic does not support patterns");
      if occ <> None then
        CErrors.user_err (Pp.str "Custom simpl tactic does not support occurrence numbers");
      simpltac (Simpl m)
    end else
      let sigma0, concl0, env0 = Proofview.Goal.(sigma gl, concl gl, env gl) in
      let simp env c _ _ = EConstr.Unsafe.to_constr (red_safe Tacred.simpl env sigma0 (EConstr.of_constr c)) in
      convert_concl_no_check (EConstr.of_constr (eval_pattern env0 sigma0 (EConstr.to_constr ~abort_on_undefined_evars:false sigma0 concl0) rdx occ simp))
    end
  in
  let open Tacticals.New in
  Proofview.Goal.enter begin fun _ ->
  match sim with
  | Simpl m -> simptac m
  | SimplCut (n,m) -> tclTHEN (simptac m) (tclTRY (donetac n))
  | _ -> simpltac sim
  end

let rec get_evalref env sigma c = match EConstr.kind sigma c with
  | Var (id, _) -> EvalVarRef id
  | Const ((k,_), _) -> EvalConstRef k
  | App (c', _) -> get_evalref env sigma c'
  | Cast (c', _, _) -> get_evalref env sigma c'
  | Proj(c,_) -> EvalConstRef(Projection.constant c)
  | _ -> errorstrm Pp.(str "The term " ++ pr_econstr_pat (Global.env ()) sigma c ++ str " is not unfoldable")

(* Strip a pattern generated by a prenex implicit to its constant. *)
let strip_unfold_term _ ((sigma, t) as p) kt = match EConstr.kind sigma t with
  | App (f, a) when kt = xNoFlag && Array.for_all (EConstr.isEvar sigma) a && EConstr.isConst sigma f ->
    (sigma, f), true
  | Const _ | Var _ -> p, true
  | Proj _ -> p, true
  | _ -> p, false

let same_proj sigma t1 t2 =
  match EConstr.kind sigma t1, EConstr.kind sigma t2 with
  | Proj(c1,_), Proj(c2, _) -> Projection.equal c1 c2
  | _ -> false

let all_ok _ _ = true

let fake_pmatcher_end () =
  mkProp, L2R, (Evd.empty, UState.empty, mkProp)

let unfoldintac occ rdx t (kt,_) =
  Proofview.V82.tactic begin fun gl ->
  let fs sigma x = Reductionops.nf_evar sigma x in
  let sigma0, concl0, env0 = project gl, pf_concl gl, pf_env gl in
  let (sigma, t), const = strip_unfold_term env0 t kt in
  let body env t c =
    Tacred.unfoldn [AllOccurrences, get_evalref env sigma t] env sigma0 c in
  let easy = occ = None && rdx = None in
  let red_flags = if easy then CClosure.betaiotazeta else CClosure.betaiota in
  let beta env = Reductionops.clos_norm_flags red_flags env sigma0 in
  let unfold, conclude = match rdx with
  | Some (_, (In_T _ | In_X_In_T _)) | None ->
    let ise = Evd.create_evar_defs sigma in
    let ise, u = mk_tpattern env0 sigma0 (ise,EConstr.Unsafe.to_constr t) all_ok L2R (EConstr.Unsafe.to_constr t) in
    let find_T, end_T =
      mk_tpattern_matcher ~raise_NoMatch:true sigma0 occ (ise,[u]) in
    (fun env c _ h ->
      try find_T env c h ~k:(fun env c _ _ -> EConstr.Unsafe.to_constr (body env t (EConstr.of_constr c)))
      with NoMatch when easy -> c
      | NoMatch | NoProgress -> errorstrm Pp.(str"No occurrence of "
        ++ pr_econstr_pat env sigma0 t ++ spc() ++ str "in " ++ Printer.pr_constr_env env sigma c)),
    (fun () -> try end_T () with
      | NoMatch when easy -> fake_pmatcher_end ()
      | NoMatch -> anomaly "unfoldintac")
  | _ ->
    (fun env (c as orig_c) _ h ->
      if const then
        let rec aux c =
          match EConstr.kind sigma0 c with
          | Const _ when EConstr.eq_constr sigma0 c t -> body env t t
          | App (f,a) when EConstr.eq_constr sigma0 f t -> EConstr.mkApp (body env f f,a)
          | Proj _ when same_proj sigma0 c t -> body env t c
          | _ ->
            let c = Reductionops.whd_betaiotazeta env sigma0 c in
            match EConstr.kind sigma0 c with
            | Const _ when EConstr.eq_constr sigma0 c t -> body env t t
            | App (f,a) when EConstr.eq_constr sigma0 f t -> EConstr.mkApp (body env f f,a)
            | Proj _ when same_proj sigma0 c t -> body env t c
            | Const (f, _) -> aux (body env c c)
            | App (f, a) -> aux (EConstr.mkApp (body env f f, a))
            | _ -> errorstrm Pp.(str "The term "++ pr_constr_env env sigma orig_c++
                str" contains no " ++ pr_econstr_env env sigma t ++ str" even after unfolding")
          in EConstr.Unsafe.to_constr @@ aux (EConstr.of_constr c)
      else
        try EConstr.Unsafe.to_constr @@ body env t (fs (unify_HO env sigma (EConstr.of_constr c) t) t)
        with _ -> errorstrm Pp.(str "The term " ++
          pr_constr_env env sigma c ++spc()++ str "does not unify with " ++ pr_econstr_pat env sigma t)),
    fake_pmatcher_end in
  let concl =
    let concl0 = EConstr.Unsafe.to_constr concl0 in
    try beta env0 (EConstr.of_constr (eval_pattern env0 sigma0 concl0 rdx occ unfold))
    with Option.IsNone -> errorstrm Pp.(str"Failed to unfold " ++ pr_econstr_pat env0 sigma t) in
  let _ = conclude () in
  Proofview.V82.of_tactic (convert_concl ~check:true concl) gl
  end

let foldtac occ rdx ft =
  Proofview.V82.tactic begin fun gl ->
  let sigma0, concl0, env0 = project gl, pf_concl gl, pf_env gl in
  let sigma, t = ft in
  let t = EConstr.to_constr ~abort_on_undefined_evars:false sigma t in
  let fold, conclude = match rdx with
  | Some (_, (In_T _ | In_X_In_T _)) | None ->
    let ise = Evd.create_evar_defs sigma in
    let ut = EConstr.Unsafe.to_constr (red_product_skip_id env0 sigma (EConstr.of_constr t)) in
    let ise, ut = mk_tpattern env0 sigma0 (ise,t) all_ok L2R ut in
    let find_T, end_T =
      mk_tpattern_matcher ~raise_NoMatch:true sigma0 occ (ise,[ut]) in
    (fun env c _ h -> try find_T env c h ~k:(fun env t _ _ -> t) with NoMatch ->c),
    (fun () -> try end_T () with NoMatch -> fake_pmatcher_end ())
  | _ ->
    (fun env c _ h ->
       try
         let sigma = unify_HO env sigma (EConstr.of_constr c) (EConstr.of_constr t) in
         EConstr.to_constr ~abort_on_undefined_evars:false sigma (EConstr.of_constr t)
    with _ -> errorstrm Pp.(str "fold pattern " ++ pr_constr_pat env sigma t ++ spc ()
      ++ str "does not match redex " ++ pr_constr_pat env sigma c)),
    fake_pmatcher_end in
  let concl0 = EConstr.Unsafe.to_constr concl0 in
  let concl = eval_pattern env0 sigma0 concl0 rdx occ fold in
  let _ = conclude () in
  Proofview.V82.of_tactic (convert_concl ~check:true (EConstr.of_constr concl)) gl
  end

let converse_dir = function L2R -> R2L | R2L -> L2R

let rw_progress rhs lhs ise = not (EConstr.eq_constr ise lhs (Evarutil.nf_evar ise rhs))

(* Coq has a more general form of "equation" (any type with a single *)
(* constructor with no arguments with_rect_r elimination lemmas).    *)
(* However there is no clear way of determining the LHS and RHS of   *)
(* such a generic Leibniz equation -- short of inspecting the type   *)
(* of the elimination lemmas.                                        *)

let rec strip_prod_assum c = match Constr.kind c with
  | Prod (_, _, c') -> strip_prod_assum c'
  | LetIn (_, v, _, c') -> strip_prod_assum (subst1 v c)
  | Cast (c', _, _) -> strip_prod_assum c'
  | _ -> c

let rule_id = mk_internal_id "rewrite rule"

exception PRtype_error of (Environ.env * Evd.evar_map * Pretype_errors.pretype_error) option

let id_map_redex _ sigma ~before:_ ~after = sigma, after

let pirrel_rewrite ?(under=false) ?(map_redex=id_map_redex) pred rdx rdx_ty new_rdx dir (sigma, c) c_ty =
  Proofview.V82.tactic begin fun gl ->
(*   ppdebug(lazy(str"sigma@pirrel_rewrite=" ++ pr_evar_map None sigma)); *)
  let env = pf_env gl in
  let beta = Reductionops.clos_norm_flags CClosure.beta env sigma in
  let sigma, new_rdx = map_redex env sigma ~before:rdx ~after:new_rdx in
  let sigma, p = (* The resulting goal *)
    Evarutil.new_evar env sigma (beta (EConstr.Vars.subst1 new_rdx pred)) in
  let pred = EConstr.mkNamedLambda (make_annot pattern_id Sorts.Relevant) rdx_ty pred in
  let sigma, elim =
    let sort = elimination_sort_of_goal gl in
    match Equality.eq_elimination_ref (dir = L2R) sort with
    | Some r -> Evd.fresh_global env sigma r
    | None ->
      let ((kn, i) as ind, _), unfolded_c_ty = Tacred.reduce_to_quantified_ind env sigma c_ty in
      let sort = elimination_sort_of_goal gl in
      let sigma, elim = Evd.fresh_global env sigma (Indrec.lookup_eliminator env ind sort) in
      if dir = R2L then sigma, elim else
      let elim, _ = EConstr.destConst sigma elim in
      let mp,l = Constant.repr2 (Constant.make1 (Constant.canonical elim)) in
      let l' = Label.of_id (Nameops.add_suffix (Label.to_id l) "_r")  in
      let c1' = Global.constant_of_delta_kn (Constant.canonical (Constant.make2 mp l')) in
      sigma, EConstr.of_constr (mkConst c1')
  in
  let proof = EConstr.mkApp (elim, [| rdx_ty; new_rdx; pred; p; rdx; c |]) in
  (* We check the proof is well typed *)
  let sigma, proof_ty =
    try Typing.type_of env sigma proof with
    | Pretype_errors.PretypeError (env, sigma, te) -> raise (PRtype_error (Some (env, sigma, te)))
    | e when CErrors.noncritical e -> raise (PRtype_error None)
  in
  ppdebug(lazy Pp.(str"pirrel_rewrite: proof term: " ++ pr_econstr_env env sigma proof));
  ppdebug(lazy Pp.(str"pirrel_rewrite of type: " ++ pr_econstr_env env sigma proof_ty));
  try Proofview.V82.of_tactic (refine_with
    ~first_goes_last:(not !ssroldreworder || under) ~with_evars:under (sigma, proof)) gl
  with e when CErrors.noncritical e ->
    (* we generate a msg like: "Unable to find an instance for the variable" *)
    let hd_ty, miss = match EConstr.kind sigma c with
    | App (hd, args) ->
        let hd_ty = Retyping.get_type_of env sigma hd in
        let names = let rec aux env t = function 0 -> [] | n ->
          let t = Reductionops.whd_all env sigma t in
          let open EConstr in
          match kind_of_type sigma t with
          | ProdType (name, ty, t) ->
              name.binder_name ::
                aux (EConstr.push_rel (Context.Rel.Declaration.LocalAssum (name,ty)) env) t (n-1)
          | _ ->
              (* In the case the head is an HO constant it may accept more arguments *)
              CList.init n (fun _ -> Names.Name.Anonymous) in aux env hd_ty (Array.length args) in
        hd_ty, Util.List.map_filter (fun (t, name) ->
          let evs = Evar.Set.elements (Evarutil.undefined_evars_of_term sigma t) in
          let open_evs = List.filter (fun k ->
            Sorts.InProp <> Retyping.get_sort_family_of
              env sigma (Evd.evar_concl (Evd.find sigma k)))
            evs in
          if open_evs <> [] then Some name else None)
          (List.combine (Array.to_list args) names)
    | _ -> anomaly "rewrite rule not an application" in
    errorstrm Pp.(Himsg.explain_refiner_error env sigma (Logic.UnresolvedBindings miss)++
      (Pp.fnl()++str"Rule's type:" ++ spc() ++ pr_econstr_env env sigma hd_ty))
  end

let pf_merge_uc_of s sigma =
  Evd.merge_universe_context sigma (Evd.evar_universe_context s)

let rwcltac ?under ?map_redex cl rdx dir sr =
  let open Proofview.Notations in
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma0 = Proofview.Goal.sigma gl in
  let sr =
    let sigma, r = sr in
    let sigma = resolve_typeclasses ~where:r ~fail:false env sigma in
    sigma, r in
  let n, r_n,_, ucst = abs_evars env sigma0 sr in
  let r_n' = abs_cterm env sigma0 n r_n in
  let r' = EConstr.Vars.subst_var pattern_id r_n' in
  let sigma0 = Evd.set_universe_context sigma0 ucst in
  let rdxt = Retyping.get_type_of env (fst sr) rdx in
(*         ppdebug(lazy(str"sigma@rwcltac=" ++ pr_evar_map None (fst sr))); *)
        ppdebug(lazy Pp.(str"r@rwcltac=" ++ pr_econstr_env env sigma0 (snd sr)));
  let cvtac, rwtac, sigma0 =
    if EConstr.Vars.closed0 sigma0 r' then
      let sigma, c, c_eq = fst sr, snd sr, Coqlib.(lib_ref "core.eq.type") in
      let sigma, c_ty = Typing.type_of env sigma c in
        ppdebug(lazy Pp.(str"c_ty@rwcltac=" ++ pr_econstr_env env sigma c_ty));
      let open EConstr in
      match kind_of_type sigma (Reductionops.whd_all env sigma c_ty) with
      | AtomicType(e, a) when Ssrcommon.is_ind_ref sigma e c_eq ->
          let new_rdx = if dir = L2R then a.(2) else a.(1) in
          pirrel_rewrite ?under ?map_redex cl rdx rdxt new_rdx dir (sigma,c) c_ty, Tacticals.New.tclIDTAC, sigma0
      | _ ->
          let cl' = EConstr.mkApp (EConstr.mkNamedLambda (make_annot pattern_id Sorts.Relevant) rdxt cl, [|rdx|]) in
          let sigma, _ = Typing.type_of env sigma cl' in
          let sigma0 = pf_merge_uc_of sigma sigma0 in
          convert_concl ~check:true cl', rewritetac ?under dir r', sigma0
    else
      let dc, r2 = EConstr.decompose_lam_n_assum sigma0 n r' in
      let r3, _, r3t  =
        try EConstr.destCast sigma0 r2 with _ ->
        errorstrm Pp.(str "no cast from " ++ pr_econstr_pat env sigma0 (snd sr)
                    ++ str " to " ++ pr_econstr_env env sigma0 r2) in
      let cl' = EConstr.mkNamedProd (make_annot rule_id Sorts.Relevant) (EConstr.it_mkProd_or_LetIn r3t dc) (EConstr.Vars.lift 1 cl) in
      let cl'' = EConstr.mkNamedProd (make_annot pattern_id Sorts.Relevant) rdxt cl' in
      let itacs = [introid pattern_id; introid rule_id] in
      let cltac = Tactics.clear [pattern_id; rule_id] in
      let rwtacs = [rewritetac ?under dir (EConstr.mkVar rule_id); cltac] in
      Tactics.apply_type ~typecheck:true cl'' [rdx; EConstr.it_mkLambda_or_LetIn r3 dc], Tacticals.New.tclTHENLIST (itacs @ rwtacs), sigma0
  in
  let cvtac' =
    Proofview.tclOR cvtac begin function
    | (PRtype_error e, _) ->
      let error = Option.cata (fun (env, sigma, te) ->
          Pp.(fnl () ++ str "Type error was: " ++ Himsg.explain_pretype_error env sigma te))
          (Pp.mt ()) e in
      if occur_existential sigma0 (Tacmach.New.pf_concl gl)
      then Tacticals.New.tclZEROMSG Pp.(str "Rewriting impacts evars" ++ error)
      else Tacticals.New.tclZEROMSG Pp.(str "Dependent type error in rewrite of "
        ++ pr_econstr_env env sigma0
          (EConstr.mkNamedLambda (make_annot pattern_id Sorts.Relevant) rdxt cl)
        ++ error)
    | (e, info) -> Proofview.tclZERO ~info e
    end
  in
  Proofview.Unsafe.tclEVARS sigma0 <*>
  Tacticals.New.tclTHEN cvtac' rwtac
  end

[@@@ocaml.warning "-3"]
let lz_coq_prod =
  let prod = lazy (Coqlib.build_prod ()) in fun () -> Lazy.force prod

let lz_setoid_relation =
  let sdir = ["Classes"; "RelationClasses"] in
  let last_srel = ref None in
  fun env -> match !last_srel with
  | Some (env', srel) when env' == env -> srel
  | _ ->
    let srel =
       try Some (UnivGen.constr_of_monomorphic_global @@
                 Coqlib.find_reference "Class_setoid" ("Coq"::sdir) "RewriteRelation" [@ocaml.warning "-3"])
       with _ -> None in
    last_srel := Some (env, srel); srel

let ssr_is_setoid env =
  match lz_setoid_relation env with
  | None -> fun _ _ _ -> false
  | Some srel ->
  fun sigma r args ->
    Rewrite.is_applied_rewrite_relation env
      sigma [] (EConstr.mkApp (r, args)) <> None

let closed0_check env sigma cl p =
  if closed0 cl then
    errorstrm Pp.(str"No occurrence of redex "++ pr_constr_env env sigma p)

let dir_org = function L2R -> 1 | R2L -> 2

let rwprocess_rule env dir rule =
  let coq_prod = lz_coq_prod () in
  let is_setoid = ssr_is_setoid env in
  let r_sigma, rules =
    let rec loop d sigma r t0 rs red =
      let t =
        if red = 1 then Tacred.hnf_constr env sigma t0
        else Reductionops.whd_betaiotazeta env sigma t0 in
      ppdebug(lazy Pp.(str"rewrule="++pr_econstr_pat env sigma t));
      match EConstr.kind sigma t with
      | Prod (_, xt, at) ->
        let sigma = Evd.create_evar_defs sigma in
        let (sigma, x) = Evarutil.new_evar env sigma xt in
        loop d sigma EConstr.(mkApp (r, [|x|])) (EConstr.Vars.subst1 x at) rs 0
      | App (pr, a) when is_ind_ref sigma pr coq_prod.Coqlib.typ ->
        let sr sigma = match EConstr.kind sigma (Tacred.hnf_constr env sigma r) with
        | App (c, ra) when is_construct_ref sigma c coq_prod.Coqlib.intro ->
          fun i -> ra.(i + 1), sigma
        | _ -> let ra = Array.append a [|r|] in
          function 1 ->
            let sigma, pi1 = Evd.fresh_global env sigma coq_prod.Coqlib.proj1 in
            EConstr.mkApp (pi1, ra), sigma
          | _ ->
            let sigma, pi2 = Evd.fresh_global env sigma coq_prod.Coqlib.proj2 in
            EConstr.mkApp (pi2, ra), sigma in
        let sigma,trty = Evd.fresh_global env sigma Coqlib.(lib_ref "core.True.type") in
        if EConstr.eq_constr sigma a.(0) trty then
         let s, sigma = sr sigma 2 in
         loop (converse_dir d) sigma s a.(1) rs 0
        else
         let s, sigma = sr sigma 2 in
         let sigma, rs2 = loop d sigma s a.(1) rs 0 in
         let s, sigma = sr sigma 1 in
         loop d sigma s a.(0) rs2 0
      | App (r_eq, a) when Hipattern.match_with_equality_type env sigma t != None ->
        let (ind, u) = EConstr.destInd sigma r_eq and rhs = Array.last a in
        let np = Inductiveops.inductive_nparamdecls env ind in
        let indu = (ind, EConstr.EInstance.kind sigma u) in
        let ind_ct = Inductiveops.type_of_constructors env indu in
        let lhs0 = last_arg sigma (EConstr.of_constr (strip_prod_assum ind_ct.(0))) in
        let rdesc = match EConstr.kind sigma lhs0 with
        | Rel (i, _) ->
          let lhs = a.(np - i) in
          let lhs, rhs = if d = L2R then lhs, rhs else rhs, lhs in
(* msgnl (str "RW: " ++ pr_rwdir d ++ str " " ++ pr_constr_pat r ++ str " : "
            ++ pr_constr_pat lhs ++ str " ~> " ++ pr_constr_pat rhs); *)
          d, r, lhs, rhs
(*
          let l_i, r_i = if d = L2R then i, 1 - ndep else 1 - ndep, i in
          let lhs = a.(np - l_i) and rhs = a.(np - r_i) in
          let a' = Array.copy a in let _ = a'.(np - l_i) <- mkVar pattern_id in
          let r' = mkCast (r, DEFAULTcast, mkApp (r_eq, a')) in
          (d, r', lhs, rhs)
*)
        | _ ->
          let lhs = EConstr.Vars.substl (array_list_of_tl (Array.sub a 0 np)) lhs0 in
          let lhs, rhs = if d = R2L then lhs, rhs else rhs, lhs in
          let d' = if Array.length a = 1 then d else converse_dir d in
          d', r, lhs, rhs in
        sigma, rdesc :: rs
      | App (s_eq, a) when is_setoid sigma s_eq a ->
        let np = Array.length a and i = 3 - dir_org d in
        let lhs = a.(np - i) and rhs = a.(np + i - 3) in
        let a' = Array.copy a in let _ = a'.(np - i) <- EConstr.mkVar pattern_id in
        let r' = EConstr.mkCast (r, DEFAULTcast, EConstr.mkApp (s_eq, a')) in
        sigma, (d, r', lhs, rhs) :: rs
      | _ ->
        if red = 0 then loop d sigma r t rs 1
        else errorstrm Pp.(str "not a rewritable relation: " ++ pr_econstr_pat env sigma t
                        ++ spc() ++ str "in rule " ++ pr_econstr_pat env sigma (snd rule))
        in
    let sigma, r = rule in
    let t = Retyping.get_type_of env sigma r in
    loop dir sigma r t [] 0
  in
    r_sigma, rules

let rwrxtac ?under ?map_redex occ rdx_pat dir rule =
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma0 = Proofview.Goal.sigma gl in
  let r_sigma, rules = rwprocess_rule env dir rule in
  let find_rule rdx =
    let rec rwtac = function
      | [] ->
        errorstrm Pp.(str "pattern " ++ pr_econstr_pat env sigma0 rdx ++
                   str " does not match " ++ pr_dir_side dir ++
                   str " of " ++ pr_econstr_pat env sigma0 (snd rule))
      | (d, r, lhs, rhs) :: rs ->
        try
          let ise = unify_HO env (Evd.create_evar_defs r_sigma) lhs rdx in
          if not (rw_progress rhs rdx ise) then raise NoMatch else
          d, (ise, Evd.evar_universe_context ise, Reductionops.nf_evar ise r)
        with _ -> rwtac rs in
     rwtac rules in
  let env0 = env in
  let concl0 = Proofview.Goal.concl gl in
  let find_R, conclude = match rdx_pat with
  | Some (_, (In_T _ | In_X_In_T _)) | None ->
      let upats_origin = dir, EConstr.Unsafe.to_constr (snd rule) in
      let rpat env sigma0 (sigma, pats) (d, r, lhs, rhs) =
        let sigma, pat =
          let rw_progress rhs t evd = rw_progress rhs (EConstr.of_constr t) evd in
          mk_tpattern env sigma0 (sigma, EConstr.to_constr ~abort_on_undefined_evars:false sigma r) (rw_progress rhs) d (EConstr.to_constr ~abort_on_undefined_evars:false sigma lhs) in
        sigma, pats @ [pat] in
      let rpats = List.fold_left (rpat env0 sigma0) (r_sigma,[]) rules in
      let find_R, end_R = mk_tpattern_matcher sigma0 occ ~upats_origin rpats in
      (fun e c _ i -> find_R ~k:(fun _ _ _ h -> mkRel h) e c i),
      fun cl -> let rdx,d,r = end_R () in closed0_check env0 sigma0 cl rdx; (d,r),rdx
  | Some(_, (T e | X_In_T (_,e) | E_As_X_In_T (e,_,_) | E_In_X_In_T (e,_,_))) ->
      let r = ref None in
      (fun env c _ h -> do_once r (fun () -> find_rule (EConstr.of_constr c), c); mkRel h),
      (fun concl -> closed0_check env0 sigma0 concl e;
        let (d,(ev,ctx,c)) , x = assert_done r in (d,(ev,ctx, EConstr.to_constr ~abort_on_undefined_evars:false ev c)) , x) in
  let concl0 = EConstr.to_constr ~abort_on_undefined_evars:false sigma0 concl0 in
  let concl = eval_pattern env0 sigma0 concl0 rdx_pat occ find_R in
  let (d, r), rdx = conclude concl in
  let r = Evd.merge_universe_context (pi1 r) (pi2 r), EConstr.of_constr (pi3 r) in
  rwcltac ?under ?map_redex (EConstr.of_constr concl) (EConstr.of_constr rdx) d r
  end

let ssrinstancesofrule ist dir arg =
  Proofview.Goal.enter begin fun gl ->
  let env0 = Proofview.Goal.env gl in
  let sigma0 = Proofview.Goal.sigma gl in
  let concl0 = Proofview.Goal.concl gl in
  let rule = interp_term env0 sigma0 ist arg in
  let r_sigma, rules = rwprocess_rule env0 dir rule in
  let find, conclude =
    let upats_origin = dir, EConstr.Unsafe.to_constr (snd rule) in
    let rpat env sigma0 (sigma, pats) (d, r, lhs, rhs) =
      let sigma, pat =
        let rw_progress rhs t evd = rw_progress rhs (EConstr.of_constr t) evd in
        mk_tpattern env sigma0
          (sigma,EConstr.to_constr ~abort_on_undefined_evars:false sigma r)
          (rw_progress rhs) d
          (EConstr.to_constr ~abort_on_undefined_evars:false sigma lhs) in
      sigma, pats @ [pat] in
    let rpats = List.fold_left (rpat env0 sigma0) (r_sigma,[]) rules in
    mk_tpattern_matcher ~all_instances:true ~raise_NoMatch:true sigma0 None ~upats_origin rpats in
  let print env p c _ = Feedback.msg_info Pp.(hov 1 (str"instance:" ++ spc() ++ pr_constr_env env r_sigma p ++ spc() ++ str "matches:" ++ spc() ++ pr_constr_env env r_sigma c)); c in
  Feedback.msg_info Pp.(str"BEGIN INSTANCES");
  try
    while true do
      ignore(find env0 (EConstr.to_constr ~abort_on_undefined_evars:false sigma0 concl0) 1 ~k:print)
    done; raise NoMatch
  with NoMatch -> Feedback.msg_info Pp.(str"END INSTANCES"); Tacticals.New.tclIDTAC
  end

let ipat_rewrite occ dir c = Proofview.Goal.enter begin fun gl ->
  rwrxtac occ None dir (Proofview.Goal.sigma gl, c)
end

let rwargtac ?under ?map_redex ist ((dir, mult), (((oclr, occ), grx), (kind, gt))) =
  let open Proofview.Notations in
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let fail = ref false in
  let interp_rpattern env sigma gc =
    try interp_rpattern env sigma gc
    with _ when snd mult = May -> fail := true; sigma, T mkProp in
  let interp env sigma gc =
    try interp_term env sigma ist gc
    with _ when snd mult = May -> fail := true; (sigma, EConstr.mkProp) in
  let rwtac =
    Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let rx = Option.map (interp_rpattern env sigma) grx in
    let sigma = match rx with
      | None -> sigma
      | Some (s,_) -> pf_merge_uc_of s sigma in
    let t = interp env sigma gt in
    let sigma = pf_merge_uc_of (fst t) sigma in
    Proofview.Unsafe.tclEVARS sigma <*>
    (match kind with
    | RWred sim -> simplintac occ rx sim
    | RWdef -> if dir = R2L then foldtac occ rx t else unfoldintac occ rx t gt
    | RWeq -> rwrxtac ?under ?map_redex occ rx dir t)
    end
  in
  let ctac = cleartac (interp_clr sigma (oclr, (fst gt, snd (interp env sigma gt)))) in
  if !fail then ctac else Tacticals.New.tclTHEN (tclMULT mult rwtac) ctac
  end

(** Rewrite argument sequence *)

(* type ssrrwargs = ssrrwarg list *)

(** The "rewrite" tactic *)

let ssrrewritetac ?under ?map_redex ist rwargs =
  Proofview.Goal.enter begin fun _ ->
  Tacticals.New.tclTHENLIST (List.map (rwargtac ?under ?map_redex ist) rwargs)
  end

(** The "unlock" tactic *)

let unfoldtac occ ko t kt =
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let concl = Proofview.Goal.concl gl in
  let concl = Evarutil.nf_evar sigma concl in
  let cl, c = fill_occ_term env sigma concl occ (fst (strip_unfold_term env t kt)) in
  let cl' = EConstr.Vars.subst1 (Tacred.unfoldn [OnlyOccurrences [1], get_evalref env sigma c] env sigma c) cl in
  let f = if ko = None then CClosure.betaiotazeta else CClosure.betaiota in
  convert_concl ~check:true (Reductionops.clos_norm_flags f env sigma cl')
  end

let unlocktac ist args =
  let open Proofview.Notations in
  let utac (occ, gt) =
    Proofview.Goal.enter begin fun gl ->
      let env = Proofview.Goal.env gl in
      let sigma = Proofview.Goal.sigma gl in
      unfoldtac occ occ (interp_term env sigma ist gt) (fst gt)
    end
  in
  Ssrcommon.tacMK_SSR_CONST "locked" >>= fun locked ->
  Ssrcommon.tacMK_SSR_CONST "master_key" >>= fun key ->
  let ktacs = [
    (Proofview.tclEVARMAP >>= fun sigma -> unfoldtac None None (sigma, locked) xInParens);
    Ssrelim.casetac key (fun ?seed:_ k -> k)
  ] in
  Tacticals.New.tclTHENLIST (List.map utac args @ ktacs)
