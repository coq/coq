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

open Ltac_plugin
open Util
open Names
open Term
open Constr
open Vars
open Locus
open Printer
open Globnames
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
let _ =
  Goptions.declare_bool_option
    { Goptions.optname  = "ssreflect 1.3 compatibility flag";
      Goptions.optkey   = ["SsrOldRewriteGoalsOrder"];
      Goptions.optread  = (fun _ -> !ssroldreworder);
      Goptions.optdepr  = false;
      Goptions.optwrite = (fun b -> ssroldreworder := b) }

(** The "simpl" tactic *)

(* We must avoid zeta-converting any "let"s created by the "in" tactical. *)

let tacred_simpl gl =
  let simpl_expr =
    Genredexpr.(
      Simpl(Redops.make_red_flag[FBeta;FMatch;FZeta;FDeltaBut []],None)) in
  let esimpl, _ = Redexpr.reduction_of_red_expr (pf_env gl) simpl_expr in
  let esimpl e sigma c =
    let (_,t) = esimpl e sigma c in
    t in
  let simpl env sigma c = (esimpl env sigma c) in
  simpl

let safe_simpltac n gl =
  if n = ~-1 then
    let cl= red_safe (tacred_simpl gl) (pf_env gl) (project gl) (pf_concl gl) in
    Proofview.V82.of_tactic (convert_concl_no_check cl) gl
  else
    ssr_n_tac "simpl" n gl

let simpltac = function
  | Simpl n -> safe_simpltac n
  | Cut n -> tclTRY (donetac n)
  | SimplCut (n,m) -> tclTHEN (safe_simpltac m) (tclTRY (donetac n))
  | Nop -> tclIDTAC

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
  let sigma, _ as it = interp_term ist gl t in
  let gl = pf_merge_uc_of sigma gl in
  let _, f, _, _ucst = pf_abs_evars gl it in
  let ist' = {ist with lfun =
    Id.Map.add pattern_id (Tacinterp.Value.of_constr f) Id.Map.empty } in
  let rf = mkRltacVar pattern_id in
  let m = pf_nbargs gl f in
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
  tclTHEN (refine_with cf) (tclTRY (Proofview.V82.of_tactic Tactics.reflexivity)) gl

let newssrcongrtac arg ist gl =
  ppdebug(lazy Pp.(str"===newcongr==="));
  ppdebug(lazy Pp.(str"concl=" ++ Printer.pr_econstr_env (pf_env gl) (project gl) (pf_concl gl)));
  (* utils *)
  let fs gl t = Reductionops.nf_evar (project gl) t in
  let tclMATCH_GOAL (c, gl_c) proj t_ok t_fail gl =
    match try Some (pf_unify_HO gl_c (pf_concl gl) c)
          with exn when CErrors.noncritical exn -> None with
    | Some gl_c ->
        tclTHEN (Proofview.V82.of_tactic (convert_concl (fs gl_c c)))
          (t_ok (proj gl_c)) gl
    | None -> t_fail () gl in 
  let mk_evar gl ty = 
    let env, sigma, si = pf_env gl, project gl, sig_it gl in
    let sigma = Evd.create_evar_defs sigma in
    let (sigma, x) = Evarutil.new_evar env sigma ty in
    x, re_sig si sigma in
  let arr, gl = pf_mkSsrConst "ssr_congr_arrow" gl in
  let ssr_congr lr = EConstr.mkApp (arr, lr) in
  (* here thw two cases: simple equality or arrow *)
  let equality, _, eq_args, gl' =
    let eq, gl = pf_fresh_global (Coqlib.build_coq_eq ()) gl in
    pf_saturate gl (EConstr.of_constr eq) 3 in
  tclMATCH_GOAL (equality, gl') (fun gl' -> fs gl' (List.assoc 0 eq_args))
  (fun ty -> congrtac (arg, Detyping.detype Detyping.Now false Id.Set.empty (pf_env gl) (project gl) ty) ist)
  (fun () ->
    let lhs, gl' = mk_evar gl EConstr.mkProp in let rhs, gl' = mk_evar gl' EConstr.mkProp in
    let arrow = EConstr.mkArrow lhs (EConstr.Vars.lift 1 rhs) in
    tclMATCH_GOAL (arrow, gl') (fun gl' -> [|fs gl' lhs;fs gl' rhs|])
    (fun lr -> tclTHEN (Proofview.V82.of_tactic (Tactics.apply (ssr_congr lr))) (congrtac (arg, mkRType) ist))
    (fun _ _ -> errorstrm Pp.(str"Conclusion is not an equality nor an arrow")))
    gl

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

let simplintac occ rdx sim gl = 
  let simptac m gl =
    if m <> ~-1 then
      CErrors.user_err (Pp.str "Localized custom simpl tactic not supported");
    let sigma0, concl0, env0 = project gl, pf_concl gl, pf_env gl in
    let simp env c _ _ = EConstr.Unsafe.to_constr (red_safe Tacred.simpl env sigma0 (EConstr.of_constr c)) in
    Proofview.V82.of_tactic
      (convert_concl_no_check (EConstr.of_constr (eval_pattern env0 sigma0 (EConstr.Unsafe.to_constr concl0) rdx occ simp)))
      gl in
  match sim with
  | Simpl m -> simptac m gl
  | SimplCut (n,m) -> tclTHEN (simptac m) (tclTRY (donetac n)) gl
  | _ -> simpltac sim gl

let rec get_evalref sigma c = match EConstr.kind sigma c with
  | Var id -> EvalVarRef id
  | Const (k,_) -> EvalConstRef k
  | App (c', _) -> get_evalref sigma c'
  | Cast (c', _, _) -> get_evalref sigma c'
  | Proj(c,_) -> EvalConstRef(Projection.constant c)
  | _ -> errorstrm Pp.(str "The term " ++ pr_constr_pat (EConstr.Unsafe.to_constr c) ++ str " is not unfoldable")

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

let unfoldintac occ rdx t (kt,_) gl = 
  let fs sigma x = Reductionops.nf_evar sigma x in
  let sigma0, concl0, env0 = project gl, pf_concl gl, pf_env gl in
  let (sigma, t), const = strip_unfold_term env0 t kt in
  let body env t c =
    Tacred.unfoldn [AllOccurrences, get_evalref sigma t] env sigma0 c in
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
        ++ pr_constr_pat (EConstr.Unsafe.to_constr t) ++ spc() ++ str "in " ++ Printer.pr_constr_env env sigma c)),
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
            let c = Reductionops.whd_betaiotazeta sigma0 c in
            match EConstr.kind sigma0 c with
            | Const _ when EConstr.eq_constr sigma0 c t -> body env t t
            | App (f,a) when EConstr.eq_constr sigma0 f t -> EConstr.mkApp (body env f f,a)
            | Proj _ when same_proj sigma0 c t -> body env t c
            | Const f -> aux (body env c c)
            | App (f, a) -> aux (EConstr.mkApp (body env f f, a))
            | _ -> errorstrm Pp.(str "The term "++ pr_constr_env env sigma orig_c++
                str" contains no " ++ pr_econstr_env env sigma t ++ str" even after unfolding")
          in EConstr.Unsafe.to_constr @@ aux (EConstr.of_constr c)
      else
        try EConstr.Unsafe.to_constr @@ body env t (fs (unify_HO env sigma (EConstr.of_constr c) t) t)
        with _ -> errorstrm Pp.(str "The term " ++
          pr_constr_env env sigma c ++spc()++ str "does not unify with " ++ pr_constr_pat (EConstr.Unsafe.to_constr t))),
    fake_pmatcher_end in
  let concl = 
    let concl0 = EConstr.Unsafe.to_constr concl0 in
    try beta env0 (EConstr.of_constr (eval_pattern env0 sigma0 concl0 rdx occ unfold)) 
    with Option.IsNone -> errorstrm Pp.(str"Failed to unfold " ++ pr_constr_pat (EConstr.Unsafe.to_constr t)) in
  let _ = conclude () in
  Proofview.V82.of_tactic (convert_concl concl) gl
;;

let foldtac occ rdx ft gl = 
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
    with _ -> errorstrm Pp.(str "fold pattern " ++ pr_constr_pat t ++ spc ()
      ++ str "does not match redex " ++ pr_constr_pat c)), 
    fake_pmatcher_end in
  let concl0 = EConstr.Unsafe.to_constr concl0 in
  let concl = eval_pattern env0 sigma0 concl0 rdx occ fold in
  let _ = conclude () in
  Proofview.V82.of_tactic (convert_concl (EConstr.of_constr concl)) gl
;;

let converse_dir = function L2R -> R2L | R2L -> L2R

let rw_progress rhs lhs ise = not (EConstr.eq_constr ise lhs (Evarutil.nf_evar ise rhs))

(* Coq has a more general form of "equation" (any type with a single *)
(* constructor with no arguments with_rect_r elimination lemmas).    *)
(* However there is no clear way of determining the LHS and RHS of   *)
(* such a generic Leibnitz equation -- short of inspecting the type  *)
(* of the elimination lemmas.                                        *)

let rec strip_prod_assum c = match Constr.kind c with
  | Prod (_, _, c') -> strip_prod_assum c'
  | LetIn (_, v, _, c') -> strip_prod_assum (subst1 v c)
  | Cast (c', _, _) -> strip_prod_assum c'
  | _ -> c

let rule_id = mk_internal_id "rewrite rule"

exception PRtype_error

let pirrel_rewrite pred rdx rdx_ty new_rdx dir (sigma, c) c_ty gl =
(*   ppdebug(lazy(str"sigma@pirrel_rewrite=" ++ pr_evar_map None sigma)); *)
  let env = pf_env gl in
  let beta = Reductionops.clos_norm_flags CClosure.beta env sigma in
  let sigma, p = 
    let sigma = Evd.create_evar_defs sigma in
    let (sigma, ev) = Evarutil.new_evar env sigma (beta (EConstr.Vars.subst1 new_rdx pred)) in
    (sigma, ev)
  in
  let pred = EConstr.mkNamedLambda pattern_id rdx_ty pred in
  let elim, gl = 
    let ((kn, i) as ind, _), unfolded_c_ty = pf_reduce_to_quantified_ind gl c_ty in
    let sort = elimination_sort_of_goal gl in
    let elim, gl = pf_fresh_global (Indrec.lookup_eliminator ind sort) gl in
    if dir = R2L then elim, gl else (* taken from Coq's rewrite *)
    let elim, _ = destConst elim in
    let mp,dp,l = Constant.repr3 (Constant.make1 (Constant.canonical elim)) in
    let l' = Label.of_id (Nameops.add_suffix (Label.to_id l) "_r")  in 
    let c1' = Global.constant_of_delta_kn (Constant.canonical (Constant.make3 mp dp l')) in
    mkConst c1', gl in
  let elim = EConstr.of_constr elim in
  let proof = EConstr.mkApp (elim, [| rdx_ty; new_rdx; pred; p; rdx; c |]) in
  (* We check the proof is well typed *)
  let sigma, proof_ty =
    try Typing.type_of env sigma proof with _ -> raise PRtype_error in
  ppdebug(lazy Pp.(str"pirrel_rewrite proof term of type: " ++ pr_econstr_env env sigma proof_ty));
  try refine_with 
    ~first_goes_last:(not !ssroldreworder) ~with_evars:false (sigma, proof) gl
  with _ -> 
    (* we generate a msg like: "Unable to find an instance for the variable" *)
    let hd_ty, miss = match EConstr.kind sigma c with
    | App (hd, args) -> 
        let hd_ty = Retyping.get_type_of env sigma hd in
        let names = let rec aux t = function 0 -> [] | n ->
          let t = Reductionops.whd_all env sigma t in
          match EConstr.kind_of_type sigma t with
          | ProdType (name, _, t) -> name :: aux t (n-1)
          | _ -> assert false in aux hd_ty (Array.length args) in
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
;;

let is_construct_ref sigma c r =
  EConstr.isConstruct sigma c && GlobRef.equal (ConstructRef (fst(EConstr.destConstruct sigma c))) r
let is_ind_ref sigma c r = EConstr.isInd sigma c && GlobRef.equal (IndRef (fst(EConstr.destInd sigma c))) r

let rwcltac cl rdx dir sr gl =
  let n, r_n,_, ucst = pf_abs_evars gl sr in
  let r_n' = pf_abs_cterm gl n r_n in
  let r' = EConstr.Vars.subst_var pattern_id r_n' in
  let gl = pf_unsafe_merge_uc ucst gl in
  let rdxt = Retyping.get_type_of (pf_env gl) (fst sr) rdx in
(*         ppdebug(lazy(str"sigma@rwcltac=" ++ pr_evar_map None (fst sr))); *)
        ppdebug(lazy Pp.(str"r@rwcltac=" ++ pr_econstr_env (pf_env gl) (project gl) (snd sr)));
  let cvtac, rwtac, gl =
    if EConstr.Vars.closed0 (project gl) r' then 
      let env, sigma, c, c_eq = pf_env gl, fst sr, snd sr, Coqlib.build_coq_eq () in
      let sigma, c_ty = Typing.type_of env sigma c in
        ppdebug(lazy Pp.(str"c_ty@rwcltac=" ++ pr_econstr_env env sigma c_ty));
      match EConstr.kind_of_type sigma (Reductionops.whd_all env sigma c_ty) with
      | AtomicType(e, a) when is_ind_ref sigma e c_eq ->
          let new_rdx = if dir = L2R then a.(2) else a.(1) in
          pirrel_rewrite cl rdx rdxt new_rdx dir (sigma,c) c_ty, tclIDTAC, gl
      | _ -> 
          let cl' = EConstr.mkApp (EConstr.mkNamedLambda pattern_id rdxt cl, [|rdx|]) in
          let sigma, _ = Typing.type_of env sigma cl' in
          let gl = pf_merge_uc_of sigma gl in
          Proofview.V82.of_tactic (convert_concl cl'), rewritetac dir r', gl
    else
      let dc, r2 = EConstr.decompose_lam_n_assum (project gl) n r' in
      let r3, _, r3t  = 
        try EConstr.destCast (project gl) r2 with _ ->
        errorstrm Pp.(str "no cast from " ++ pr_constr_pat (EConstr.Unsafe.to_constr (snd sr))
                    ++ str " to " ++ pr_econstr_env (pf_env gl) (project gl) r2) in
      let cl' = EConstr.mkNamedProd rule_id (EConstr.it_mkProd_or_LetIn r3t dc) (EConstr.Vars.lift 1 cl) in
      let cl'' = EConstr.mkNamedProd pattern_id rdxt cl' in
      let itacs = [introid pattern_id; introid rule_id] in
      let cltac = Proofview.V82.of_tactic (Tactics.clear [pattern_id; rule_id]) in
      let rwtacs = [rewritetac dir (EConstr.mkVar rule_id); cltac] in
      apply_type cl'' [rdx; EConstr.it_mkLambda_or_LetIn r3 dc], tclTHENLIST (itacs @ rwtacs), gl
  in
  let cvtac' _ =
    try cvtac gl with
    | PRtype_error ->
      if occur_existential (project gl) (Tacmach.pf_concl gl)
      then errorstrm Pp.(str "Rewriting impacts evars")
      else errorstrm Pp.(str "Dependent type error in rewrite of "
        ++ pr_constr_env (pf_env gl) (project gl) (Term.mkNamedLambda pattern_id (EConstr.Unsafe.to_constr rdxt) (EConstr.Unsafe.to_constr cl)))
  in
  tclTHEN cvtac' rwtac gl

let prof_rwcltac = mk_profiler "rwrxtac.rwcltac";;
let rwcltac cl rdx dir sr gl =
  prof_rwcltac.profile (rwcltac cl rdx dir sr) gl
;;


let lz_coq_prod =
  let prod = lazy (Coqlib.build_prod ()) in fun () -> Lazy.force prod

let lz_setoid_relation =
  let sdir = ["Classes"; "RelationClasses"] in
  let last_srel = ref (Environ.empty_env, None) in
  fun env -> match !last_srel with
  | env', srel when env' == env -> srel
  | _ ->
    let srel =
       try Some (UnivGen.constr_of_global @@
                   Coqlib.coq_reference "Class_setoid" sdir "RewriteRelation")
       with _ -> None in
    last_srel := (env, srel); srel

let ssr_is_setoid env =
  match lz_setoid_relation env with
  | None -> fun _ _ _ -> false
  | Some srel ->
  fun sigma r args ->
    Rewrite.is_applied_rewrite_relation env 
      sigma [] (EConstr.mkApp (r, args)) <> None

let prof_rwxrtac_find_rule = mk_profiler "rwrxtac.find_rule";;

let closed0_check cl p gl =
  if closed0 cl then
    errorstrm Pp.(str"No occurrence of redex "++ pr_constr_env (pf_env gl) (project gl) p)

let dir_org = function L2R -> 1 | R2L -> 2

let rwprocess_rule dir rule gl =
  let env = pf_env gl in
  let coq_prod = lz_coq_prod () in
  let is_setoid = ssr_is_setoid env in
  let r_sigma, rules =
    let rec loop d sigma r t0 rs red =
      let t =
        if red = 1 then Tacred.hnf_constr env sigma t0
        else Reductionops.whd_betaiotazeta sigma t0 in
      ppdebug(lazy Pp.(str"rewrule="++pr_constr_pat (EConstr.Unsafe.to_constr t)));
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
        if EConstr.eq_constr sigma a.(0) (EConstr.of_constr (UnivGen.constr_of_global @@ Coqlib.build_coq_True ())) then
         let s, sigma = sr sigma 2 in
         loop (converse_dir d) sigma s a.(1) rs 0
        else
         let s, sigma = sr sigma 2 in
         let sigma, rs2 = loop d sigma s a.(1) rs 0 in
         let s, sigma = sr sigma 1 in
         loop d sigma s a.(0) rs2 0
      | App (r_eq, a) when Hipattern.match_with_equality_type sigma t != None ->
        let (ind, u) = EConstr.destInd sigma r_eq and rhs = Array.last a in
        let np = Inductiveops.inductive_nparamdecls ind in
        let indu = (ind, EConstr.EInstance.kind sigma u) in
        let ind_ct = Inductiveops.type_of_constructors env indu in
        let lhs0 = last_arg sigma (EConstr.of_constr (strip_prod_assum ind_ct.(0))) in
        let rdesc = match EConstr.kind sigma lhs0 with
        | Rel i ->
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
        else errorstrm Pp.(str "not a rewritable relation: " ++ pr_constr_pat (EConstr.Unsafe.to_constr t)
                        ++ spc() ++ str "in rule " ++ pr_constr_pat  (EConstr.Unsafe.to_constr (snd rule)))
        in
    let sigma, r = rule in
    let t = Retyping.get_type_of env sigma r in
    loop dir sigma r t [] 0
  in
    r_sigma, rules

let rwrxtac occ rdx_pat dir rule gl =
  let env = pf_env gl in
  let r_sigma, rules = rwprocess_rule dir rule gl in
  let find_rule rdx =
    let rec rwtac = function
      | [] ->
        errorstrm Pp.(str "pattern " ++ pr_constr_pat (EConstr.Unsafe.to_constr rdx) ++
                   str " does not match " ++ pr_dir_side dir ++
                   str " of " ++ pr_constr_pat (EConstr.Unsafe.to_constr (snd rule)))
      | (d, r, lhs, rhs) :: rs ->
        try
          let ise = unify_HO env (Evd.create_evar_defs r_sigma) lhs rdx in
          if not (rw_progress rhs rdx ise) then raise NoMatch else
          d, (ise, Evd.evar_universe_context ise, Reductionops.nf_evar ise r)
        with _ -> rwtac rs in
     rwtac rules in
  let find_rule rdx = prof_rwxrtac_find_rule.profile find_rule rdx in
  let sigma0, env0, concl0 = project gl, pf_env gl, pf_concl gl in
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
      fun cl -> let rdx,d,r = end_R () in closed0_check cl rdx gl; (d,r),rdx
  | Some(_, (T e | X_In_T (_,e) | E_As_X_In_T (e,_,_) | E_In_X_In_T (e,_,_))) ->
      let r = ref None in
      (fun env c _ h -> do_once r (fun () -> find_rule (EConstr.of_constr c), c); mkRel h),
      (fun concl -> closed0_check concl e gl;
        let (d,(ev,ctx,c)) , x = assert_done r in (d,(ev,ctx, EConstr.to_constr ~abort_on_undefined_evars:false ev c)) , x) in
  let concl0 = EConstr.Unsafe.to_constr concl0 in
  let concl = eval_pattern env0 sigma0 concl0 rdx_pat occ find_R in
  let (d, r), rdx = conclude concl in
  let r = Evd.merge_universe_context (pi1 r) (pi2 r), EConstr.of_constr (pi3 r) in
  rwcltac (EConstr.of_constr concl) (EConstr.of_constr rdx) d r gl
;;

let prof_rwxrtac = mk_profiler "rwrxtac";;
let rwrxtac occ rdx_pat dir rule gl =
  prof_rwxrtac.profile (rwrxtac occ rdx_pat dir rule) gl
;;

let ssrinstancesofrule ist dir arg gl =
  let sigma0, env0, concl0 = project gl, pf_env gl, pf_concl gl in
  let rule = interp_term ist gl arg in
  let r_sigma, rules = rwprocess_rule dir rule gl in
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
      ignore(find env0 (EConstr.Unsafe.to_constr concl0) 1 ~k:print)
    done; raise NoMatch
  with NoMatch -> Feedback.msg_info Pp.(str"END INSTANCES"); tclIDTAC gl

let ipat_rewrite occ dir c gl = rwrxtac occ None dir (project gl, c) gl

let rwargtac ist ((dir, mult), (((oclr, occ), grx), (kind, gt))) gl =
  let fail = ref false in
  let interp_rpattern gl gc =
    try interp_rpattern gl gc
    with _ when snd mult = May -> fail := true; project gl, T mkProp in
  let interp gc gl =
    try interp_term ist gl gc
    with _ when snd mult = May -> fail := true; (project gl, EConstr.mkProp) in
  let rwtac gl = 
    let rx = Option.map (interp_rpattern gl) grx in
    let t = interp gt gl in
    (match kind with
    | RWred sim -> simplintac occ rx sim
    | RWdef -> if dir = R2L then foldtac occ rx t else unfoldintac occ rx t gt
    | RWeq -> rwrxtac occ rx dir t) gl in
  let ctac = old_cleartac (interp_clr (project gl) (oclr, (fst gt, snd (interp gt gl)))) in
  if !fail then ctac gl else tclTHEN (tclMULT mult rwtac) ctac gl

(** Rewrite argument sequence *)

(* type ssrrwargs = ssrrwarg list *)

(** The "rewrite" tactic *)

let ssrrewritetac ist rwargs =
  tclTHENLIST (List.map (rwargtac ist) rwargs)

(** The "unlock" tactic *)

let unfoldtac occ ko t kt gl =
  let env = pf_env gl in
  let cl, c = pf_fill_occ_term gl occ (fst (strip_unfold_term env t kt)) in
  let cl' = EConstr.Vars.subst1 (pf_unfoldn [OnlyOccurrences [1], get_evalref (project gl) c] gl c) cl in
  let f = if ko = None then CClosure.betaiotazeta else CClosure.betaiota in
  Proofview.V82.of_tactic
    (convert_concl (pf_reduce (Reductionops.clos_norm_flags f) gl cl')) gl

let unlocktac ist args gl =
  let utac (occ, gt) gl =
    unfoldtac occ occ (interp_term ist gl gt) (fst gt) gl in
  let locked, gl = pf_mkSsrConst "locked" gl in
  let key, gl = pf_mkSsrConst "master_key" gl in
  let ktacs = [
    (fun gl -> unfoldtac None None (project gl,locked) xInParens gl); 
    Ssrelim.casetac key ] in
  tclTHENLIST (List.map utac args @ ktacs) gl

