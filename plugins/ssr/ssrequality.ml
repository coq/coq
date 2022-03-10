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
open Proofview.Notations

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
  | Cut n -> Tacticals.tclTRY (donetac n)
  | SimplCut (n,m) -> Tacticals.tclTHEN (safe_simpltac m) (Tacticals.tclTRY (donetac n))
  | Nop -> Tacticals.tclIDTAC

let simpltac s = Proofview.Goal.enter (fun _ -> simpltac s)

(** The "congr" tactic *)

let interp_congrarg_at env sigma ist ~concl n rf ty m =
  debug_ssr (fun () -> Pp.(str"===interp_congrarg_at==="));
  let congrn, _ = mkSsrRRef "nary_congruence" in
  let args1 = mkRnat n :: mkRHoles n @ [ty] in
  let args2 = mkRHoles (3 * n) in
  let rec loop i =
    if i + n > m then None else
    try
      let rt = mkRApp congrn (args1 @  mkRApp rf (mkRHoles i) :: args2) in
      debug_ssr (fun () -> Pp.(str"rt=" ++ Printer.pr_glob_constr_env env sigma rt));
      Some (interp_refine env sigma ist ~concl rt)
    with _ -> loop (i + 1) in
  loop 0

let pattern_id = mk_internal_id "pattern value"

let congrtac ((n, t), ty) ist =
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let concl = Proofview.Goal.concl gl in
  debug_ssr (fun () -> (Pp.str"===congr==="));
  debug_ssr (fun () -> Pp.(str"concl=" ++ Printer.pr_econstr_env env sigma concl));
  let nsigma, _ as it = interp_term env sigma ist t in
  let sigma = Evd.merge_universe_context sigma (Evd.evar_universe_context nsigma) in
  let f, _, _ucst = abs_evars env sigma it in
  let ist' = {ist with lfun =
    Id.Map.add pattern_id (Tacinterp.Value.of_constr f) Id.Map.empty } in
  let rf = mkRltacVar pattern_id in
  let m = pf_nbargs env sigma f in
  let cf = if n > 0 then
    match interp_congrarg_at env sigma ist' ~concl n rf ty m with
    | Some cf -> cf
    | None -> errorstrm Pp.(str "No " ++ int n ++ str "-congruence with "
                         ++ pr_term t)
    else let rec loop i =
      if i > m then errorstrm Pp.(str "No congruence with " ++ pr_term t)
      else match interp_congrarg_at env sigma ist' ~concl i rf ty m with
      | Some cf -> cf
      | None -> loop (i + 1) in
      loop 1 in
  Tacticals.(tclTHEN (refine_with cf) (tclTRY Tactics.reflexivity))
  end

let pf_typecheck t =
  Proofview.Goal.enter begin fun gl ->
  let sigma, _  = Typing.type_of (Proofview.Goal.env gl) (Proofview.Goal.sigma gl) t in
  Proofview.Unsafe.tclEVARS sigma
  end

let tclMATCH_GOAL env sigma c t_ok t_fail =
  Proofview.Goal.enter begin fun gl ->
  match unify_HO env sigma (Proofview.Goal.concl gl) c with
  | sigma ->
    Proofview.Unsafe.tclEVARS sigma <*>
    convert_concl ~check:true (Reductionops.nf_evar sigma c) <*> t_ok sigma
  | exception exn when CErrors.noncritical exn -> t_fail ()
  end

let mk_evar env sigma ty =
  let sigma = Evd.create_evar_defs sigma in
  let (sigma, x) = Evarutil.new_evar env sigma ty in
  sigma, x

let newssrcongrtac arg ist =
  let open Proofview.Notations in
  Proofview.Goal.enter_one ~__LOC__ begin fun _g ->
    (Ssrcommon.tacMK_SSR_CONST "ssr_congr_arrow") end >>= fun arr ->
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let concl = Proofview.Goal.concl gl in
  debug_ssr (fun () -> Pp.(str"===newcongr==="));
  debug_ssr (fun () -> Pp.(str"concl=" ++ Printer.pr_econstr_env env sigma concl));
  (* utils *)
  let fs sigma t = Reductionops.nf_evar sigma t in
  let ssr_congr lr = EConstr.mkApp (arr, lr) in
  let sigma, eq = Evd.fresh_global env sigma Coqlib.(lib_ref "core.eq.type") in
  (* here the two cases: simple equality or arrow *)
  let equality, _, eq_args, sigma' = saturate env sigma eq 3 in
  Proofview.Unsafe.tclEVARS sigma <*>
  tclMATCH_GOAL env sigma' equality
  (fun sigma' ->
    let x = List.find_map (fun (n, x, _) -> if n = 0 then Some x else None) eq_args in
    let ty = fs sigma' x in
    congrtac (arg, Detyping.detype Detyping.Now false Id.Set.empty env sigma ty) ist)
  (fun () ->
    try
    let sigma, t_lhs = Evarutil.new_Type sigma in
    let sigma, t_rhs = Evarutil.new_Type sigma in
    let sigma, lhs = mk_evar env sigma t_lhs in
    let sigma, rhs = mk_evar env sigma t_rhs in
    let arrow = EConstr.mkArrow lhs Sorts.Relevant (EConstr.Vars.lift 1 rhs) in
    tclMATCH_GOAL env sigma arrow
    (fun sigma ->
      let lr = [|fs sigma lhs;fs sigma rhs|] in
      let a = ssr_congr lr in
      Tacticals.tclTHENLIST [ pf_typecheck a
                  ; Tactics.apply a
                  ; congrtac (arg, mkRType) ist ])
    (fun _ -> Tacticals.tclZEROMSG Pp.(str"Conclusion is not an equality nor an arrow"))
    with e -> Proofview.tclZERO e (* FIXME *)
    )
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
      let simp env c _ _ = red_safe Tacred.simpl env sigma0 c in
      convert_concl_no_check (eval_pattern env0 sigma0 (Reductionops.nf_evar sigma0 concl0) rdx occ simp)
    end
  in
  let open Tacticals in
  Proofview.Goal.enter begin fun _ ->
  match sim with
  | Simpl m -> simptac m
  | SimplCut (n,m) -> tclTHEN (simptac m) (tclTRY (donetac n))
  | _ -> simpltac sim
  end

let rec get_evalref env sigma c = match EConstr.kind sigma c with
  | Var id -> Tacred.EvalVarRef id
  | Const (k,_) -> Tacred.EvalConstRef k
  | App (c', _) -> get_evalref env sigma c'
  | Cast (c', _, _) -> get_evalref env sigma c'
  | Proj(c,_) -> Tacred.EvalConstRef(Projection.constant c)
  | _ -> errorstrm Pp.(str "The term " ++ pr_econstr_pat (Global.env ()) sigma c ++ str " is not unfoldable")

(* Strip a pattern generated by a prenex implicit to its constant. *)
let strip_unfold_term _ ((sigma, t) as p) kt = match EConstr.kind sigma t with
  | App (f, a) when kt = NoFlag && Array.for_all (EConstr.isEvar sigma) a && EConstr.isConst sigma f ->
    (sigma, f), true
  | Const _ | Var _ -> p, true
  | Proj _ -> p, true
  | _ -> p, false

let same_proj sigma t1 t2 =
  match EConstr.kind sigma t1, EConstr.kind sigma t2 with
  | Proj(c1,_), Proj(c2, _) -> Projection.CanOrd.equal c1 c2
  | _ -> false

let classify_pattern p = match p with
| None -> None
| Some p -> redex_of_pattern p

let unfoldintac occ rdx t (kt,_) =
  Proofview.Goal.enter begin fun gl ->
  let fs sigma x = Reductionops.nf_evar sigma x in
  let sigma0 = Proofview.Goal.sigma gl in
  let env0 = Proofview.Goal.env gl in
  let concl0 = Proofview.Goal.concl gl in
  let (sigma, t), const = strip_unfold_term env0 t kt in
  let body env t c =
    Tacred.unfoldn [AllOccurrences, get_evalref env sigma t] env sigma0 c in
  let easy = occ = None && rdx = None in
  let red_flags = if easy then CClosure.betaiotazeta else CClosure.betaiota in
  let beta env = Reductionops.clos_norm_flags red_flags env sigma0 in
  let unfold, conclude = match classify_pattern rdx with
  | None ->
    let ise = Evd.create_evar_defs sigma in
    let rigid ev = Evd.mem sigma0 ev in
    let ise, u = mk_tpattern env0 ~rigid (ise, t) L2R t in
    let find_T, end_T =
      mk_tpattern_matcher ~raise_NoMatch:true sigma0 occ (ise,[u]) in
    (fun env c _ h ->
      try find_T env c h ~k:(fun env c _ _ -> body env t c)
      with NoMatch when easy -> c
      | NoMatch | NoProgress -> errorstrm Pp.(str"No occurrence of "
        ++ pr_econstr_pat env sigma0 t ++ spc() ++ str "in " ++ Printer.pr_econstr_env env sigma c)),
    (fun () -> try ignore @@ end_T () with
      | NoMatch when easy -> ()
      | NoMatch -> anomaly "unfoldintac")
  | Some _ ->
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
            | Const f -> aux (body env c c)
            | App (f, a) -> aux (EConstr.mkApp (body env f f, a))
            | _ -> errorstrm Pp.(str "The term "++ pr_econstr_env env sigma orig_c ++
                str" contains no " ++ pr_econstr_env env sigma t ++ str" even after unfolding")
          in aux c
      else
        try body env t (fs (unify_HO env sigma c t) t)
        with _ -> errorstrm Pp.(str "The term " ++
          pr_econstr_env env sigma c ++spc()++ str "does not unify with " ++ pr_econstr_pat env sigma t)),
    ignore in
  let concl =
    try beta env0 (eval_pattern env0 sigma0 concl0 rdx occ unfold)
    with Option.IsNone -> errorstrm Pp.(str"Failed to unfold " ++ pr_econstr_pat env0 sigma t) in
  let () = conclude () in
  convert_concl ~check:true concl
  end

let foldtac occ rdx ft =
  Proofview.Goal.enter begin fun gl ->
  let sigma0 = Proofview.Goal.sigma gl in
  let env0 = Proofview.Goal.env gl in
  let concl0 = Proofview.Goal.concl gl in
  let sigma, t = ft in
  let t = Reductionops.nf_evar sigma t in
  let fold, conclude = match classify_pattern rdx with
  | None ->
    let ise = Evd.create_evar_defs sigma in
    let ut = red_product_skip_id env0 sigma t in
    let rigid ev = Evd.mem sigma0 ev in
    let ise, ut = mk_tpattern ~rigid env0 (ise,t) L2R ut in
    let find_T, end_T =
      mk_tpattern_matcher ~raise_NoMatch:true sigma0 occ (ise,[ut]) in
    (fun env c _ h -> try find_T env c h ~k:(fun env t _ _ -> t) with NoMatch ->c),
    (fun () -> try ignore @@ end_T () with NoMatch -> ())
  | Some _ ->
    (fun env c _ h ->
       try
         let sigma = unify_HO env sigma c t in
         Reductionops.nf_evar sigma t
    with _ -> errorstrm Pp.(str "fold pattern " ++ pr_econstr_pat env sigma t ++ spc ()
      ++ str "does not match redex " ++ pr_econstr_pat env sigma c)),
    ignore in
  let concl = eval_pattern env0 sigma0 concl0 rdx occ fold in
  let () = conclude () in
  convert_concl ~check:true concl
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

(* Invariants expected from the arguments:
    ⊢ rdx : rdx_ty
    pattern_id : rdx_ty ⊢ pred : Type@{s}
    ⊢ new_rdx : rdx_ty
    ⊢ c : c_ty
    ⊢ c_ty ≡ EQN rdx_ty rdx new_rdx
*)
let pirrel_rewrite ?(under=false) ?(map_redex=id_map_redex) pred rdx rdx_ty new_rdx dir (sigma, c) c_ty =
  let open Tacmach in
  let open Tacticals in
  Proofview.Goal.enter begin fun gl ->
(*   ppdebug(lazy(str"sigma@pirrel_rewrite=" ++ pr_evar_map None sigma)); *)
  let env = pf_env gl in
  let beta = Reductionops.clos_norm_flags CClosure.beta env sigma in
  let sigma, new_rdx = map_redex env sigma ~before:rdx ~after:new_rdx in
  let sigma, p = (* The resulting goal *)
    Evarutil.new_evar env sigma (beta (EConstr.Vars.subst1 new_rdx pred)) in
  let pred = EConstr.mkNamedLambda (make_annot pattern_id Sorts.Relevant) rdx_ty pred in
  let sigma, elim =
    let sort = Tacticals.elimination_sort_of_goal gl in
    match Equality.eq_elimination_ref (dir = L2R) sort with
    | Some r -> Evd.fresh_global env sigma r
    | None ->
      let ((kn, i) as ind, _), unfolded_c_ty = Tacred.reduce_to_quantified_ind env sigma c_ty in
      let sort = Tacticals.elimination_sort_of_goal gl in
      let sigma, elim = Evd.fresh_global env sigma (Indrec.lookup_eliminator env ind sort) in
      if dir = R2L then sigma, elim else
      let elim, _ = EConstr.destConst sigma elim in
      let mp,l = KerName.repr (Constant.canonical elim) in
      let l' = Label.of_id (Nameops.add_suffix (Label.to_id l) "_r")  in
      let c1' = Global.constant_of_delta_kn (Constant.canonical (Constant.make2 mp l')) in
      sigma, EConstr.of_constr (mkConst c1')
  in
  (* We check the proof is well typed. We assume that the type of [elim] is of
     the form [forall (A : Type) (x : A) (P : A -> Type@{s}), T] s.t. the only
     universes to unify are by checking the [A] and [P] arguments. *)
  let sigma =
    try
      let open EConstr in
      let elimT = Retyping.get_type_of env sigma elim in
      let (idA, tA, elimT) = destProd sigma elimT in
      let (_, _, elimT) = destProd sigma elimT in
      let (idP, tP, _) = destProd sigma elimT in
      let sigma = Typing.check env sigma rdx_ty tA in
      let tP = mkLetIn (idA, rdx_ty, tA, mkLetIn (anonR, mkProp, mkType Univ.Universe.type1, tP)) in
      let sigma = Typing.check env sigma pred tP in
      sigma
    with
    | Pretype_errors.PretypeError (env, sigma, te) -> raise (PRtype_error (Some (env, sigma, te)))
    | e when CErrors.noncritical e -> raise (PRtype_error None)
  in
  let proof = EConstr.mkApp (elim, [| rdx_ty; new_rdx; pred; p; rdx; c |]) in
  debug_ssr (fun () -> Pp.(str"pirrel_rewrite: proof term: " ++ pr_econstr_env env sigma proof));
  Proofview.tclORELSE (refine_with
    ~first_goes_last:(not !ssroldreworder || under) ~with_evars:under (sigma, proof))
  (fun e ->
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
      tclZEROMSG Pp.(Himsg.explain_refiner_error env sigma (Logic.UnresolvedBindings miss)++
      (Pp.fnl()++str"Rule's type:" ++ spc() ++ pr_econstr_env env sigma hd_ty)))
  end

let pf_merge_uc_of s sigma =
  Evd.merge_universe_context sigma (Evd.evar_universe_context s)

let rwcltac ?under ?map_redex cl rdx dir (sigma, r) =
  let open Proofview.Notations in
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma0 = Proofview.Goal.sigma gl in
  let sigma = resolve_typeclasses ~where:r ~fail:false env sigma in
  let r_n, evs, ucst = abs_evars env sigma0 (sigma, r) in
  let n = List.length evs in
  let r_n' = abs_cterm env sigma0 n r_n in
  let r' = EConstr.Vars.subst_var pattern_id r_n' in
  let sigma0 = Evd.set_universe_context sigma0 ucst in
  let sigma, rdxt = Typing.type_of env sigma rdx in
  let () = debug_ssr (fun () -> Pp.(str"r@rwcltac=" ++ pr_econstr_env env sigma r)) in
  let cvtac, rwtac, sigma0 =
    if EConstr.Vars.closed0 sigma0 r' then
      let c_eq = Coqlib.(lib_ref "core.eq.type") in
      let sigma, c_ty = Typing.type_of env sigma r in
      let () = debug_ssr (fun () -> Pp.(str"c_ty@rwcltac=" ++ pr_econstr_env env sigma c_ty)) in
      let open EConstr in
      match kind_of_type sigma (Reductionops.whd_all env sigma c_ty) with
      | AtomicType(e, a) when Ssrcommon.is_ind_ref sigma e c_eq ->
          let new_rdx = if dir = L2R then a.(2) else a.(1) in
          pirrel_rewrite ?under ?map_redex cl rdx a.(0) new_rdx dir (sigma, r) c_ty, Tacticals.tclIDTAC, sigma0
      | _ ->
          let cl' = EConstr.mkApp (EConstr.mkNamedLambda (make_annot pattern_id Sorts.Relevant) rdxt cl, [|rdx|]) in
          let sigma, _ = Typing.type_of env sigma cl' in
          let sigma0 = pf_merge_uc_of sigma sigma0 in
          convert_concl ~check:true cl', rewritetac ?under dir r', sigma0
    else
      let dc, r2 = EConstr.decompose_lam_n_assum sigma0 n r' in
      let r3, _, r3t  =
        try EConstr.destCast sigma0 r2 with _ ->
        errorstrm Pp.(str "no cast from " ++ pr_econstr_pat env sigma0 r
                    ++ str " to " ++ pr_econstr_env env sigma0 r2) in
      let cl' = EConstr.mkNamedProd (make_annot rule_id Sorts.Relevant) (EConstr.it_mkProd_or_LetIn r3t dc) (EConstr.Vars.lift 1 cl) in
      let cl'' = EConstr.mkNamedProd (make_annot pattern_id Sorts.Relevant) rdxt cl' in
      let itacs = [introid pattern_id; introid rule_id] in
      let cltac = Tactics.clear [pattern_id; rule_id] in
      let rwtacs = [
        Tacticals.tclTHENLIST [
          rewritetac ?under dir (EConstr.mkVar rule_id);
          if !ssroldreworder || Option.default false under then
            Proofview.tclUNIT ()
          else
            Proofview.cycle 1
          ];
        cltac] in
      Tactics.apply_type ~typecheck:true cl'' [rdx; EConstr.it_mkLambda_or_LetIn r3 dc], Tacticals.tclTHENLIST (itacs @ rwtacs), sigma0
  in
  let cvtac' =
    Proofview.tclORELSE cvtac begin function
    | (PRtype_error e, _) ->
      let error = Option.cata (fun (env, sigma, te) ->
          Pp.(fnl () ++ str "Type error was: " ++ Himsg.explain_pretype_error env sigma te))
          (Pp.mt ()) e in
      if occur_existential sigma0 (Tacmach.pf_concl gl)
      then Tacticals.tclZEROMSG Pp.(str "Rewriting impacts evars" ++ error)
      else Tacticals.tclZEROMSG Pp.(str "Dependent type error in rewrite of "
        ++ pr_econstr_env env sigma0
          (EConstr.mkNamedLambda (make_annot pattern_id Sorts.Relevant) rdxt cl)
        ++ error)
    | (e, info) -> Proofview.tclZERO ~info e
    end
  in
  Proofview.Unsafe.tclEVARS sigma0 <*>
  Tacticals.tclTHEN cvtac' rwtac
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
       try Some (UnivGen.constr_of_monomorphic_global (Global.env ()) @@
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
  if EConstr.Vars.closed0 sigma cl then
    errorstrm Pp.(str"No occurrence of redex "++ pr_econstr_env env sigma p)

let dir_org = function L2R -> 1 | R2L -> 2

let rwprocess_rule env dir rule =
  let coq_prod = lz_coq_prod () in
  let is_setoid = ssr_is_setoid env in
  let r_sigma, rules =
    let rec loop d sigma r t0 rs red =
      let t =
        if red = 1 then Tacred.hnf_constr env sigma t0
        else Reductionops.clos_whd_flags CClosure.betaiotazeta env sigma t0 in
      debug_ssr (fun () -> Pp.(str"rewrule="++pr_econstr_pat env sigma t));
      match EConstr.kind sigma t with
      | Prod (_, xt, at) ->
        let sigma = Evd.create_evar_defs sigma in
        let (sigma, x) = Evarutil.new_evar env sigma xt in
        loop d sigma EConstr.(mkApp (r, [|x|])) (EConstr.Vars.subst1 x at) rs 0
      | App (pr, a) when is_ind_ref sigma pr coq_prod.Coqlib.typ ->
        let r0 = Reductionops.clos_whd_flags CClosure.all env sigma r in
        let sigma, pL, pR = match EConstr.kind sigma r0 with
        | App (c, ra) when is_construct_ref sigma c coq_prod.Coqlib.intro ->
          (sigma, ra.(2), ra.(3))
        | _ ->
          let ra = Array.append a [|r|] in
          let sigma, pi1 = Evd.fresh_global env sigma coq_prod.Coqlib.proj1 in
          let sigma, pi2 = Evd.fresh_global env sigma coq_prod.Coqlib.proj2 in
          let pL = EConstr.mkApp (pi1, ra) in
          let pR = EConstr.mkApp (pi2, ra) in
          (sigma, pL, pR)
        in
        if EConstr.isRefX sigma Coqlib.(lib_ref "core.True.type") a.(0) then
         loop (converse_dir d) sigma pR a.(1) rs 0
        else
         let sigma, rs2 = loop d sigma pR a.(1) rs 0 in
         loop d sigma pL a.(0) rs2 0
      | App (r_eq, a) when Hipattern.match_with_equality_type env sigma t != None ->
        let (ind, u) = EConstr.destInd sigma r_eq and rhs = Array.last a in
        let np = Inductiveops.inductive_nparamdecls env ind in
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
  let rigid ev = Evd.mem sigma0 ev in
  let find_R, conclude = match classify_pattern rdx_pat with
  | None ->
      let upats_origin = dir, (snd rule) in
      let rpat (sigma, pats) (d, r, lhs, rhs) =
        let sigma, pat =
          mk_tpattern ~ok:(rw_progress rhs) ~rigid env0 (sigma, Reductionops.nf_evar sigma r) d (Reductionops.nf_evar sigma lhs) in
        sigma, pats @ [pat] in
      let rpats = List.fold_left rpat (r_sigma,[]) rules in
      let find_R, end_R = mk_tpattern_matcher sigma0 occ ~upats_origin rpats in
      (fun e c _ i -> find_R ~k:(fun _ _ _ h -> EConstr.mkRel h) e c i),
      fun cl -> let rdx,d,r = end_R () in closed0_check env0 sigma0 cl rdx; (d,r),rdx
  | Some (_, e) ->
      let r = ref None in
      (fun env c _ h -> do_once r (fun () -> find_rule c, c); EConstr.mkRel h),
      (fun concl -> closed0_check env0 sigma0 concl e;
        let (d,(ev,ctx,c)) , x = assert_done r in (d,(true, ev,ctx, Reductionops.nf_evar ev c)) , x) in
  let concl0 = Reductionops.nf_evar sigma0 concl0 in
  let concl = eval_pattern env0 sigma0 concl0 rdx_pat occ find_R in
  let (d, (_, sigma, uc, t)), rdx = conclude concl in
  let r = Evd.merge_universe_context sigma uc, t in
  rwcltac ?under ?map_redex concl rdx d r
  end

let ssrinstancesofrule ist dir arg =
  Proofview.Goal.enter begin fun gl ->
  let env0 = Proofview.Goal.env gl in
  let sigma0 = Proofview.Goal.sigma gl in
  let concl0 = Proofview.Goal.concl gl in
  let rigid ev = Evd.mem sigma0 ev in
  let rule = interp_term env0 sigma0 ist arg in
  let r_sigma, rules = rwprocess_rule env0 dir rule in
  let find, conclude =
    let upats_origin = dir, (snd rule) in
    let rpat (sigma, pats) (d, r, lhs, rhs) =
      let sigma, pat =
        mk_tpattern ~ok:(rw_progress rhs) ~rigid env0
          (sigma, Reductionops.nf_evar sigma r)
          d
          (Reductionops.nf_evar sigma lhs) in
      sigma, pats @ [pat] in
    let rpats = List.fold_left rpat (r_sigma,[]) rules in
    mk_tpattern_matcher ~all_instances:true ~raise_NoMatch:true sigma0 None ~upats_origin rpats in
  let print env p c _ = Feedback.msg_info Pp.(hov 1 (str"instance:" ++ spc() ++ pr_econstr_env env r_sigma p ++ spc() ++ str "matches:" ++ spc() ++ pr_econstr_env env r_sigma c)); c in
  Feedback.msg_info Pp.(str"BEGIN INSTANCES");
  try
    while true do
      ignore(find env0 (Reductionops.nf_evar sigma0 concl0) 1 ~k:print)
    done; raise NoMatch
  with NoMatch -> Feedback.msg_info Pp.(str"END INSTANCES"); Tacticals.tclIDTAC
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
    with _ when snd mult = May -> fail := true; sigma, T EConstr.mkProp in
  let interp env sigma gc =
    try interp_term env sigma ist gc
    with _ when snd mult = May -> fail := true; (sigma, EConstr.mkProp) in
  let rwtac =
    Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let rx = Option.map (interp_rpattern env sigma) grx in
    (* Evarmaps below are extensions of sigma, so setting the universe context is correct *)
    let sigma = match rx with
    | None -> sigma
    | Some (s,_) -> Evd.set_universe_context sigma (Evd.evar_universe_context s)
    in
    let t = interp env sigma gt in
    let sigma = Evd.set_universe_context sigma  (Evd.evar_universe_context (fst t)) in
    Proofview.Unsafe.tclEVARS sigma <*>
    (match kind with
    | RWred sim -> simplintac occ rx sim
    | RWdef -> if dir = R2L then foldtac occ rx t else unfoldintac occ rx t gt
    | RWeq -> rwrxtac ?under ?map_redex occ rx dir t)
    end
  in
  let ctac = cleartac (interp_clr sigma (oclr, (fst gt, snd (interp env sigma gt)))) in
  if !fail then ctac else Tacticals.tclTHEN (tclMULT mult rwtac) ctac
  end

(** Rewrite argument sequence *)

(* type ssrrwargs = ssrrwarg list *)

(** The "rewrite" tactic *)

let ssrrewritetac ?under ?map_redex ist rwargs =
  Proofview.Goal.enter begin fun _ ->
  Tacticals.tclTHENLIST (List.map (rwargtac ?under ?map_redex ist) rwargs)
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
    (Proofview.tclEVARMAP >>= fun sigma -> unfoldtac None None (sigma, locked) InParens);
    Ssrelim.casetac key (fun ?seed:_ k -> k)
  ] in
  Tacticals.tclTHENLIST (List.map utac args @ ktacs)
