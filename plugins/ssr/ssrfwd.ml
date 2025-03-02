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

open Pp
open Names
open Constr
open Context

open Proofview.Notations

open Ssrmatching_plugin.Ssrmatching
open Ssrprinters
open Ssrcommon
open Ssrtacticals

module RelDecl = Context.Rel.Declaration
module ERelevance = EConstr.ERelevance

(** 8. Forward chaining tactics (pose, set, have, suffice, wlog) *)
(** Defined identifier *)

let ssrposetac (id, (_, t)) =
  let open Proofview.Notations in
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let ist, t =
    match t.Ssrast.interp_env with
    | Some ist -> ist, Ssrcommon.ssrterm_of_ast_closure_term t
    | None -> assert false in
  let sigma, t, _ = abs_ssrterm ist env sigma t in
  Proofview.Unsafe.tclEVARS sigma <*>
  Tactics.pose_tac (Name id) t
  end

let redex_of_pattern_tc env p =
  let sigma, e = match redex_of_pattern p with
  | None -> CErrors.anomaly (str "pattern without redex.")
  | Some (sigma, e) -> sigma, e
  in
  let sigma = Typeclasses.resolve_typeclasses ~fail:false env sigma in
  Evarutil.nf_evar sigma e, Evd.ustate sigma

let ssrsettac id ((_, (pat, pty)), (_, occ)) =
  let open Proofview.Notations in
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let cl = Proofview.Goal.concl gl in
  let pty = Option.map (fun { Ssrast.body; interp_env } ->
    let ist = Option.get interp_env in
    (mkRHole, Some body), ist) pty in
  let pat = interp_cpattern env sigma pat pty in
  let (c, ucst), cl =
    try fill_occ_pattern ~raise_NoMatch:true env sigma cl pat occ 1
    with NoMatch -> redex_of_pattern_tc env pat, cl in
  let sigma = Evd.merge_universe_context sigma ucst in
  if Termops.occur_existential sigma c then errorstrm(str"The pattern"++spc()++
    pr_econstr_pat env sigma c++spc()++str"did not match and has holes."++spc()++
    str"Did you mean pose?") else
  let c, (sigma, cty) =  match EConstr.kind sigma c with
  | Cast(t, DEFAULTcast, ty) -> t, (sigma, ty)
  | _ -> c, Typing.type_of env sigma c in
  let cl' = EConstr.mkLetIn (make_annot (Name id) ERelevance.relevant, c, cty, cl) in
  Proofview.Unsafe.tclEVARS sigma <*>
  convert_concl ~check:true cl' <*>
  introid id
  end

open Util

open Printer

open Ssrast
open Ssripats

let ssrhaveNOtcresolution = Summary.ref ~name:"SSR:havenotcresolution" false

let () =
  Goptions.(declare_bool_option
    { optstage = Summary.Stage.Interp;
      optkey   = ["SsrHave";"NoTCResolution"];
      optread  = (fun _ -> !ssrhaveNOtcresolution);
      optdepr  = None;
      optwrite = (fun b -> ssrhaveNOtcresolution := b);
    })


open Constrexpr
open Glob_term

let combineCG t1 t2 f g = match t1, t2 with
 | (x, (t1, None)), (_, (t2, None)) -> x, (g t1 t2, None)
 | (x, (_, Some t1)), (_, (_, Some t2)) -> x, (mkRHole, Some (f t1 t2))
 | _, (_, (_, None)) -> anomaly "have: mixed C-G constr"
 | _ -> anomaly "have: mixed G-C constr"

type cut_kind = Have | HaveTransp | Suff

let basecuttac k c =
  let open Proofview.Notations in
  let open EConstr in
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Tacmach.project gl in
    let concl = Proofview.Goal.concl gl in
    match Typing.sort_of env sigma c with
    | exception e when CErrors.noncritical e ->
      let _, info = Exninfo.capture e in
      Tacticals.tclZEROMSG ~info (str "Not a proposition or a type.")
    | sigma, sc ->
      let r = ESorts.relevance_of_sort sc in
      let needs_typing, sigma, f, glf =
        match k with
        | HaveTransp ->
          let name = Context.make_annot Name.Anonymous r in
          let sigma, p = Evarutil.new_evar env sigma c in
          let sigma, f = Evarutil.new_evar env sigma (mkLetIn (name,p,c,Vars.lift 1 concl)) in
          let gp = Proofview_monad.with_empty_state (fst @@ destEvar sigma p) in
          let gf = Proofview_monad.with_empty_state (fst @@ destEvar sigma f) in
          false, sigma, f, [gp;gf]
        | _ ->
          let sigma, sg = Typing.sort_of env sigma concl in
          let qc,qg = ESorts.quality sigma sc, ESorts.quality sigma sg in
          match qc, qg with
          | Sorts.Quality.(QConstant QProp), Sorts.Quality.(QConstant QProp) ->
          let f = Rocqlib.lib_ref ("plugins.ssreflect.ssr_have") in
          let sigma, f = EConstr.fresh_global env sigma f in
          let sigma, step = Evarutil.new_evar env sigma c in
          let stepg = Proofview_monad.with_empty_state (fst @@ destEvar sigma step) in
          let sigma, rest = Evarutil.new_evar env sigma (mkArrow c r concl) in
          let restg = Proofview_monad.with_empty_state (fst @@ destEvar sigma rest) in
          let glf = [stepg;restg] in
          let f = EConstr.mkApp (f, [|c;concl;step;rest|]) in
          false, sigma, f, glf
          | _ ->
          let f = Rocqlib.lib_ref ("plugins.ssreflect.ssr_have_upoly") in
          let sigma, uc = match qc with
            | QConstant (QSProp | QProp) -> sigma, Univ.Level.set
            | _ -> Evd.new_univ_level_variable Evd.univ_flexible sigma in
          let sigma, ug = match qg with
            | QConstant (QSProp | QProp) -> sigma, Univ.Level.set
            | _ -> Evd.new_univ_level_variable Evd.univ_flexible sigma in
          let names = UVars.Instance.of_array ([|qc;qg|],[|uc;ug|]) in
          let sigma, f = EConstr.fresh_global env sigma ~names f in
          let sigma, step = Evarutil.new_evar env sigma c in
          let stepg = Proofview_monad.with_empty_state (fst @@ destEvar sigma step) in
          let sigma, rest = Evarutil.new_evar env sigma (mkArrow c r concl) in
          let restg = Proofview_monad.with_empty_state (fst @@ destEvar sigma rest) in
          let glf = [stepg;restg] in
          let f = EConstr.mkApp (f, [|c;concl;step;rest|]) in
          true, sigma, f, glf in
      Proofview.Unsafe.tclEVARS sigma <*>
      (if needs_typing
        then Ssrcommon.tacTYPEOF f >>= fun _ -> Tacticals.tclIDTAC
        else Tacticals.tclIDTAC) >>= fun () ->
      Tactics.eapply ~with_classes:false f
      <*>
      Proofview.Unsafe.tclGETGOALS >>= begin fun gl ->
        match k with
        | Suff ->
            Proofview.Unsafe.tclSETGOALS (List.rev glf @ gl) <*>
            Proofview.tclFOCUS 1 (List.length glf) Tactics.reduce_after_refine
        | Have | HaveTransp ->
            let ngoals = List.length gl + 1 in
            Proofview.Unsafe.tclSETGOALS (gl @ glf) <*>
            Proofview.tclFOCUS ngoals (ngoals + List.length glf - 1) Tactics.reduce_after_refine
      end
    end

let basesufftac t = basecuttac Suff t

let introstac ipats = tclIPAT ipats

let make_ct t =
  let open CAst in
  let mkt t = mk_term NoFlag t in
  let mkl t = (NoFlag, (t, None)) in
  match Ssrcommon.ssrterm_of_ast_closure_term t with
  | _, (_, Some { loc; v = CCast (ct, Some DEFAULTcast, cty)}) ->
    mkt ct, mkt cty, mkt (mkCHole None), loc
  | _, (_, Some ct) ->
    mkt ct, mkt (mkCHole None), mkt (mkCHole None), None
  | _, (t, None) ->
    begin match DAst.get t with
    | GCast (ct, Some DEFAULTcast, cty) ->
      mkl ct, mkl cty, mkl mkRHole, t.CAst.loc
    | _ -> mkl t, mkl mkRHole, mkl mkRHole, None
    end

(* FIXME: understand why we have to play with the goal states *)

let drop_state =
  let map gl = Proofview.with_empty_state (Proofview.drop_state gl) in
  Proofview.Unsafe.tclGETGOALS >>= fun gls ->
  Proofview.Unsafe.tclSETGOALS (List.map map gls)

let set_state s =
  let map gl = Proofview.goal_with_state (Proofview.drop_state gl) s in
  Proofview.Unsafe.tclGETGOALS >>= fun gls ->
  Proofview.Unsafe.tclSETGOALS (List.map map gls)

let assert_is_conv (ctx, concl) =
  Proofview.Goal.enter begin fun gl ->
    Proofview.tclORELSE (convert_concl ~check:true (EConstr.it_mkProd_or_LetIn concl ctx))
    (fun _ -> Tacticals.tclZEROMSG (str "Given proof term is not of type " ++
      pr_econstr_env (Tacmach.pf_env gl) (Tacmach.project gl) (EConstr.mkArrow (EConstr.mkVar (Id.of_string "_")) ERelevance.relevant concl)))
  end

let push_goals gs =
  Proofview.Goal.enter begin fun gl ->
    (* FIXME: do we really want to preserve state? *)
    let gstate = Proofview.Goal.state gl in
    let map ev = Proofview.goal_with_state ev gstate in
    Proofview.Unsafe.tclSETGOALS (List.map map (gs @ [Proofview.Goal.goal gl]))
  end

let havetac ist
  (transp,((((clr, orig_pats), binders), simpl), (((fk, _), t), hint)))
  suff namefst
=
 let open Proofview.Notations in
 Ssrcommon.tacMK_SSR_CONST "abstract_key" >>= fun abstract_key ->
 Ssrcommon.tacMK_SSR_CONST "abstract" >>= fun abstract ->
 Proofview.Goal.enter begin fun gl ->
 let concl = Proofview.Goal.concl gl in
 let gstate = Proofview.Goal.state gl in
 let pats = tclCompileIPats orig_pats in
 let binders = tclCompileIPats binders in
 let simpl = tclCompileIPats simpl in
 let skols, pats =
   List.partition (function IOpAbstractVars _ -> true | _ -> false) pats in
 let itac_mkabs = introstac skols in
 let itac_c, clr =
   match clr with
   | None -> introstac pats, []
   | Some clr -> introstac (tclCompileIPats (IPatClear clr :: orig_pats)), clr in
 let itac, clr = introstac pats, cleartac clr in
 let binderstac n =
   let rec aux = function 0 -> [] | n -> IOpInaccessible None :: aux (n-1) in
   Tacticals.tclTHEN (if binders <> [] then introstac (aux n) else Tacticals.tclIDTAC)
     (introstac binders) in
 let simpltac = introstac simpl in
 let fixtc =
   not !ssrhaveNOtcresolution &&
   match fk with FwdHint(_,true) -> false | _ -> true in
 let hint = hinttac ist true hint in
 let cuttac t = basecuttac (if transp then HaveTransp else Have) t in
 (* Introduce now abstract constants, so that everything sees them *)
 let unlock_abs env (idty,args_id) sigma =
    let sigma, _ = Typing.type_of env sigma idty in
    unify_HO env sigma args_id.(2) abstract_key
 in
 drop_state <*>
 Tacticals.tclTHENFIRST itac_mkabs (Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let interp sigma rtc t =
    abs_ssrterm ~resolve_typeclasses:rtc ist env sigma t
  in
  let ct, cty, hole, loc = make_ct t in
  let sigma, cut, itac1, itac2 =
   match fk, namefst, suff with
   | FwdHave, true, true ->
     errorstrm (str"Suff have does not accept a proof term")
   | FwdHave, false, true ->
     let cty = combineCG cty hole (mkCArrow ?loc) mkRArrow in
     let sigma, t, _ = interp sigma false (combineCG ct cty (mkCCast ?loc) mkRCast) in
     let sigma, ty = Typing.type_of env sigma t in
     let ctx, _ = EConstr.decompose_prod_n_decls sigma 1 ty in
     sigma, ty, assert_is_conv (ctx, concl) <*> Tactics.apply t, itac_c
   | FwdHave, false, false ->
     let skols = List.flatten (List.map (function
       | IOpAbstractVars ids -> ids
       | _ -> assert false) skols) in
     let skols_args =
       List.map (fun id -> snd @@ (* FIXME: evar leak *)
         Ssripats.Internal.examine_abstract env sigma (EConstr.mkVar id)) skols in
     let sigma = List.fold_right (unlock_abs env) skols_args sigma in
     let sigma, t, n_evars =
       interp sigma false (combineCG ct cty (mkCCast ?loc) mkRCast) in
     if skols <> [] && n_evars <> 0 then
       CErrors.user_err (Pp.strbrk @@ "Automatic generalization of unresolved implicit "^
                     "arguments together with abstract variables is "^
                     "not supported");
     let gs =
       List.map (fun (_,a) ->
         Ssripats.Internal.find_abstract_proof env sigma false a.(1)) skols_args in
     let tacopen_skols = push_goals gs in
     let sigma, ty = Typing.type_of env sigma t in
     sigma, ty, Tactics.apply t,
       itac_c <*> simpltac <*> tacopen_skols <*> unfold [abstract; abstract_key]
   | _,true,true  ->
     let sigma, _, ty, _ = pf_interp_ty ~resolve_typeclasses:fixtc env sigma ist cty in
     sigma, EConstr.mkArrow ty ERelevance.relevant concl, hint <*> itac, clr
   | _,false,true ->
     let sigma, _, ty, _ = pf_interp_ty ~resolve_typeclasses:fixtc env sigma ist cty in
     sigma, EConstr.mkArrow ty ERelevance.relevant concl, hint, itac_c
   | _, false, false ->
     let sigma, n, cty, _  = pf_interp_ty ~resolve_typeclasses:fixtc env sigma ist cty in
     sigma, cty, (binderstac n) <*> hint, Tacticals.tclTHEN itac_c simpltac
   | _, true, false -> assert false in
  Proofview.Unsafe.tclEVARS sigma <*>
  Tacticals.tclTHENS (cuttac cut) [ itac1; itac2 ] end) <*>
  set_state gstate
end

let destProd_or_LetIn sigma c =
  match EConstr.kind sigma c with
  | Prod (n,ty,c) -> RelDecl.LocalAssum (n, ty), c
  | LetIn (n,bo,ty,c) -> RelDecl.LocalDef (n, bo, ty), c
  | _ -> raise DestKO

let wlogtac ist (((clr0, pats),_),_) (gens, ((_, ct))) hint suff ghave =
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let concl = Proofview.Goal.concl gl in
  let clr0 = Option.default [] clr0 in
  let pats = tclCompileIPats pats in
  let mkclr gen clrs = clr_of_wgen gen clrs in
  let mkpats = function
  | _, Some ((x, _), _) -> fun pats -> IOpId (hoi_id x) :: pats
  | _ -> fun x -> x in
  let ct = match Ssrcommon.ssrterm_of_ast_closure_term ct with
  | (a, (b, Some ct)) ->
    begin match ct.CAst.v with
    | CCast (_, Some DEFAULTcast, cty) -> a, (b, Some cty)
    | _ -> anomaly "wlog: ssr cast hole deleted by typecheck"
    end
  | (a, (t, None)) ->
    begin match DAst.get t with
    | GCast (_, Some DEFAULTcast, cty) -> a, (cty, None)
    | _ -> anomaly "wlog: ssr cast hole deleted by typecheck"
    end
  in
  let cut_implies_goal = not (suff || ghave <> `NoGen) in
  let c, args, ct, sigma =
    let gens = List.filter (function _, Some _ -> true | _ -> false) gens in
    let c = EConstr.mkProp in
    let c = if cut_implies_goal then EConstr.mkArrow c ERelevance.relevant concl else c in
    let mkabs gen (sigma, args, c) =
      abs_wgen env sigma false (fun x -> x) gen (args, c)
    in
    let sigma, args, c = List.fold_right mkabs gens (sigma, [], c) in
    let env, _ =
      List.fold_left (fun (env, c) _ ->
        let rd, c = destProd_or_LetIn sigma c in
        EConstr.push_rel rd env, c) (env, c) gens in
    let sigma, _, ct, _ = pf_interp_ty env sigma ist ct in
    let rec var2rel c g s = match EConstr.kind sigma c, g with
      | Prod({binder_name=Anonymous} as x,_,c), [] -> EConstr.mkProd(x, EConstr.Vars.subst_vars sigma s ct, c)
      | Sort _, [] -> EConstr.Vars.subst_vars sigma s ct
      | LetIn({binder_name=Name id} as n,b,ty,c), _::g -> EConstr.mkLetIn (n,b,ty,var2rel c g (id::s))
      | Prod({binder_name=Name id} as n,ty,c), _::g -> EConstr.mkProd (n,ty,var2rel c g (id::s))
      | _ -> CErrors.anomaly(str"SSR: wlog: var2rel: " ++ pr_econstr_env env sigma c) in
    let c = var2rel c gens [] in
    let rec pired c = function
      | [] -> c
      | t::ts as args -> match EConstr.kind sigma c with
         | Prod(_,_,c) -> pired (EConstr.Vars.subst1 t c) ts
         | LetIn(id,b,ty,c) -> EConstr.mkLetIn (id,b,ty,pired c args)
         | _ -> CErrors.anomaly(str"SSR: wlog: pired: " ++ pr_econstr_env env sigma c) in
    c, args, pired c args, sigma
  in
  let tacipat pats = introstac pats in
  let tacigens =
    Tacticals.tclTHEN
      (Tacticals.tclTHENLIST(List.rev(List.fold_right mkclr gens [cleartac clr0])))
      (introstac (List.fold_right mkpats gens [])) in
  let hinttac = hinttac ist true hint in
  let cut_kind, fst_goal_tac, snd_goal_tac =
    match suff, ghave with
    | true, `NoGen -> Suff, Tacticals.tclTHEN hinttac (tacipat pats), tacigens
    | false, `NoGen -> Suff, hinttac, Tacticals.tclTHEN tacigens (tacipat pats)
    | true, `Gen _ -> assert false
    | false, `Gen id ->
      if gens = [] then errorstrm(str"gen have requires some generalizations");
      let clear0 = cleartac clr0 in
      let id, name_general_hyp, cleanup, pats = match id, pats with
      | None, (IOpId id as ip)::pats -> Some id, tacipat [ip], clear0, pats
      | None, _ -> None, Tacticals.tclIDTAC, clear0, pats
      | Some (Some id),_ -> Some id, introid id, clear0, pats
      | Some _,_ ->
          let id = mk_anon_id "tmp" (Tacmach.pf_ids_of_hyps gl) in
          Some id, introid id, Tacticals.tclTHEN clear0 (Tactics.clear [id]), pats in
      let tac_specialize = match id with
      | None -> Tacticals.tclIDTAC
      | Some id ->
        if pats = [] then Tacticals.tclIDTAC else
        let args = Array.of_list args in
        debug_ssr (fun () -> str"specialized="++ pr_econstr_env env sigma EConstr.(mkApp (mkVar id,args)));
        debug_ssr (fun () -> str"specialized_ty="++ pr_econstr_env env sigma ct);
        Tacticals.tclTHENS (basecuttac Have ct)
          [Tactics.apply EConstr.(mkApp (mkVar id,args)); Tacticals.tclIDTAC] in
      Have,
      (if hint = nohint then tacigens else hinttac),
      Tacticals.tclTHENLIST [name_general_hyp; tac_specialize; tacipat pats; cleanup]
  in
  Proofview.Unsafe.tclEVARS sigma <*>
  Tacticals.tclTHENS (basecuttac cut_kind c) [fst_goal_tac; snd_goal_tac]
  end

(** The "suffice" tactic *)

open Proofview.Notations

let sufftac ist ((((clr, pats),binders),simpl), ((_, c), hint)) =
  let clr = Option.default [] clr in
  let pats = tclCompileIPats pats in
  let binders = tclCompileIPats binders in
  let simpl = tclCompileIPats simpl in
  let htac = Tacticals.tclTHEN (introstac pats) (hinttac ist true hint) in
  let c = match Ssrcommon.ssrterm_of_ast_closure_term c with
  | (a, (b, Some ct)) ->
    begin match ct.CAst.v with
    | CCast (_, Some DEFAULTcast, cty) -> a, (b, Some cty)
    | _ -> anomaly "suff: ssr cast hole deleted by typecheck"
    end
  | (a, (t, None)) ->
    begin match DAst.get t with
    | GCast (_, Some DEFAULTcast, cty) -> a, (cty, None)
    | _ -> anomaly "suff: ssr cast hole deleted by typecheck"
    end
  in
  let ctac =
    let open Tacmach in
    Proofview.Goal.enter begin fun gl ->
    let sigma, _, ty, _ = pf_interp_ty (pf_env gl) (project gl) ist c in
    Proofview.Unsafe.tclEVARS sigma <*> basesufftac ty
  end in
  Tacticals.tclTHENS ctac [htac; Tacticals.tclTHEN (cleartac clr) (introstac (binders@simpl))]

let is_app_evar sigma t =
  match EConstr.kind sigma t with
  | Constr.Evar _ -> true
  | Constr.App(t,_) ->
      begin match EConstr.kind sigma t with
      | Constr.Evar _ -> true
      | _ -> false end
  | _ -> false

let rec ncons n e = match n with
  | 0 -> []
  | n when n > 0 -> e :: ncons (n - 1) e
  | _ -> failwith "ncons"

let intro_lock ipats =
  let hnf' = Proofview.numgoals >>= fun ng ->
             Proofview.tclDISPATCH
               (ncons (ng - 1) ssrsmovetac @ [Proofview.tclUNIT ()]) in
  let protect_subgoal env sigma hd args =
    Ssrcommon.tacMK_SSR_CONST "Under_rel" >>= fun under_rel ->
    Ssrcommon.tacMK_SSR_CONST "Under_rel_from_rel" >>= fun under_from_rel ->
    Tactics.refine ~typecheck:true (fun sigma ->
        let lm2 = Array.length args - 2 in
        let sigma, carrier =
          Typing.type_of env sigma args.(lm2) in
        let rel = EConstr.mkApp (hd, Array.sub args 0 lm2) in
        let rel_args = Array.sub args lm2 2 in
        let under_rel_args = Array.append [|carrier; rel|] rel_args in
        let ty = EConstr.mkApp (under_rel, under_rel_args) in
        let sigma, t = Evarutil.new_evar env sigma ty in
        sigma, EConstr.mkApp(under_from_rel,Array.append under_rel_args [|t|])) in
  let rec lock_eq () : unit Proofview.tactic = Proofview.Goal.enter begin fun _ ->
    Proofview.tclORELSE
      (Ssripats.tclIPAT [Ssripats.IOpTemporay; Ssripats.IOpEqGen (lock_eq ())])
      (fun _exn -> Proofview.Goal.enter begin fun gl ->
        let c = Proofview.Goal.concl gl in
        let sigma = Proofview.Goal.sigma gl in
        let env = Proofview.Goal.env gl in
        let open EConstr in
        match kind_of_type sigma c with
        | AtomicType(hd, args) when
            Array.length args >= 2 && is_app_evar sigma (Array.last args) &&
            Ssrequality.ssr_is_setoid env sigma hd args
            (* if the last condition above [ssr_is_setoid ...] holds
            then [Corelib.Classes.RelationClasses] has been required *)
            ||
            (* if this is not the case, the tactic can still succeed
            when the considered relation is [Corelib.Init.Logic.iff] *)
            Ssrcommon.is_const_ref env sigma hd (Rocqlib.lib_ref "core.iff.type") &&
            Array.length args = 2 && is_app_evar sigma args.(1) ->
          protect_subgoal env sigma hd args
        | _ ->
        let t = Reductionops.whd_all env sigma c in
        match kind_of_type sigma t with
        | AtomicType(hd, args) when
            Ssrcommon.is_ind_ref env sigma hd (Rocqlib.lib_ref "core.eq.type") &&
            Array.length args = 3 && is_app_evar sigma args.(2) ->
          protect_subgoal env sigma hd args
        | _ ->
    debug_ssr (fun () -> Pp.(str"under: stop:" ++ pr_econstr_env env sigma t));

            Proofview.tclUNIT ()
       end)
    end
  in
  hnf' <*> Ssripats.tclIPATssr ipats <*> lock_eq ()

let pretty_rename evar_map term varnames =
  let rec aux term vars =
    try
      match vars with
      | [] -> term
      | Names.Name.Anonymous :: varnames ->
          let name, types, body = EConstr.destLambda evar_map term in
          let res = aux body varnames in
          EConstr.mkLambda (name, types, res)
      | Names.Name.Name _ as name :: varnames ->
          let { Context.binder_relevance = r }, types, body =
            EConstr.destLambda evar_map term in
          let res = aux body varnames in
          EConstr.mkLambda (Context.make_annot name r, types, res)
    with DestKO -> term
  in
    aux term varnames

let overtac = ssr_n_tac "over" ~-1

let check_numgoals ?(minus = 0) nh =
  Proofview.numgoals >>= fun ng ->
  if nh <> ng then
    let errmsg =
      str"Incorrect number of tactics" ++ spc() ++
        str"(expected "++int (ng - minus)++str(String.plural ng " tactic") ++
        str", was given "++ int (nh - minus)++str")."
    in
    CErrors.user_err errmsg
  else
    Proofview.tclUNIT ()

let undertac ?(pad_intro = false) ist ipats ((dir,_),_ as rule) hint =

  (* total number of implied hints *)
  let nh = List.length (snd hint) + (if hint = nullhint then 2 else 1) in

  let varnames =
    let rec aux acc = function
      | IPatId id :: rest -> aux (Names.Name.Name id :: acc) rest
      | IPatClear _ :: rest -> aux acc rest
      | IPatSimpl _ :: rest -> aux acc rest
      | IPatAnon (One _ | Drop) :: rest ->
          aux (Names.Name.Anonymous :: acc) rest
      | _ -> List.rev acc in
    aux [] @@ match ipats with
              | None -> []
              | Some (IPatCase(Regular (l :: _)) :: _) -> l
              | Some l -> l in

  (* If we find a "=> [|]" we add 1 | to get "=> [||]" for the extra
   * goal (the one that is left once we run over) *)
  let ipats =
    match ipats with
    | None -> [IPatNoop]
    | Some l when pad_intro -> (* typically, ipats = Some [IPatAnon All] *)
       let new_l = ncons (nh - 1) l in
       [IPatCase(Regular (new_l @ [[]]))]
    | Some (IPatCase(Regular []) :: _ as ipats) -> ipats
    (* Erik: is the previous line correct/useful? *)
    | Some (IPatCase(Regular l) :: rest) -> IPatCase(Regular(l @ [[]])) :: rest
    | Some (IPatCase(Block _) :: _ as l) -> l
    | Some l -> [IPatCase(Regular [l;[]])] in

  let map_redex env evar_map ~before:_ ~after:t =
    debug_ssr (fun () -> Pp.(str"under vars: " ++ prlist Names.Name.print varnames));

    let evar_map, ty = Typing.type_of env evar_map t in
    let new_t = (* pretty-rename the bound variables *)
      try begin match EConstr.destApp evar_map t with (f, ar) ->
            let lam = Array.last ar in
            debug_ssr(fun () -> Pp.(str"under: mapping:" ++
                             pr_econstr_env env evar_map lam));
            let new_lam = pretty_rename evar_map lam varnames in
            let new_ar, len1 = Array.copy ar, pred (Array.length ar) in
            new_ar.(len1) <- new_lam;
            EConstr.mkApp (f, new_ar)
          end with
      | DestKO ->
        debug_ssr (fun () -> Pp.(str"under: cannot pretty-rename bound variables with destApp"));
        t
    in
    debug_ssr (fun () -> Pp.(str"under: to:" ++ pr_econstr_env env evar_map new_t));
    evar_map, new_t
  in
  let undertacs =
    if hint = nohint then
      Proofview.tclUNIT ()
    else
      let betaiota = Tactics.reduct_in_concl ~cast:false ~check:false
          (Reductionops.nf_betaiota, DEFAULTcast)
      in
      (* Usefulness of check_numgoals: tclDISPATCH would be enough,
         except for the error message w.r.t. the number of
         provided/expected tactics, as the last one is implied *)
      check_numgoals ~minus:1 nh <*>
        Proofview.tclDISPATCH
          ((List.map (function None -> overtac
                             | Some e -> ssrevaltac ist e <*>
                                           overtac)
              (if hint = nullhint then [None] else snd hint))
           @ [betaiota])
  in
  let rew =
    Ssrequality.ssrrewritetac ~under:true ~map_redex ist [rule]
  in
  rew <*> intro_lock ipats <*> undertacs
