(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* This file is (C) Copyright 2006-2015 Microsoft Corporation and Inria. *)

open Names
open Tacmach

open Ssrmatching_plugin.Ssrmatching

open Ssrprinters
open Ssrcommon
open Ssrtacticals

module RelDecl = Context.Rel.Declaration

(** 8. Forward chaining tactics (pose, set, have, suffice, wlog) *)
(** Defined identifier *)


let settac id c = Tactics.letin_tac None (Name id) c None
let posetac id cl = Proofview.V82.of_tactic (settac id cl Locusops.nowhere)

let ssrposetac ist (id, (_, t)) gl =
  let sigma, t, ucst, _ = pf_abs_ssrterm ist gl t in
  posetac id t (pf_merge_uc ucst gl)

open Pp
open Term

let ssrsettac ist id ((_, (pat, pty)), (_, occ)) gl =
  let pat = interp_cpattern ist gl pat (Option.map snd pty) in
  let cl, sigma, env = pf_concl gl, project gl, pf_env gl in
  let (c, ucst), cl = 
    let cl = EConstr.Unsafe.to_constr cl in
    try fill_occ_pattern ~raise_NoMatch:true env sigma cl pat occ 1
    with NoMatch -> redex_of_pattern ~resolve_typeclasses:true env pat, cl in
  let c = EConstr.of_constr c in
  let cl = EConstr.of_constr cl in
  if Termops.occur_existential sigma c then errorstrm(str"The pattern"++spc()++
    pr_constr_pat (EConstr.Unsafe.to_constr c)++spc()++str"did not match and has holes."++spc()++
    str"Did you mean pose?") else
  let c, (gl, cty) =  match EConstr.kind sigma c with
  | Cast(t, DEFAULTcast, ty) -> t, (gl, ty)
  | _ -> c, pfe_type_of gl c in
  let cl' = EConstr.mkLetIn (Name id, c, cty, cl) in
  let gl = pf_merge_uc ucst gl in
  Tacticals.tclTHEN (Proofview.V82.of_tactic (convert_concl cl')) (introid id) gl

open Util

let rec is_Evar_or_CastedMeta sigma x =
  EConstr.isEvar sigma x || EConstr.isMeta sigma x ||
  (EConstr.isCast sigma x && is_Evar_or_CastedMeta sigma (pi1 (EConstr.destCast sigma x)))

let occur_existential_or_casted_meta c =
  let rec occrec c = match kind_of_term c with
    | Evar _ -> raise Not_found
    | Cast (m,_,_) when isMeta m -> raise Not_found
    | _ -> iter_constr occrec c
  in try occrec c; false with Not_found -> true

open Printer

let examine_abstract id gl =
  let gl, tid = pfe_type_of gl id in
  let abstract, gl = pf_mkSsrConst "abstract" gl in
  let sigma = project gl in
  if not (EConstr.isApp sigma tid) || not (EConstr.eq_constr sigma (fst(EConstr.destApp sigma tid)) abstract) then
    errorstrm(strbrk"not an abstract constant: "++pr_econstr id);
  let _, args_id = EConstr.destApp sigma tid in
  if Array.length args_id <> 3 then
    errorstrm(strbrk"not a proper abstract constant: "++pr_econstr id);
  if not (is_Evar_or_CastedMeta sigma args_id.(2)) then
    errorstrm(strbrk"abstract constant "++pr_econstr id++str" already used");
  tid, args_id

let pf_find_abstract_proof check_lock gl abstract_n = 
  let fire gl t = EConstr.Unsafe.to_constr (Reductionops.nf_evar (project gl) (EConstr.of_constr t)) in
  let abstract, gl = pf_mkSsrConst "abstract" gl in
  let l = Evd.fold_undefined (fun e ei l ->
    match kind_of_term ei.Evd.evar_concl with
    | App(hd, [|ty; n; lock|])
      when (not check_lock || 
                 (occur_existential_or_casted_meta  (fire gl ty) &&
                  is_Evar_or_CastedMeta (project gl) (EConstr.of_constr @@ fire gl lock))) &&
      Term.eq_constr hd (EConstr.Unsafe.to_constr abstract) && Term.eq_constr n abstract_n -> e::l
    | _ -> l) (project gl) [] in
  match l with
  | [e] -> e
  | _ -> errorstrm(strbrk"abstract constant "++pr_constr abstract_n++
           strbrk" not found in the evar map exactly once. "++
           strbrk"Did you tamper with it?")

let reduct_in_concl t = Tactics.reduct_in_concl (t, DEFAULTcast)
let unfold cl =
  let module R = Reductionops in let module F = CClosure.RedFlags in
  reduct_in_concl (R.clos_norm_flags (F.mkflags
    (List.map (fun c -> F.fCONST (fst (destConst (EConstr.Unsafe.to_constr c)))) cl @
       [F.fBETA; F.fMATCH; F.fFIX; F.fCOFIX])))

open Ssrast
open Ssripats

let ssrhaveNOtcresolution = Summary.ref ~name:"SSR:havenotcresolution" false

let inHaveTCResolution = Libobject.declare_object {
  (Libobject.default_object "SSRHAVETCRESOLUTION") with
  Libobject.cache_function = (fun (_,v) -> ssrhaveNOtcresolution := v);
  Libobject.load_function = (fun _ (_,v) -> ssrhaveNOtcresolution := v);
  Libobject.classify_function = (fun v -> Libobject.Keep v);
}
let _ =
  Goptions.declare_bool_option
    { Goptions.optname  = "have type classes";
      Goptions.optkey   = ["SsrHave";"NoTCResolution"];
      Goptions.optread  = (fun _ -> !ssrhaveNOtcresolution);
      Goptions.optdepr  = false;
      Goptions.optwrite = (fun b ->
        Lib.add_anonymous_leaf (inHaveTCResolution b)) }


open Constrexpr 
open Glob_term 
open Misctypes

let combineCG t1 t2 f g = match t1, t2 with
 | (x, (t1, None)), (_, (t2, None)) -> x, (g t1 t2, None)
 | (x, (_, Some t1)), (_, (_, Some t2)) -> x, (mkRHole, Some (f t1 t2))
 | _, (_, (_, None)) -> anomaly "have: mixed C-G constr"
 | _ -> anomaly "have: mixed G-C constr"

let basecuttac name c gl =
  let hd, gl = pf_mkSsrConst name gl in
  let t = EConstr.mkApp (hd, [|c|]) in
  let gl, _ = pf_e_type_of gl t in
  Proofview.V82.of_tactic (Tactics.apply t) gl

let havetac ist
  (transp,((((clr, pats), binders), simpl), (((fk, _), t), hint)))
  suff namefst gl 
=
 let concl = pf_concl gl in
 let skols, pats =
   List.partition (function IPatNewHidden _ -> true | _ -> false) pats in
 let itac_mkabs = introstac ~ist skols in
 let itac_c = introstac ~ist (IPatClear clr :: pats) in
 let itac, id, clr = introstac ~ist pats, Tacticals.tclIDTAC, cleartac clr in
 let binderstac n =
   let rec aux = function 0 -> [] | n -> IPatAnon One :: aux (n-1) in
   Tacticals.tclTHEN (if binders <> [] then introstac ~ist (aux n) else Tacticals.tclIDTAC)
     (introstac ~ist binders) in
 let simpltac = introstac ~ist simpl in
 let fixtc =
   not !ssrhaveNOtcresolution &&
   match fk with FwdHint(_,true) -> false | _ -> true in
 let hint = hinttac ist true hint in
 let cuttac t gl =
   if transp then
     let have_let, gl = pf_mkSsrConst "ssr_have_let" gl in
     let step = EConstr.mkApp (have_let, [|concl;t|]) in
     let gl, _ = pf_e_type_of gl step in
     applyn ~with_evars:true ~with_shelve:false 2 step gl
   else basecuttac "ssr_have" t gl in
 (* Introduce now abstract constants, so that everything sees them *)
 let abstract_key, gl = pf_mkSsrConst "abstract_key" gl in
 let unlock_abs (idty,args_id) gl =
    let gl, _ = pf_e_type_of gl idty in
    pf_unify_HO gl args_id.(2) abstract_key in
 Tacticals.tclTHENFIRST itac_mkabs (fun gl ->
  let mkt t = mk_term xNoFlag t in
  let mkl t = (xNoFlag, (t, None)) in
  let interp gl rtc t = pf_abs_ssrterm ~resolve_typeclasses:rtc ist gl t in
  let interp_ty gl rtc t =
    let a,b,_,u = pf_interp_ty ~resolve_typeclasses:rtc ist gl t in a,b,u in
  let open CAst in
  let ct, cty, hole, loc = match t with
    | _, (_, Some { loc; v = CCast (ct, CastConv cty)}) ->
      mkt ct, mkt cty, mkt (mkCHole None), loc
    | _, (_, Some ct) ->
      mkt ct, mkt (mkCHole None), mkt (mkCHole None), None
    | _, ({ loc; v = GCast (ct, CastConv cty) }, None) ->
      mkl ct, mkl cty, mkl mkRHole, loc
    | _, (t, None) -> mkl t, mkl mkRHole, mkl mkRHole, None in
  let gl, cut, sol, itac1, itac2 =
   match fk, namefst, suff with
   | FwdHave, true, true ->
     errorstrm (str"Suff have does not accept a proof term")
   | FwdHave, false, true ->
     let cty = combineCG cty hole (mkCArrow ?loc) mkRArrow in
     let _,t,uc,_ = interp gl false (combineCG ct cty (mkCCast ?loc) mkRCast) in
     let gl = pf_merge_uc uc gl in
     let gl, ty = pfe_type_of gl t in
     let ctx, _ = EConstr.decompose_prod_n_assum (project gl) 1 ty in
     let assert_is_conv gl =
       try Proofview.V82.of_tactic (convert_concl (EConstr.it_mkProd_or_LetIn concl ctx)) gl
       with _ -> errorstrm (str "Given proof term is not of type " ++
         pr_econstr (EConstr.mkArrow (EConstr.mkVar (Id.of_string "_")) concl)) in
     gl, ty, Tacticals.tclTHEN assert_is_conv (Proofview.V82.of_tactic (Tactics.apply t)), id, itac_c
   | FwdHave, false, false ->
     let skols = List.flatten (List.map (function
       | IPatNewHidden ids -> ids
       | _ -> assert false) skols) in
     let skols_args =
       List.map (fun id -> examine_abstract (EConstr.mkVar id) gl) skols in
     let gl = List.fold_right unlock_abs skols_args gl in
     let sigma, t, uc, n_evars =
       interp gl false (combineCG ct cty (mkCCast ?loc) mkRCast) in
     if skols <> [] && n_evars <> 0 then
       CErrors.user_err (Pp.strbrk @@ "Automatic generalization of unresolved implicit "^
                     "arguments together with abstract variables is "^
                     "not supported");
     let gl = re_sig (sig_it gl) (Evd.merge_universe_context sigma uc) in
     let gs =
       List.map (fun (_,a) ->
         pf_find_abstract_proof false gl (EConstr.Unsafe.to_constr a.(1))) skols_args in
     let tacopen_skols gl =
        let stuff, g = Refiner.unpackage gl in
        Refiner.repackage stuff (gs @ [g]) in
     let gl, ty = pf_e_type_of gl t in
     gl, ty, Proofview.V82.of_tactic (Tactics.apply t), id,
       Tacticals.tclTHEN (Tacticals.tclTHEN itac_c simpltac)
         (Tacticals.tclTHEN tacopen_skols (fun gl ->
            let abstract, gl = pf_mkSsrConst "abstract" gl in
            Proofview.V82.of_tactic (unfold [abstract; abstract_key]) gl))
   | _,true,true  ->
     let _, ty, uc = interp_ty gl fixtc cty in let gl = pf_merge_uc uc gl in
     gl, EConstr.mkArrow ty concl, hint, itac, clr
   | _,false,true ->
     let _, ty, uc = interp_ty gl fixtc cty in let gl = pf_merge_uc uc gl in
     gl, EConstr.mkArrow ty concl, hint, id, itac_c
   | _, false, false -> 
     let n, cty, uc = interp_ty gl fixtc cty in let gl = pf_merge_uc uc gl in
     gl, cty, Tacticals.tclTHEN (binderstac n) hint, id, Tacticals.tclTHEN itac_c simpltac
   | _, true, false -> assert false in
  Tacticals.tclTHENS (cuttac cut) [ Tacticals.tclTHEN sol itac1; itac2 ] gl)
 gl
;;

(* to extend the abstract value one needs:
  Utility lemma to partially instantiate an abstract constant type.
  Lemma use_abstract T n l (x : abstract T n l) : T.
  Proof. by case: l x. Qed.
*)
let ssrabstract ist gens (*last*) gl =
  let main _ (_,cid) ist gl =
(*
    let proj1, proj2, prod =
      let pdata = build_prod () in
      pdata.Coqlib.proj1, pdata.Coqlib.proj2, pdata.Coqlib.typ in
*)
    let concl, env = pf_concl gl, pf_env gl in
    let fire gl t = Reductionops.nf_evar (project gl) t in
    let abstract, gl = pf_mkSsrConst "abstract" gl in
    let abstract_key, gl = pf_mkSsrConst "abstract_key" gl in
    let cid_interpreted = interp_cpattern ist gl cid None in
    let id = EConstr.mkVar (Option.get (id_of_pattern cid_interpreted)) in
    let idty, args_id = examine_abstract id gl in
    let abstract_n = args_id.(1) in
    let abstract_proof = pf_find_abstract_proof true gl (EConstr.Unsafe.to_constr abstract_n) in 
    let gl, proof =
      let pf_unify_HO gl a b =
        try pf_unify_HO gl a b
        with _ -> errorstrm(strbrk"The abstract variable "++pr_econstr id++
          strbrk" cannot abstract this goal.  Did you generalize it?") in
      let find_hole p t =
        match EConstr.kind (project gl) t with
        | Evar _ (*when last*) -> pf_unify_HO gl concl t, p
        | Meta _ (*when last*) -> pf_unify_HO gl concl t, p
        | Cast(m,_,_) when EConstr.isEvar (project gl) m || EConstr.isMeta
          (project gl) m (*when last*) -> pf_unify_HO gl concl t, p
(*
        | Evar _ ->
            let sigma, it = project gl, sig_it gl in
            let sigma, ty = Evarutil.new_type_evar sigma env in
            let gl = re_sig it sigma in
            let p = mkApp (proj2,[|ty;concl;p|]) in
            let concl = mkApp(prod,[|ty; concl|]) in
            pf_unify_HO gl concl t, p
        | App(hd, [|left; right|]) when Term.eq_constr hd prod ->
            find_hole (mkApp (proj1,[|left;right;p|])) left
*)
        | _ -> errorstrm(strbrk"abstract constant "++pr_econstr abstract_n++
               strbrk" has an unexpected shape. Did you tamper with it?")
      in
        find_hole
          ((*if last then*) id
          (*else mkApp(mkSsrConst "use_abstract",Array.append args_id [|id|])*))
          (fire gl args_id.(0)) in
    let gl = (*if last then*) pf_unify_HO gl abstract_key args_id.(2) (*else gl*) in
    let gl, _ = pf_e_type_of gl idty in
    let proof = fire gl proof in
(*     if last then *)
      let tacopen gl =
        let stuff, g = Refiner.unpackage gl in
        Refiner.repackage stuff [ g; abstract_proof ] in
      Tacticals.tclTHENS tacopen [Tacticals.tclSOLVE [Proofview.V82.of_tactic (Tactics.apply proof)]; Proofview.V82.of_tactic (unfold[abstract;abstract_key])] gl
(* else apply proof gl *)
  in
  let introback ist (gens, _) =
    introstac ~ist
      (List.map (fun (_,cp) -> match id_of_pattern (interp_cpattern ist gl cp None) with
        | None -> IPatAnon One
        | Some id -> IPatId id)
        (List.tl (List.hd gens))) in
  Tacticals.tclTHEN (with_dgens gens main ist) (introback ist gens) gl


let destProd_or_LetIn sigma c =
  match EConstr.kind sigma c with
  | Prod (n,ty,c) -> RelDecl.LocalAssum (n, ty), c
  | LetIn (n,bo,ty,c) -> RelDecl.LocalDef (n, bo, ty), c
  | _ -> raise DestKO

let wlogtac ist (((clr0, pats),_),_) (gens, ((_, ct))) hint suff ghave gl =
  let mkabs gen = abs_wgen false ist (fun x -> x) gen in
  let mkclr gen clrs = clr_of_wgen gen clrs in
  let mkpats = function
  | _, Some ((x, _), _) -> fun pats -> IPatId (hoi_id x) :: pats
  | _ -> fun x -> x in
  let open CAst in
  let ct = match ct with
  | (a, (b, Some { v = CCast (_, CastConv cty)})) -> a, (b, Some cty)
  | (a, ({ v = GCast (_, CastConv cty) }, None)) -> a, (cty, None)
  | _ -> anomaly "wlog: ssr cast hole deleted by typecheck" in
  let cut_implies_goal = not (suff || ghave <> `NoGen) in
  let c, args, ct, gl =
    let gens = List.filter (function _, Some _ -> true | _ -> false) gens in
    let concl = pf_concl gl in
    let c = EConstr.mkProp in
    let c = if cut_implies_goal then EConstr.mkArrow c concl else c in
    let gl, args, c = List.fold_right mkabs gens (gl,[],c) in
    let env, _ =
      List.fold_left (fun (env, c) _ ->
        let rd, c = destProd_or_LetIn (project gl) c in
        EConstr.push_rel rd env, c) (pf_env gl, c) gens in
    let sigma = project gl in
    let (sigma, ev) = Evarutil.new_evar env sigma EConstr.mkProp in
    let k, _ = EConstr.destEvar sigma ev in
    let fake_gl = {Evd.it = k; Evd.sigma = sigma} in
    let _, ct, _, uc = pf_interp_ty ist fake_gl ct in
    let rec var2rel c g s = match EConstr.kind sigma c, g with
      | Prod(Anonymous,_,c), [] -> EConstr.mkProd(Anonymous, EConstr.Vars.subst_vars s ct, c)
      | Sort _, [] -> EConstr.Vars.subst_vars s ct
      | LetIn(Name id as n,b,ty,c), _::g -> EConstr.mkLetIn (n,b,ty,var2rel c g (id::s))
      | Prod(Name id as n,ty,c), _::g -> EConstr.mkProd (n,ty,var2rel c g (id::s))
      | _ -> CErrors.anomaly(str"SSR: wlog: var2rel: " ++ pr_econstr c) in
    let c = var2rel c gens [] in
    let rec pired c = function
      | [] -> c
      | t::ts as args -> match EConstr.kind sigma c with
         | Prod(_,_,c) -> pired (EConstr.Vars.subst1 t c) ts
         | LetIn(id,b,ty,c) -> EConstr.mkLetIn (id,b,ty,pired c args)
         | _ -> CErrors.anomaly(str"SSR: wlog: pired: " ++ pr_econstr c) in
    c, args, pired c args, pf_merge_uc uc gl in
  let tacipat pats = introstac ~ist pats in
  let tacigens = 
    Tacticals.tclTHEN
      (Tacticals.tclTHENLIST(List.rev(List.fold_right mkclr gens [cleartac clr0])))
      (introstac ~ist (List.fold_right mkpats gens [])) in
  let hinttac = hinttac ist true hint in
  let cut_kind, fst_goal_tac, snd_goal_tac =
    match suff, ghave with
    | true, `NoGen -> "ssr_wlog", Tacticals.tclTHEN hinttac (tacipat pats), tacigens
    | false, `NoGen -> "ssr_wlog", hinttac, Tacticals.tclTHEN tacigens (tacipat pats)
    | true, `Gen _ -> assert false
    | false, `Gen id ->
      if gens = [] then errorstrm(str"gen have requires some generalizations");
      let clear0 = cleartac clr0 in
      let id, name_general_hyp, cleanup, pats = match id, pats with
      | None, (IPatId id as ip)::pats -> Some id, tacipat [ip], clear0, pats
      | None, _ -> None, Tacticals.tclIDTAC, clear0, pats
      | Some (Some id),_ -> Some id, introid id, clear0, pats
      | Some _,_ ->
          let id = mk_anon_id "tmp" gl in
          Some id, introid id, Tacticals.tclTHEN clear0 (Proofview.V82.of_tactic (Tactics.clear [id])), pats in
      let tac_specialize = match id with
      | None -> Tacticals.tclIDTAC
      | Some id ->
        if pats = [] then Tacticals.tclIDTAC else
        let args = Array.of_list args in
        ppdebug(lazy(str"specialized="++pr_econstr EConstr.(mkApp (mkVar id,args))));
        ppdebug(lazy(str"specialized_ty="++pr_econstr ct));
        Tacticals.tclTHENS (basecuttac "ssr_have" ct)
          [Proofview.V82.of_tactic (Tactics.apply EConstr.(mkApp (mkVar id,args))); Tacticals.tclIDTAC] in
      "ssr_have",
      (if hint = nohint then tacigens else hinttac),
      Tacticals.tclTHENLIST [name_general_hyp; tac_specialize; tacipat pats; cleanup]
  in
  Tacticals.tclTHENS (basecuttac cut_kind c) [fst_goal_tac; snd_goal_tac] gl

(** The "suffice" tactic *)

let sufftac ist ((((clr, pats),binders),simpl), ((_, c), hint)) =
  let htac = Tacticals.tclTHEN (introstac ~ist pats) (hinttac ist true hint) in
  let open CAst in
  let c = match c with
  | (a, (b, Some { v = CCast (_, CastConv cty)})) -> a, (b, Some cty)
  | (a, ({ v = GCast (_, CastConv cty) }, None)) -> a, (cty, None)
  | _ -> anomaly "suff: ssr cast hole deleted by typecheck" in
  let ctac gl =
    let _,ty,_,uc = pf_interp_ty ist gl c in let gl = pf_merge_uc uc gl in
    basecuttac "ssr_suff" ty gl in
  Tacticals.tclTHENS ctac [htac; Tacticals.tclTHEN (cleartac clr) (introstac ~ist (binders@simpl))]
