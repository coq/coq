(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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
open Tacmach

open Ssrmatching_plugin.Ssrmatching
open Ssrprinters
open Ssrcommon
open Ssrtacticals

module RelDecl = Context.Rel.Declaration

(** 8. Forward chaining tactics (pose, set, have, suffice, wlog) *)
(** Defined identifier *)

let posetac id cl = Proofview.V82.of_tactic (Tactics.pose_tac (Name id) cl)

let ssrposetac (id, (_, t)) gl =
  let ist, t =
    match t.Ssrast.interp_env with
    | Some ist -> ist, Ssrcommon.ssrterm_of_ast_closure_term t
    | None -> assert false in
  let sigma, t, ucst, _ = pf_abs_ssrterm ist gl t in
  posetac id t (pf_merge_uc ucst gl)

let ssrsettac id ((_, (pat, pty)), (_, occ)) gl =
  let pty = Option.map (fun { Ssrast.body; interp_env } ->
    let ist = Option.get interp_env in
    (mkRHole, Some body), ist) pty in
  let pat = interp_cpattern gl pat pty in
  let cl, sigma, env = pf_concl gl, project gl, pf_env gl in
  let (c, ucst), cl = 
    let cl = EConstr.Unsafe.to_constr cl in
    try fill_occ_pattern ~raise_NoMatch:true env sigma cl pat occ 1
    with NoMatch -> redex_of_pattern ~resolve_typeclasses:true env pat, cl in
  let gl = pf_merge_uc ucst gl in
  let c = EConstr.of_constr c in
  let cl = EConstr.of_constr cl in
  if Termops.occur_existential sigma c then errorstrm(str"The pattern"++spc()++
    pr_econstr_pat env sigma c++spc()++str"did not match and has holes."++spc()++
    str"Did you mean pose?") else
  let c, (gl, cty) =  match EConstr.kind sigma c with
  | Cast(t, DEFAULTcast, ty) -> t, (gl, ty)
  | _ -> c, pfe_type_of gl c in
  let cl' = EConstr.mkLetIn (make_annot (Name id) Sorts.Relevant, c, cty, cl) in
  Tacticals.tclTHEN (Proofview.V82.of_tactic (convert_concl ~check:true cl')) (introid id) gl

open Util

open Printer

open Ssrast
open Ssripats

let ssrhaveNOtcresolution = Summary.ref ~name:"SSR:havenotcresolution" false

let () =
  Goptions.(declare_bool_option
    { optname  = "have type classes";
      optkey   = ["SsrHave";"NoTCResolution"];
      optread  = (fun _ -> !ssrhaveNOtcresolution);
      optdepr  = false;
      optwrite = (fun b -> ssrhaveNOtcresolution := b);
    })


open Constrexpr 
open Glob_term 

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

let introstac ipats = Proofview.V82.of_tactic (tclIPAT ipats)

let havetac ist
  (transp,((((clr, orig_pats), binders), simpl), (((fk, _), t), hint)))
  suff namefst gl 
=
 let concl = pf_concl gl in
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
 let itac, id, clr = introstac pats, Tacticals.tclIDTAC, old_cleartac clr in
 let binderstac n =
   let rec aux = function 0 -> [] | n -> IOpInaccessible None :: aux (n-1) in
   Tacticals.tclTHEN (if binders <> [] then introstac (aux n) else Tacticals.tclIDTAC)
     (introstac binders) in
 let simpltac = introstac simpl in
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
  let ct, cty, hole, loc = match Ssrcommon.ssrterm_of_ast_closure_term t with
    | _, (_, Some { loc; v = CCast (ct, CastConv cty)}) ->
      mkt ct, mkt cty, mkt (mkCHole None), loc
    | _, (_, Some ct) ->
      mkt ct, mkt (mkCHole None), mkt (mkCHole None), None
    | _, (t, None) ->
      begin match DAst.get t with
      | GCast (ct, CastConv cty) ->
        mkl ct, mkl cty, mkl mkRHole, t.CAst.loc
      | _ -> mkl t, mkl mkRHole, mkl mkRHole, None
      end
  in
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
       try Proofview.V82.of_tactic (convert_concl ~check:true (EConstr.it_mkProd_or_LetIn concl ctx)) gl
       with _ -> errorstrm (str "Given proof term is not of type " ++
         pr_econstr_env (pf_env gl) (project gl) (EConstr.mkArrow (EConstr.mkVar (Id.of_string "_")) Sorts.Relevant concl)) in
     gl, ty, Tacticals.tclTHEN assert_is_conv (Proofview.V82.of_tactic (Tactics.apply t)), id, itac_c
   | FwdHave, false, false ->
     let skols = List.flatten (List.map (function
       | IOpAbstractVars ids -> ids
       | _ -> assert false) skols) in
     let skols_args =
       List.map (fun id -> Ssripats.Internal.examine_abstract (EConstr.mkVar id) gl) skols in
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
         Ssripats.Internal.pf_find_abstract_proof false gl (EConstr.Unsafe.to_constr a.(1))) skols_args in
     let tacopen_skols gl = re_sig (gs @ [gl.Evd.it]) gl.Evd.sigma in
     let gl, ty = pf_e_type_of gl t in
     gl, ty, Proofview.V82.of_tactic (Tactics.apply t), id,
       Tacticals.tclTHEN (Tacticals.tclTHEN itac_c simpltac)
         (Tacticals.tclTHEN tacopen_skols (fun gl ->
            let abstract, gl = pf_mkSsrConst "abstract" gl in
            Proofview.V82.of_tactic (unfold [abstract; abstract_key]) gl))
   | _,true,true  ->
     let _, ty, uc = interp_ty gl fixtc cty in let gl = pf_merge_uc uc gl in
     gl, EConstr.mkArrow ty Sorts.Relevant concl, hint, itac, clr
   | _,false,true ->
     let _, ty, uc = interp_ty gl fixtc cty in let gl = pf_merge_uc uc gl in
     gl, EConstr.mkArrow ty Sorts.Relevant concl, hint, id, itac_c
   | _, false, false -> 
     let n, cty, uc = interp_ty gl fixtc cty in let gl = pf_merge_uc uc gl in
     gl, cty, Tacticals.tclTHEN (binderstac n) hint, id, Tacticals.tclTHEN itac_c simpltac
   | _, true, false -> assert false in
  Tacticals.tclTHENS (cuttac cut) [ Tacticals.tclTHEN sol itac1; itac2 ] gl)
 gl
;;

let destProd_or_LetIn sigma c =
  match EConstr.kind sigma c with
  | Prod (n,ty,c) -> RelDecl.LocalAssum (n, ty), c
  | LetIn (n,bo,ty,c) -> RelDecl.LocalDef (n, bo, ty), c
  | _ -> raise DestKO

let wlogtac ist (((clr0, pats),_),_) (gens, ((_, ct))) hint suff ghave gl =
  let clr0 = Option.default [] clr0 in
  let pats = tclCompileIPats pats in
  let mkabs gen = abs_wgen false (fun x -> x) gen in
  let mkclr gen clrs = clr_of_wgen gen clrs in
  let mkpats = function
  | _, Some ((x, _), _) -> fun pats -> IOpId (hoi_id x) :: pats
  | _ -> fun x -> x in
  let ct = match Ssrcommon.ssrterm_of_ast_closure_term ct with
  | (a, (b, Some ct)) ->
    begin match ct.CAst.v with
    | CCast (_, CastConv cty) -> a, (b, Some cty)
    | _ -> anomaly "wlog: ssr cast hole deleted by typecheck"
    end
  | (a, (t, None)) ->
    begin match DAst.get t with
    | GCast (_, CastConv cty) -> a, (cty, None)
    | _ -> anomaly "wlog: ssr cast hole deleted by typecheck"
    end
  in
  let cut_implies_goal = not (suff || ghave <> `NoGen) in
  let c, args, ct, gl =
    let gens = List.filter (function _, Some _ -> true | _ -> false) gens in
    let concl = pf_concl gl in
    let c = EConstr.mkProp in
    let c = if cut_implies_goal then EConstr.mkArrow c Sorts.Relevant concl else c in
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
      | Prod({binder_name=Anonymous} as x,_,c), [] -> EConstr.mkProd(x, EConstr.Vars.subst_vars s ct, c)
      | Sort _, [] -> EConstr.Vars.subst_vars s ct
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
    c, args, pired c args, pf_merge_uc uc gl in
  let tacipat pats = introstac pats in
  let tacigens = 
    Tacticals.tclTHEN
      (Tacticals.tclTHENLIST(List.rev(List.fold_right mkclr gens [old_cleartac clr0])))
      (introstac (List.fold_right mkpats gens [])) in
  let hinttac = hinttac ist true hint in
  let cut_kind, fst_goal_tac, snd_goal_tac =
    match suff, ghave with
    | true, `NoGen -> "ssr_wlog", Tacticals.tclTHEN hinttac (tacipat pats), tacigens
    | false, `NoGen -> "ssr_wlog", hinttac, Tacticals.tclTHEN tacigens (tacipat pats)
    | true, `Gen _ -> assert false
    | false, `Gen id ->
      if gens = [] then errorstrm(str"gen have requires some generalizations");
      let clear0 = old_cleartac clr0 in
      let id, name_general_hyp, cleanup, pats = match id, pats with
      | None, (IOpId id as ip)::pats -> Some id, tacipat [ip], clear0, pats
      | None, _ -> None, Tacticals.tclIDTAC, clear0, pats
      | Some (Some id),_ -> Some id, introid id, clear0, pats
      | Some _,_ ->
          let id = mk_anon_id "tmp" (Tacmach.pf_ids_of_hyps gl) in
          Some id, introid id, Tacticals.tclTHEN clear0 (Proofview.V82.of_tactic (Tactics.clear [id])), pats in
      let tac_specialize = match id with
      | None -> Tacticals.tclIDTAC
      | Some id ->
        if pats = [] then Tacticals.tclIDTAC else
        let args = Array.of_list args in
        ppdebug(lazy(str"specialized="++ pr_econstr_env (pf_env gl) (project gl) EConstr.(mkApp (mkVar id,args))));
        ppdebug(lazy(str"specialized_ty="++ pr_econstr_env (pf_env gl) (project gl) ct));
        Tacticals.tclTHENS (basecuttac "ssr_have" ct)
          [Proofview.V82.of_tactic (Tactics.apply EConstr.(mkApp (mkVar id,args))); Tacticals.tclIDTAC] in
      "ssr_have",
      (if hint = nohint then tacigens else hinttac),
      Tacticals.tclTHENLIST [name_general_hyp; tac_specialize; tacipat pats; cleanup]
  in
  Tacticals.tclTHENS (basecuttac cut_kind c) [fst_goal_tac; snd_goal_tac] gl

(** The "suffice" tactic *)

let sufftac ist ((((clr, pats),binders),simpl), ((_, c), hint)) =
  let clr = Option.default [] clr in
  let pats = tclCompileIPats pats in
  let binders = tclCompileIPats binders in
  let simpl = tclCompileIPats simpl in
  let htac = Tacticals.tclTHEN (introstac pats) (hinttac ist true hint) in
  let c = match Ssrcommon.ssrterm_of_ast_closure_term c with
  | (a, (b, Some ct)) ->
    begin match ct.CAst.v with
    | CCast (_, CastConv cty) -> a, (b, Some cty)
    | _ -> anomaly "suff: ssr cast hole deleted by typecheck"
    end
  | (a, (t, None)) ->
    begin match DAst.get t with
    | GCast (_, CastConv cty) -> a, (cty, None)
    | _ -> anomaly "suff: ssr cast hole deleted by typecheck"
    end
  in
  let ctac gl =
    let _,ty,_,uc = pf_interp_ty ist gl c in let gl = pf_merge_uc uc gl in
    basecuttac "ssr_suff" ty gl in
  Tacticals.tclTHENS ctac [htac; Tacticals.tclTHEN (old_cleartac clr) (introstac (binders@simpl))]

open Proofview.Notations

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
  let rec lock_eq () : unit Proofview.tactic = Proofview.Goal.enter begin fun _ ->
    Proofview.tclORELSE
      (Ssripats.tclIPAT [Ssripats.IOpTemporay; Ssripats.IOpEqGen (lock_eq ())])
      (fun _exn -> Proofview.Goal.enter begin fun gl ->
        let c = Proofview.Goal.concl gl in
        let sigma = Proofview.Goal.sigma gl in
        let env = Proofview.Goal.env gl in
        match EConstr.kind_of_type sigma c with
        | Term.AtomicType(hd, args) when
            Ssrcommon.is_const_ref sigma hd (Coqlib.lib_ref "core.iff.type") &&
           Array.length args = 2 && is_app_evar sigma args.(1) ->
           Tactics.New.refine ~typecheck:true (fun sigma ->
               let sigma, under_iff =
                 Ssrcommon.mkSsrConst "Under_iff" env sigma in
               let sigma, under_from_iff =
                 Ssrcommon.mkSsrConst "Under_iff_from_iff" env sigma in
               let ty = EConstr.mkApp (under_iff,args) in
               let sigma, t = Evarutil.new_evar env sigma ty in
               sigma, EConstr.mkApp(under_from_iff,Array.append args [|t|]))
        | _ ->
        let t = Reductionops.whd_all env sigma c in
        match EConstr.kind_of_type sigma t with
        | Term.AtomicType(hd, args) when
            Ssrcommon.is_ind_ref sigma hd (Coqlib.lib_ref "core.eq.type") &&
            Array.length args = 3 && is_app_evar sigma args.(2) ->
              Tactics.New.refine ~typecheck:true (fun sigma ->
                let sigma, under =
                  Ssrcommon.mkSsrConst "Under_eq" env sigma in
                let sigma, under_from_eq =
                  Ssrcommon.mkSsrConst "Under_eq_from_eq" env sigma in
                let ty = EConstr.mkApp (under,args) in
                let sigma, t = Evarutil.new_evar env sigma ty in
                sigma, EConstr.mkApp(under_from_eq,Array.append args [|t|]))
        | _ ->
    ppdebug(lazy Pp.(str"under: stop:" ++ pr_econstr_env env sigma t));

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

let overtac = Proofview.V82.tactic (ssr_n_tac "over" ~-1)

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
    ppdebug(lazy Pp.(str"under vars: " ++ prlist Names.Name.print varnames));

    let evar_map, ty = Typing.type_of env evar_map t in
    let new_t = (* pretty-rename the bound variables *)
      try begin match EConstr.destApp evar_map t with (f, ar) ->
            let lam = Array.last ar in
            ppdebug(lazy Pp.(str"under: mapping:" ++
                             pr_econstr_env env evar_map lam));
            let new_lam = pretty_rename evar_map lam varnames in
            let new_ar, len1 = Array.copy ar, pred (Array.length ar) in
            new_ar.(len1) <- new_lam;
            EConstr.mkApp (f, new_ar)
          end with
      | DestKO ->
        ppdebug(lazy Pp.(str"under: cannot pretty-rename bound variables with destApp"));
        t
    in
    ppdebug(lazy Pp.(str"under: to:" ++ pr_econstr_env env evar_map new_t));
    evar_map, new_t
  in
  let undertacs =
    if hint = nohint then
      Proofview.tclUNIT ()
    else
      let betaiota = Tactics.reduct_in_concl ~check:false (Reductionops.nf_betaiota, DEFAULTcast) in
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
    Proofview.V82.tactic
      (Ssrequality.ssrrewritetac ~under:true ~map_redex ist [rule])
  in
  rew <*> intro_lock ipats <*> undertacs
