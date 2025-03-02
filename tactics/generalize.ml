(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* module CVars = Vars *)

open Pp
open Util
open Names
open Constr
open Context
open Termops
open Environ
open EConstr
open Vars
open Find_subterm
open Namegen
open Locus
open Proofview.Notations
open Context.Named.Declaration

module NamedDecl = Context.Named.Declaration

(*********************************************)
(*                 Errors                    *)
(*********************************************)

exception AlreadyUsed of Id.t

let error ?loc e =
  Loc.raise ?loc e

exception Unhandled

let wrap_unhandled f e =
  try Some (f e)
  with Unhandled -> None

let tactic_interp_error_handler = function
  | AlreadyUsed id ->
      Id.print id ++ str " is already used."
  | _ -> raise Unhandled

let _ = CErrors.register_handler (wrap_unhandled tactic_interp_error_handler)

let fresh_id_in_env avoid id env =
  let avoid' = ids_of_named_context_val (named_context_val env) in
  let avoid = if Id.Set.is_empty avoid then avoid' else Id.Set.union avoid' avoid in
  next_ident_away_in_goal (Global.env ()) id avoid

(*********************************)
(*  Basic generalization tactics *)
(*********************************)

(* Given a type [T] convertible to [forall x1..xn:A1..An(x1..xn-1), G(x1..xn)]
   and [a1..an:A1..An(a1..an-1)] such that the goal is [G(a1..an)],
   this generalizes [hyps |- goal] into [hyps |- T] *)

(* Given a context [hyps] with domain [x1..xn], possibly with let-ins,
   and well-typed in the current goal, [bring_hyps hyps] generalizes
   [ctxt |- G(x1..xn] into [ctxt |- forall hyps, G(x1..xn)] *)

let bring_hyps hyps =
  if List.is_empty hyps then Tacticals.tclIDTAC
  else
    let hyps = List.rev hyps in
    Proofview.Goal.enter begin fun gl ->
      let env = Proofview.Goal.env gl in
      let sigma = Proofview.Goal.sigma gl in
      let concl = Tacmach.pf_concl gl in
      let newcl = it_mkNamedProd_or_LetIn sigma concl hyps in
      let args = Context.Named.instance mkVar hyps in
      Refine.refine_with_principal ~typecheck:false begin fun sigma ->
        let (sigma, ev) =
          Evarutil.new_evar env sigma newcl in
        (sigma, mkApp (ev, args), Some (fst @@ destEvar sigma ev))
      end
    end

let revert hyps =
  Proofview.Goal.enter begin fun gl ->
    let ctx = List.map (fun id -> Tacmach.pf_get_hyp id gl) hyps in
      (bring_hyps ctx) <*> (Tactics.clear hyps)
  end

(***************************)
(*  Generalization tactics *)
(***************************)

(* Compute a name for a generalization *)

let generalized_name env sigma c t ids cl = function
  | Name id as na ->
      if Id.List.mem id ids then
        error (AlreadyUsed id);
      na
  | Anonymous ->
      match EConstr.kind sigma c with
      | Var id ->
         (* Keep the name even if not occurring: may be used by intros later *)
          Name id
      | _ ->
          if noccurn sigma 1 cl then Anonymous else
            (* On ne s'etait pas casse la tete : on avait pris pour nom de
               variable la premiere lettre du type, meme si "c" avait ete une
               constante dont on aurait pu prendre directement le nom *)
            named_hd env sigma t Anonymous

(* Abstract over [c] in [forall x1:A1(c)..xi:Ai(c).T(c)] producing
   [forall x, x1:A1(x1), .., xi:Ai(x). T(x)] with all [c] abtracted in [Ai]
   but only those at [occs] in [T] *)

let generalize_goal_gen env sigma ids i ((occs,c,b),na) t cl =
  let open Context.Rel.Declaration in
  let decls,cl = decompose_prod_n_decls sigma i cl in
  let dummy_prod = it_mkProd_or_LetIn mkProp decls in
  let newdecls,_ =
    let arity = Array.length (snd (EConstr.decompose_app sigma c)) in
    let cache = ref Int.Map.empty in
    let eq sigma k t =
      let c =
        try Int.Map.find k !cache
        with Not_found ->
          let c = EConstr.Vars.lift k c in
          let () = cache := Int.Map.add k c !cache in
          c
      in
      (* We use a nounivs equality because generalize morally takes a pattern as
         argument, so we have to ignore freshly generated sorts. *)
      EConstr.eq_constr_nounivs sigma c t
    in
    decompose_prod_n_decls sigma i (replace_term_gen sigma eq arity (mkRel 1) dummy_prod)
  in
  let cl',sigma' = subst_closed_term_occ env sigma (AtOccs occs) c (it_mkProd_or_LetIn cl newdecls) in
  let na = generalized_name env sigma c t ids cl' na in
  let r = Retyping.relevance_of_type env sigma t in
  let decl = match b with
    | None -> LocalAssum (make_annot na r,t)
    | Some b -> LocalDef (make_annot na r,b,t)
  in
  mkProd_or_LetIn decl cl', sigma'

let generalize_goal gl i ((occs,c,b),na as o) (cl,sigma) =
  let open Tacmach in
  let env = pf_env gl in
  let ids = pf_ids_of_hyps gl in
  let sigma, t = Typing.type_of env sigma c in
  generalize_goal_gen env sigma ids i o t cl

let generalize_dep ?(with_let=false) c =
  let open Tacmach in
  let open Tacticals in
  Proofview.Goal.enter begin fun gl ->
  let env = pf_env gl in
  let sign = named_context_val env in
  let sigma = project gl in
  let init_ids = ids_of_named_context (Global.named_context()) in
  let seek (d:named_declaration) (toquant:named_context) =
    if List.exists (fun d' -> occur_var_in_decl env sigma (NamedDecl.get_id d') d) toquant
      || dependent_in_decl sigma c d then
      d::toquant
    else
      toquant in
  let to_quantify = Context.Named.fold_outside seek (named_context_of_val sign) ~init:[] in
  let qhyps = List.map NamedDecl.get_id to_quantify in
  let tothin = List.filter (fun id -> not (Id.List.mem id init_ids)) qhyps in
  let tothin' =
    match EConstr.kind sigma c with
      | Var id when mem_named_context_val id sign && not (Id.List.mem id init_ids)
          -> tothin@[id]
      | _ -> tothin
  in
  let cl' = it_mkNamedProd_or_LetIn sigma (pf_concl gl) to_quantify in
  let is_var, body = match EConstr.kind sigma c with
  | Var id ->
    let body = NamedDecl.get_value (pf_get_hyp id gl) in
    let is_var = Option.is_empty body && not (List.mem id init_ids) in
    if with_let then is_var, body else is_var, None
  | _ -> false, None
  in
  let cl'',evd = generalize_goal gl 0 ((AllOccurrences,c,body),Anonymous)
    (cl',project gl) in
  (* Check that the generalization is indeed well-typed *)
  let evd =
    (* No need to retype for variables, term is statically well-typed *)
    if is_var then evd
    else fst (Typing.type_of env evd cl'')
  in
  let args = Array.to_list (Context.Named.instance mkVar to_quantify) in
  tclTHENLIST
    [ Proofview.Unsafe.tclEVARS evd;
      Tactics.apply_type ~typecheck:false cl'' (if Option.is_empty body then c::args else args);
      Tactics.clear tothin']
  end

(**  *)
let generalize_gen_let lconstr = Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let newcl, evd =
    List.fold_right_i (generalize_goal gl) 0 lconstr
      (Tacmach.pf_concl gl,Tacmach.project gl)
  in
  let (evd, _) = Typing.type_of env evd newcl in
  let map ((_, c, b),_) = if Option.is_empty b then Some c else None in
  Proofview.tclTHEN (Proofview.Unsafe.tclEVARS evd)
  (Tactics.apply_type ~typecheck:false newcl (List.map_filter map lconstr))
end

let new_generalize_gen_let lconstr =
  Proofview.Goal.enter begin fun gl ->
    let sigma = Proofview.Goal.sigma gl in
    let concl = Proofview.Goal.concl gl in
    let env = Proofview.Goal.env gl in
    let ids = Tacmach.pf_ids_of_hyps gl in
    let newcl, sigma, args =
      List.fold_right_i
        (fun i ((_,c,b),_ as o) (cl, sigma, args) ->
          let sigma, t = Typing.type_of env sigma c in
          let args = if Option.is_empty b then c :: args else args in
          let cl, sigma = generalize_goal_gen env sigma ids i o t cl in
          (cl, sigma, args))
        0 lconstr (concl, sigma, [])
    in
    Proofview.tclTHEN (Proofview.Unsafe.tclEVARS sigma)
        (Refine.refine_with_principal ~typecheck:false begin fun sigma ->
          let (sigma, ev) = Evarutil.new_evar env sigma newcl in
          (sigma, applist (ev, args), Some (fst @@ destEvar sigma ev))
         end)
  end

let generalize_gen lconstr =
  generalize_gen_let (List.map (fun ((occs,c),na) ->
    (occs,c,None),na) lconstr)

let new_generalize_gen lconstr =
  new_generalize_gen_let (List.map (fun ((occs,c),na) ->
    (occs,c,None),na) lconstr)

let generalize l =
  new_generalize_gen_let (List.map (fun c -> ((AllOccurrences,c,None),Anonymous)) l)

(* Faudra-t-il une version avec plusieurs args de generalize_dep ?
Cela peut-être troublant de faire "Generalize Dependent H n" dans
"n:nat; H:n=n |- P(n)" et d'échouer parce que H a disparu après la
généralisation dépendante par n.

let quantify lconstr =
 List.fold_right
   (fun com tac -> tclTHEN tac (tactic_com generalize_dep c))
   lconstr
   tclIDTAC
*)

let rocq_eq env sigma       = Evd.fresh_global env sigma Rocqlib.(lib_ref "core.eq.type")
let rocq_eq_refl env sigma  = Evd.fresh_global env sigma Rocqlib.(lib_ref "core.eq.refl")

let rocq_heq_ref        = lazy (Rocqlib.lib_ref "core.JMeq.type")
let rocq_heq env sigma      = Evd.fresh_global env sigma (Lazy.force rocq_heq_ref)
let rocq_heq_refl env sigma = Evd.fresh_global env sigma (Rocqlib.lib_ref "core.JMeq.refl")
(* let rocq_heq_refl = lazy (glob (lib_ref "core.JMeq.refl")) *)

let mkEq env sigma t x y =
  let sigma, eq = rocq_eq env sigma in
  sigma, mkApp (eq, [| t; x; y |])

let mkRefl env sigma t x =
  let sigma, refl = rocq_eq_refl env sigma in
  sigma, mkApp (refl, [| t; x |])

let mkHEq env sigma t x u y =
  let sigma, c = rocq_heq env sigma in
  sigma, mkApp (c,[| t; x; u; y |])

let mkHRefl env sigma t x =
  let sigma, c = rocq_heq_refl env sigma in
  sigma, mkApp (c, [| t; x |])

let lift_togethern n l =
  let l', _ =
    List.fold_right
      (fun x (acc, n) ->
        (lift n x :: acc, succ n))
      l ([], n)
  in l'

let lift_list l = List.map (lift 1) l

let ids_of_constr env sigma ?(all=false) vars c =
  let rec aux vars c =
    match EConstr.kind sigma c with
    | Var id -> Id.Set.add id vars
    | App (f, args) ->
        (match EConstr.kind sigma f with
        | Construct ((ind,_),_)
        | Ind (ind,_) ->
            let (mib,mip) = Inductive.lookup_mind_specif env ind in
              Array.fold_left_from
                (if all then 0 else mib.Declarations.mind_nparams)
                aux vars args
        | _ -> EConstr.fold sigma aux vars c)
    | _ -> EConstr.fold sigma aux vars c
  in aux vars c

let decompose_indapp env sigma f args =
  match EConstr.kind sigma f with
  | Construct ((ind,_),_)
  | Ind (ind,_) ->
      let (mib,mip) = Inductive.lookup_mind_specif env ind in
      let first = mib.Declarations.mind_nparams_rec in
      let pars, args = Array.chop first args in
        mkApp (f, pars), args
  | _ -> f, args

let mk_term_eq homogeneous env sigma ty t ty' t' =
  if homogeneous then
    let sigma, eq = mkEq env sigma ty t t' in
    let sigma, refl = mkRefl env sigma ty' t' in
    sigma, (eq, refl)
  else
    let sigma, heq = mkHEq env sigma ty t ty' t' in
    let sigma, hrefl = mkHRefl env sigma ty' t' in
    sigma, (heq, hrefl)

let make_abstract_generalize env id typ concl dep ctx body c eqs args refls =
  let open Context.Rel.Declaration in
  Refine.refine_with_principal ~typecheck:true begin fun sigma ->
  let eqslen = List.length eqs in
    (* Abstract by the "generalized" hypothesis equality proof if necessary. *)
  let sigma, abshypeq, abshypt =
    if dep then
      let ty = lift 1 c in
      let homogeneous = Reductionops.is_conv env sigma ty typ in
      let sigma, (eq, refl) =
        mk_term_eq homogeneous (push_rel_context ctx env) sigma ty (mkRel 1) typ (mkVar id) in
      sigma, mkProd (make_annot Anonymous ERelevance.relevant, eq, lift 1 concl), [| refl |]
    else sigma, concl, [||]
  in
    (* Abstract by equalities *)
  let eqs = lift_togethern 1 eqs in (* lift together and past genarg *)
  let abseqs = it_mkProd_or_LetIn (lift eqslen abshypeq)
      (List.map (fun x -> LocalAssum (make_annot Anonymous ERelevance.relevant, x)) eqs)
  in
  let r = ERelevance.relevant in (* TODO relevance *)
  let decl = match body with
    | None -> LocalAssum (make_annot (Name id) r, c)
    | Some body -> LocalDef (make_annot (Name id) r, body, c)
  in
    (* Abstract by the "generalized" hypothesis. *)
  let genarg = mkProd_or_LetIn decl abseqs in
    (* Abstract by the extension of the context *)
  let genctyp = it_mkProd_or_LetIn genarg ctx in
    (* The goal will become this product. *)
  let (sigma, genc) = Evarutil.new_evar env sigma genctyp in
    (* Apply the old arguments giving the proper instantiation of the hyp *)
  let instc = mkApp (genc, Array.of_list args) in
    (* Then apply to the original instantiated hyp. *)
  let instc = Option.cata (fun _ -> instc) (mkApp (instc, [| mkVar id |])) body in
    (* Apply the reflexivity proofs on the indices. *)
  let appeqs = mkApp (instc, Array.of_list refls) in
    (* Finally, apply the reflexivity proof for the original hyp, to get a term of type gl again. *)
  (sigma, mkApp (appeqs, abshypt), Some (fst @@ destEvar sigma genc))
  end

let hyps_of_vars env sigma sign nogen hyps =
  if Id.Set.is_empty hyps then []
  else
    let (_,lh) =
      Context.Named.fold_inside
        (fun (hs,hl) d ->
          let x = NamedDecl.get_id d in
          if Id.Set.mem x nogen then (hs,hl)
          else if Id.Set.mem x hs then (hs,x::hl)
          else
            let xvars = global_vars_set_of_decl env sigma d in
              if not (Id.Set.is_empty (Id.Set.diff xvars hs)) then
                (Id.Set.add x hs, x :: hl)
              else (hs, hl))
        ~init:(hyps,[])
        sign
    in lh

exception Seen

let linear env sigma vars args =
  let seen = ref vars in
    try
      Array.iter (fun i ->
        let rels = ids_of_constr env sigma ~all:true Id.Set.empty i in
        let seen' =
          Id.Set.fold (fun id acc ->
            if Id.Set.mem id acc then raise Seen
            else Id.Set.add id acc)
            rels !seen
        in seen := seen')
        args;
      true
    with Seen -> false

let is_defined_variable env id =
  env |> lookup_named id |> is_local_def

let abstract_args gl generalize_vars dep id defined f args =
  let open Context.Rel.Declaration in
  let sigma = Tacmach.project gl in
  let env = Tacmach.pf_env gl in
  let concl = Tacmach.pf_concl gl in
  let hyps = Proofview.Goal.hyps gl in
  let dep = dep || local_occur_var sigma id concl in
  let avoid = ref Id.Set.empty in
  let get_id name =
    let id = fresh_id_in_env !avoid (match name with Name n -> n | Anonymous -> Id.of_string "gen_x") env in
      avoid := Id.Set.add id !avoid; id
  in
    (* Build application generalized w.r.t. the argument plus the necessary eqs.
       From env |- c : forall G, T and args : G we build
       (T[G'], G' : ctx, env ; G' |- args' : G, eqs := G'_i = G_i, refls : G' = G, vars to generalize)

       eqs are not lifted w.r.t. each other yet. (* will be needed when going to dependent indexes *)
    *)
  let aux (sigma, prod, ctx, ctxenv, c, args, eqs, refls, nongenvars, vars) arg =
    let name, ty_relevance, ty, arity =
      let rel, c = Reductionops.whd_decompose_prod_n env sigma 1 prod in
      let ({binder_name=na;binder_relevance=r},t) = List.hd rel in
      na, r, t, c
    in
    let argty = Retyping.get_type_of env sigma arg in
    let sigma, ty = Evarsolve.refresh_universes (Some true) env sigma ty in
    let lenctx = List.length ctx in
    let liftargty = lift lenctx argty in
    let leq = constr_cmp ctxenv sigma Conversion.CUMUL liftargty ty in
      match EConstr.kind sigma arg with
      | Var id when not (is_defined_variable env id) && leq && not (Id.Set.mem id nongenvars) ->
          (sigma, subst1 arg arity, ctx, ctxenv, mkApp (c, [|arg|]), args, eqs, refls,
          Id.Set.add id nongenvars, Id.Set.remove id vars)
      | _ ->
          let name = get_id name in
          let decl = LocalAssum (make_annot (Name name) ty_relevance, ty) in
          let ctx = decl :: ctx in
          let c' = mkApp (lift 1 c, [|mkRel 1|]) in
          let args = arg :: args in
          let liftarg = lift (List.length ctx) arg in
          let sigma, eq, refl =
            if leq then
              let sigma, eq = mkEq env  sigma (lift 1 ty) (mkRel 1) liftarg in
              let sigma, refl = mkRefl env sigma (lift (-lenctx) ty) arg in
              sigma, eq, refl
            else
              let sigma, eq = mkHEq env sigma (lift 1 ty) (mkRel 1) liftargty liftarg in
              let sigma, refl = mkHRefl env sigma argty arg in
              sigma, eq, refl
          in
          let eqs = eq :: lift_list eqs in
          let refls = refl :: refls in
          let argvars = ids_of_constr env sigma vars arg in
            (sigma, arity, ctx, push_rel decl ctxenv, c', args, eqs, refls,
            nongenvars, Id.Set.union argvars vars)
  in
  let f', args' = decompose_indapp env sigma f args in
  let dogen, f', args' =
    let parvars = ids_of_constr env sigma ~all:true Id.Set.empty f' in
      if not (linear env sigma parvars args') then true, f, args
      else
        match Array.findi (fun i x -> not (isVar sigma x) || is_defined_variable env (destVar sigma x)) args' with
        | None -> false, f', args'
        | Some nonvar ->
            let before, after = Array.chop nonvar args' in
              true, mkApp (f', before), after
  in
    if dogen then
      let tyf' = Retyping.get_type_of env sigma f' in
      let sigma, arity, ctx, ctxenv, c', args, eqs, refls, nogen, vars =
        Array.fold_left aux (sigma, tyf',[],env,f',[],[],[],Id.Set.empty,Id.Set.empty) args'
      in
      let args, refls = List.rev args, List.rev refls in
      let vars =
        if generalize_vars then
          let nogen = Id.Set.add id nogen in
            hyps_of_vars env sigma hyps nogen vars
        else []
      in
      let body, c' =
        if defined then Some c', Retyping.get_type_of ctxenv sigma c'
        else None, c'
      in
      let typ = Tacmach.pf_get_hyp_typ id gl in
      let tac = make_abstract_generalize env id typ concl dep ctx body c' eqs args refls in
      let tac = Proofview.Unsafe.tclEVARS sigma <*> tac in
        Some (tac, dep, succ (List.length ctx), vars)
    else None

let abstract_generalize ?(generalize_vars=true) ?(force_dep=false) id =
  let open Context.Named.Declaration in
  Proofview.Goal.enter begin fun gl ->
  Rocqlib.(check_required_library jmeq_module_name);
  let sigma = Tacmach.project gl in
  let (f, args, def, id, oldid) =
    let oldid = Tacmach.pf_get_new_id id gl in
      match Tacmach.pf_get_hyp id gl with
      | LocalAssum (_,t) -> let f, args = decompose_app sigma t in
                (f, args, false, id, oldid)
      | LocalDef (_,t,_) ->
          let f, args = decompose_app sigma t in
          (f, args, true, id, oldid)
  in
  if Array.is_empty args then Proofview.tclUNIT ()
  else
    let newc = abstract_args gl generalize_vars force_dep id def f args in
      match newc with
      | None -> Proofview.tclUNIT ()
      | Some (tac, dep, n, vars) ->
          let tac =
            if dep then
              Tacticals.tclTHENLIST [
                tac;
                 Tactics.rename_hyp [(id, oldid)]; Tacticals.tclDO n Tactics.intro;
                 generalize_dep ~with_let:true (mkVar oldid)]
            else Tacticals.tclTHENLIST [
                    tac;
                    Tactics.clear [id];
                    Tacticals.tclDO n Tactics.intro]
          in
            if List.is_empty vars then tac
            else Tacticals.tclTHEN tac
              (Tacticals.tclFIRST
                [revert vars ;
                 Tacticals.tclMAP (fun id ->
                      Tacticals.tclTRY (generalize_dep ~with_let:true (mkVar id))) vars])
  end
