(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open CErrors
open Util
open Constr
open Context
open Vars
open Declare
open Names
open Libnames
open Globnames
open Nameops
open Constrexpr
open Constrexpr_ops
open Constrintern
open Decl_kinds
open Evarutil
open Context.Rel.Declaration
open ComFixpoint

module RelDecl = Context.Rel.Declaration

(* Wellfounded definition *)

open Coqlib

let init_constant sigma rf = Evarutil.new_global sigma rf
let fix_sub_ref () = lib_ref "program.wf.fix_sub"
let measure_on_R_ref () = lib_ref "program.wf.mr"
let well_founded sigma = init_constant sigma (lib_ref "core.wf.well_founded")

let mkSubset sigma name typ prop =
  let open EConstr in
  let sigma, app_h = Evarutil.new_global sigma (delayed_force build_sigma).typ in
  sigma, mkApp (app_h, [| typ; mkLambda (make_annot name Sorts.Relevant, typ, prop) |])

let make_qref s = qualid_of_string s
let lt_ref = make_qref "Init.Peano.lt"

let rec telescope sigma l =
  let open EConstr in
  let open Vars in
  match l with
  | [] -> assert false
  | [LocalAssum (n, t)] ->
    sigma, t, [LocalDef (n, mkRel 1, t)], mkRel 1
  | LocalAssum (n, t) :: tl ->
      let sigma, ty, tys, (k, constr) =
        List.fold_left
          (fun (sigma, ty, tys, (k, constr)) decl ->
            let t = RelDecl.get_type decl in
            let pred = mkLambda (RelDecl.get_annot decl, t, ty) in
            let sigma, ty = Evarutil.new_global sigma (lib_ref "core.sigT.type") in
            let sigma, intro = Evarutil.new_global sigma (lib_ref "core.sigT.intro") in
            let sigty = mkApp (ty, [|t; pred|]) in
            let intro = mkApp (intro, [|lift k t; lift k pred; mkRel k; constr|]) in
              (sigma, sigty, pred :: tys, (succ k, intro)))
          (sigma, t, [], (2, mkRel 1)) tl
      in
      let sigma, last, subst = List.fold_right2
        (fun pred decl (sigma, prev, subst) ->
          let t = RelDecl.get_type decl in
          let sigma, p1 = Evarutil.new_global sigma (lib_ref "core.sigT.proj1") in
          let sigma, p2 = Evarutil.new_global sigma (lib_ref "core.sigT.proj2") in
          let proj1 = applist (p1, [t; pred; prev]) in
          let proj2 = applist (p2, [t; pred; prev]) in
            (sigma, lift 1 proj2, LocalDef (get_annot decl, proj1, t) :: subst))
        (List.rev tys) tl (sigma, mkRel 1, [])
      in sigma, ty, (LocalDef (n, last, t) :: subst), constr

  | LocalDef (n, b, t) :: tl ->
    let sigma, ty, subst, term = telescope sigma tl in
    sigma, ty, (LocalDef (n, b, t) :: subst), lift 1 term

let nf_evar_context sigma ctx =
  List.map (map_constr (fun c -> Evarutil.nf_evar sigma c)) ctx

let build_wellfounded (recname,pl,bl,arityc,body) poly r measure notation =
  let open EConstr in
  let open Vars in
  let lift_rel_context n l = Termops.map_rel_context_with_binders (liftn n) l in
  Coqlib.check_required_library ["Coq";"Program";"Wf"];
  let env = Global.env() in
  let sigma, decl = Constrexpr_ops.interp_univ_decl_opt env pl in
  let sigma, (_, ((env', binders_rel), impls)) = interp_context_evars ~program_mode:true env sigma bl in
  let len = List.length binders_rel in
  let top_env = push_rel_context binders_rel env in
  let sigma, top_arity = interp_type_evars ~program_mode:true top_env sigma arityc in
  let full_arity = it_mkProd_or_LetIn top_arity binders_rel in
  let sigma, argtyp, letbinders, make = telescope sigma binders_rel in
  let argname = Id.of_string "recarg" in
  let arg = LocalAssum (make_annot (Name argname) Sorts.Relevant, argtyp) in
  let binders = letbinders @ [arg] in
  let binders_env = push_rel_context binders_rel env in
  let sigma, (rel, _) = interp_constr_evars_impls ~program_mode:true env sigma r in
  let relty = Typing.unsafe_type_of env sigma rel in
  let relargty =
    let error () =
      user_err ?loc:(constr_loc r)
               ~hdr:"Command.build_wellfounded"
                    (Printer.pr_econstr_env env sigma rel ++ str " is not an homogeneous binary relation.")
    in
      try
        let ctx, ar = Reductionops.splay_prod_n env sigma 2 relty in
          match ctx, EConstr.kind sigma ar with
          | [LocalAssum (_,t); LocalAssum (_,u)], Sort s
              when Sorts.is_prop (ESorts.kind sigma s) && Reductionops.is_conv env sigma t u -> t
          | _, _ -> error ()
      with e when CErrors.noncritical e -> error ()
  in
  let sigma, measure = interp_casted_constr_evars ~program_mode:true binders_env sigma measure relargty in
  let sigma, wf_rel, wf_rel_fun, measure_fn =
    let measure_body, measure =
      it_mkLambda_or_LetIn measure letbinders,
      it_mkLambda_or_LetIn measure binders
    in
    let sigma, comb = Evarutil.new_global sigma (delayed_force measure_on_R_ref) in
    let wf_rel = mkApp (comb, [| argtyp; relargty; rel; measure |]) in
    let wf_rel_fun x y =
      mkApp (rel, [| subst1 x measure_body;
                     subst1 y measure_body |])
    in sigma, wf_rel, wf_rel_fun, measure
  in
  let sigma, wf_term = well_founded sigma in
  let wf_proof = mkApp (wf_term, [| argtyp ; wf_rel |]) in
  let argid' = Id.of_string (Id.to_string argname ^ "'") in
  let wfarg sigma len =
    let sigma, ss_term = mkSubset sigma (Name argid') argtyp (wf_rel_fun (mkRel 1) (mkRel (len + 1))) in
    sigma, LocalAssum (make_annot (Name argid') Sorts.Relevant, ss_term)
  in
  let sigma, intern_bl =
    let sigma, wfa = wfarg sigma 1 in
    sigma, wfa :: [arg]
  in
  let _intern_env = push_rel_context intern_bl env in
  let sigma, proj = Evarutil.new_global sigma (delayed_force build_sigma).Coqlib.proj1 in
  let wfargpred = mkLambda (make_annot (Name argid') Sorts.Relevant, argtyp, wf_rel_fun (mkRel 1) (mkRel 3)) in
  let projection = (* in wfarg :: arg :: before *)
    mkApp (proj, [| argtyp ; wfargpred ; mkRel 1 |])
  in
  let top_arity_let = it_mkLambda_or_LetIn top_arity letbinders in
  let intern_arity = substl [projection] top_arity_let in
  (* substitute the projection of wfarg for something,
     now intern_arity is in wfarg :: arg *)
  let sigma, wfa = wfarg sigma 1 in
  let intern_fun_arity_prod = it_mkProd_or_LetIn intern_arity [wfa] in
  let intern_fun_binder = LocalAssum (make_annot (Name (add_suffix recname "'")) Sorts.Relevant,
                                      intern_fun_arity_prod) in
  let sigma, curry_fun =
    let wfpred = mkLambda (make_annot (Name argid') Sorts.Relevant, argtyp, wf_rel_fun (mkRel 1) (mkRel (2 * len + 4))) in
    let sigma, intro = Evarutil.new_global sigma (delayed_force build_sigma).Coqlib.intro in
    let arg = mkApp (intro, [| argtyp; wfpred; lift 1 make; mkRel 1 |]) in
    let app = mkApp (mkRel (2 * len + 2 (* recproof + orig binders + current binders *)), [| arg |]) in
    let rcurry = mkApp (rel, [| measure; lift len measure |]) in
    let lam = LocalAssum (make_annot (Name (Id.of_string "recproof")) Sorts.Relevant, rcurry) in
    let body = it_mkLambda_or_LetIn app (lam :: binders_rel) in
    let ty = it_mkProd_or_LetIn (lift 1 top_arity) (lam :: binders_rel) in
    sigma, LocalDef (make_annot (Name recname) Sorts.Relevant, body, ty)
  in
  let fun_bl = intern_fun_binder :: [arg] in
  let lift_lets = lift_rel_context 1 letbinders in
  let sigma, intern_body =
    let ctx = LocalAssum (make_annot (Name recname) Sorts.Relevant, get_type curry_fun) :: binders_rel in
    let (r, l, impls, scopes) =
      Constrintern.compute_internalization_data env sigma
        Constrintern.Recursive full_arity impls
    in
    let newimpls = Id.Map.singleton recname
        (r, l, impls @ [(Some (Id.of_string "recproof", Impargs.Manual, (true, false)))],
         scopes @ [None]) in
    interp_casted_constr_evars ~program_mode:true (push_rel_context ctx env) sigma
      ~impls:newimpls body (lift 1 top_arity)
  in
  let intern_body_lam = it_mkLambda_or_LetIn intern_body (curry_fun :: lift_lets @ fun_bl) in
  let prop = mkLambda (make_annot (Name argname) Sorts.Relevant, argtyp, top_arity_let) in
  (* XXX: Previous code did parallel evdref update, so possible old
     weak ordering semantics may bite here. *)
  let sigma, def =
    let sigma, h_a_term = Evarutil.new_global sigma (delayed_force fix_sub_ref) in
    let sigma, h_e_term = Evarutil.new_evar env sigma
        ~src:(Loc.tag @@ Evar_kinds.QuestionMark {
            Evar_kinds.default_question_mark with Evar_kinds.qm_obligation=Evar_kinds.Define false;
          }) wf_proof in
    let sigma = Evd.set_obligation_evar sigma (fst (destEvar sigma h_e_term)) in
    sigma, mkApp (h_a_term, [| argtyp ; wf_rel ; h_e_term; prop |])
  in
  let sigma, def = Typing.solve_evars env sigma def in
  let sigma = Evarutil.nf_evar_map sigma in
  let def = mkApp (def, [|intern_body_lam|]) in
  let binders_rel = nf_evar_context sigma binders_rel in
  let binders = nf_evar_context sigma binders in
  let top_arity = Evarutil.nf_evar sigma top_arity in
  let hook, recname, typ =
    if List.length binders_rel > 1 then
      let name = add_suffix recname "_func" in
      (* XXX: Mutating the evar_map in the hook! *)
      (* XXX: Likely the sigma is out of date when the hook is called .... *)
      let hook sigma { DeclareDef.Hook.S.dref; _ } =
        let sigma, h_body = Evarutil.new_global sigma dref in
        let body = it_mkLambda_or_LetIn (mkApp (h_body, [|make|])) binders_rel in
        let ty = it_mkProd_or_LetIn top_arity binders_rel in
        let ty = EConstr.Unsafe.to_constr ty in
        let univs = Evd.check_univ_decl ~poly sigma decl in
        (*FIXME poly? *)
        let ce = definition_entry ~types:ty ~univs (EConstr.to_constr sigma body) in
        (* FIXME: include locality *)
        let c = Declare.declare_constant recname (DefinitionEntry ce, IsDefinition Definition) in
        let gr = ConstRef c in
        if Impargs.is_implicit_args () || not (List.is_empty impls) then
          Impargs.declare_manual_implicits false gr impls
      in
      let typ = it_mkProd_or_LetIn top_arity binders in
      hook, name, typ
    else
      let typ = it_mkProd_or_LetIn top_arity binders_rel in
      let hook sigma { DeclareDef.Hook.S.dref; _ } =
        if Impargs.is_implicit_args () || not (List.is_empty impls) then
          Impargs.declare_manual_implicits false dref impls
      in hook, recname, typ
  in
  (* XXX: Capturing sigma here... bad bad *)
  let hook = DeclareDef.Hook.make (hook sigma) in
  Obligations.check_evars env sigma;
  let evars, _, evars_def, evars_typ =
    Obligations.eterm_obligations env recname sigma 0 def typ
  in
  let ctx = Evd.evar_universe_context sigma in
    ignore(Obligations.add_definition ~name:recname ~term:evars_def ~univdecl:decl
             ~poly evars_typ ctx evars ~hook)

let out_def = function
  | Some def -> def
  | None -> user_err Pp.(str "Program Fixpoint needs defined bodies.")

let collect_evars_of_term evd c ty =
  let evars = Evar.Set.union (Evd.evars_of_term evd c) (Evd.evars_of_term evd ty) in
  Evar.Set.fold (fun ev acc -> Evd.add acc ev (Evd.find_undefined evd ev))
  evars (Evd.from_ctx (Evd.evar_universe_context evd))

let do_program_recursive ~scope ~poly fixkind fixl ntns =
  let cofix = fixkind = DeclareObl.IsCoFixpoint in
  let (env, rec_sign, pl, evd), fix, info =
    interp_recursive ~cofix ~program_mode:true fixl ntns
  in
    (* Program-specific code *)
    (* Get the interesting evars, those that were not instantiated *)
  let evd = Typeclasses.resolve_typeclasses ~filter:Typeclasses.no_goals ~fail:true env evd in
    (* Solve remaining evars *)
  let evd = nf_evar_map_undefined evd in
  let collect_evars id def typ imps =
    (* Generalize by the recursive prototypes  *)
    let def = nf_evar evd (Termops.it_mkNamedLambda_or_LetIn def rec_sign) in
    let typ = nf_evar evd (Termops.it_mkNamedProd_or_LetIn typ rec_sign) in
    let evm = collect_evars_of_term evd def typ in
    let evars, _, def, typ =
      Obligations.eterm_obligations env id evm
        (List.length rec_sign) def typ in
    (id, def, typ, imps, evars)
  in
  let (fixnames,fixrs,fixdefs,fixtypes) = fix in
  let fiximps = List.map pi2 info in
  let fixdefs = List.map out_def fixdefs in
  let defs = List.map4 collect_evars fixnames fixdefs fixtypes fiximps in
  let () = if not cofix then begin
      let possible_indexes = List.map ComFixpoint.compute_possible_guardness_evidences info in
      (* XXX: are we allowed to have evars here? *)
      let fixtypes = List.map (EConstr.to_constr ~abort_on_undefined_evars:false evd) fixtypes in
      let fixdefs = List.map (EConstr.to_constr ~abort_on_undefined_evars:false evd) fixdefs in
      let fixdecls = Array.of_list (List.map2 (fun x r -> make_annot (Name x) r) fixnames fixrs),
        Array.of_list fixtypes,
        Array.of_list (List.map (subst_vars (List.rev fixnames)) fixdefs)
      in
      let indexes =
        Pretyping.search_guard (Global.env ()) possible_indexes fixdecls in
      List.iteri (fun i _ ->
          Inductive.check_fix env
                              ((indexes,i),fixdecls))
        fixl
  end in
  let ctx = Evd.evar_universe_context evd in
  let kind = match fixkind with
  | DeclareObl.IsFixpoint _ -> Fixpoint
  | DeclareObl.IsCoFixpoint -> CoFixpoint
  in
  Obligations.add_mutual_definitions defs ~poly ~scope ~kind ~univdecl:pl ctx ntns fixkind

let do_program_fixpoint ~scope ~poly l =
  let g = List.map (fun ((_,wf,_,_,_),_) -> wf) l in
    match g, l with
    | [Some { CAst.v = CWfRec (n,r) }], [((({CAst.v=id},pl),_,bl,typ,def),ntn)] ->
        let recarg = mkIdentC n.CAst.v in
        build_wellfounded (id, pl, bl, typ, out_def def) poly r recarg ntn

    | [Some { CAst.v = CMeasureRec (n, m, r) }], [((({CAst.v=id},pl),_,bl,typ,def),ntn)] ->
      (* We resolve here a clash between the syntax of Program Fixpoint and the one of funind *)
      let r = match n, r with
        | Some id, None ->
          let loc = id.CAst.loc in
          Some (CAst.make ?loc @@ CRef(qualid_of_ident ?loc id.CAst.v,None))
        | Some _, Some _ ->
          user_err Pp.(str"Measure takes only two arguments in Program Fixpoint.")
        | _, _ -> r
      in
        build_wellfounded (id, pl, bl, typ, out_def def) poly
          (Option.default (CAst.make @@ CRef (lt_ref,None)) r) m ntn

    | _, _ when List.for_all (fun ro -> match ro with None | Some { CAst.v = CStructRec _} -> true | _ -> false) g ->
        let fixl,ntns = extract_fixpoint_components ~structonly:true l in
        let fixkind = DeclareObl.IsFixpoint (List.map (fun d -> d.fix_annot) fixl) in
          do_program_recursive ~scope ~poly fixkind fixl ntns

    | _, _ ->
        user_err ~hdr:"do_program_fixpoint"
          (str "Well-founded fixpoints not allowed in mutually recursive blocks")

let extract_cofixpoint_components l =
  let fixl, ntnl = List.split l in
  List.map (fun (({CAst.v=id},pl),bl,typ,def) ->
            {fix_name = id; fix_annot = None; fix_univs = pl;
             fix_binders = bl; fix_body = def; fix_type = typ}) fixl,
  List.flatten ntnl

let check_safe () =
  let open Declarations in
  let flags = Environ.typing_flags (Global.env ()) in
  flags.check_universes && flags.check_guarded

let do_fixpoint ~scope ~poly l =
  do_program_fixpoint ~scope ~poly l;
  if not (check_safe ()) then Feedback.feedback Feedback.AddedAxiom else ()

let do_cofixpoint ~scope ~poly l =
  let fixl,ntns = extract_cofixpoint_components l in
  do_program_recursive ~scope ~poly DeclareObl.IsCoFixpoint fixl ntns;
  if not (check_safe ()) then Feedback.feedback Feedback.AddedAxiom else ()
