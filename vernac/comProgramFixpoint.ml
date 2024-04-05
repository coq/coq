(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open CErrors
open Util
open Context
open Declare
open Names
open Libnames
open Nameops
open Constrexpr
open Constrexpr_ops
open Constrintern
open Evarutil
open Context.Rel.Declaration
open ComFixpoint

module RelDecl = Context.Rel.Declaration

(* Wellfounded definition *)

open Coqlib

let init_constant sigma rf = Evd.fresh_global sigma rf
let fix_sub_ref () = lib_ref "program.wf.fix_sub"
let measure_on_R_ref () = lib_ref "program.wf.mr"
let well_founded sigma = init_constant (Global.env ()) sigma (lib_ref "core.wf.well_founded")

let mkSubset sigma name typ prop =
  let open EConstr in
  let sigma, app_h = Evd.fresh_global (Global.env ()) sigma (delayed_force build_sigma).typ in
  sigma, mkApp (app_h, [| typ; mkLambda (make_annot name Sorts.Relevant, typ, prop) |])

let make_qref s = qualid_of_string s
let lt_ref = make_qref "Init.Peano.lt"

let nf_evar_context sigma ctx =
  let nf c = Evarutil.nf_evar sigma c in
  let nfa na = UnivSubst.nf_binder_annot (fun r -> Evarutil.nf_relevance sigma r) na in
  let map = function
  | RelDecl.LocalAssum (na, t) -> RelDecl.LocalAssum (nfa na, nf t)
  | RelDecl.LocalDef (na, c, t) -> RelDecl.LocalDef (nfa na, nf c, nf t)
  in
  List.map map ctx

let build_wellfounded pm (recname,pl,bl,arityc,body) ?scope ?clearbody poly ?typing_flags ?user_warns ?using r measure notations =
  let open EConstr in
  let open Vars in
  let open Combinators in
  let ntns = List.map Metasyntax.prepare_where_notation notations in
  let fix_sub_ref, measure_on_R_ref = try fix_sub_ref (), measure_on_R_ref ()
    with NotFoundRef r ->
      CErrors.user_err
        Pp.(str r ++ spc() ++ str "not registered," ++ spc() ++
            str "you should try requiring library Coq.Program.Wf.")
  in
  let env = Global.env() in
  let sigma, udecl = interp_univ_decl_opt env pl in
  let sigma, (impls_env, ((env', binders_rel), impls)) = interp_context_evars ~program_mode:true env sigma bl in
  let len = List.length binders_rel in
  let top_env = push_rel_context binders_rel env in
  let flags = Pretyping.{ all_no_fail_flags with program_mode = true } in
  let sigma, (top_arity, arityimpls) = interp_type_evars_impls ~flags top_env sigma arityc in
  let sigma, letbinders, { telescope_type = argtyp; telescope_value = make } =
    telescope env sigma binders_rel in
  let argname = Id.of_string "recarg" in
  let arg = LocalAssum (make_annot (Name argname) Sorts.Relevant, argtyp) in
  let binders = letbinders @ [arg] in
  let binders_env = push_rel_context binders_rel env in
  let sigma, (rel, _) = interp_constr_evars_impls ~program_mode:true env sigma r in
  let relargty = Hipattern.is_homogeneous_relation ?loc:(constr_loc r) env sigma rel in
  let sigma, measure = interp_casted_constr_evars ~program_mode:true binders_env sigma measure relargty in
  let sigma, wf_rel, wf_rel_fun, measure_fn =
    let measure_body, measure =
      it_mkLambda_or_LetIn measure letbinders,
      it_mkLambda_or_LetIn measure binders
    in
    let sigma, comb = Evd.fresh_global (Global.env ()) sigma measure_on_R_ref in
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
  let sigma, proj = Evd.fresh_global (Global.env ()) sigma (delayed_force build_sigma).Coqlib.proj1 in
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
  let recproofid = Id.of_string "recproof" in
  let sigma, curry_fun =
    let wfpred = mkLambda (make_annot (Name argid') Sorts.Relevant, argtyp, wf_rel_fun (mkRel 1) (mkRel (2 * len + 4))) in
    let sigma, intro = Evd.fresh_global (Global.env ()) sigma (delayed_force build_sigma).Coqlib.intro in
    let arg = mkApp (intro, [| argtyp; wfpred; lift 1 make; mkRel 1 |]) in
    let app = mkApp (mkRel (2 * len + 2 (* recproof + orig binders + current binders *)), [| arg |]) in
    let rcurry = mkApp (rel, [| measure; lift len measure |]) in
    let lam = LocalAssum (make_annot (Name recproofid) Sorts.Relevant, rcurry) in
    let body = it_mkLambda_or_LetIn app (lam :: binders_rel) in
    let ty = it_mkProd_or_LetIn (lift 1 top_arity) (lam :: binders_rel) in
    sigma, LocalDef (make_annot (Name recname) Sorts.Relevant, body, ty)
  in
  let fun_bl = intern_fun_binder :: [arg] in
  let lift_lets = lift_rel_context 1 letbinders in
  let sigma, intern_body =
    let ctx = LocalAssum (make_annot (Name recname) Sorts.Relevant, get_type curry_fun) :: binders_rel in
    let impl = CAst.make (Some (Name recproofid, true)) in
    let newimpls = impls @ impl :: arityimpls in
    let dummy_decl =
      (* Ensure the measure argument does not contribute to the computation of automatic implicit arguments *)
      LocalAssum (make_annot (Name recproofid) Sorts.Relevant, mkProp) in
    let full_arity = it_mkProd_or_LetIn top_arity (dummy_decl :: binders_rel) in
    let interning_data =
      Constrintern.compute_internalization_data env sigma recname
        Constrintern.Recursive full_arity newimpls in
    let interning_data =
      (* Force the obligation status of "recproof" *)
      set_obligation_internalization_data recproofid interning_data in
    let newimpls = Id.Map.add recname interning_data impls_env in
    Metasyntax.with_syntax_protection (fun () ->
        let env_ctx = push_rel_context ctx env in
        List.iter (Metasyntax.set_notation_for_interpretation env_ctx newimpls) ntns;
        interp_casted_constr_evars ~program_mode:true env_ctx sigma
          ~impls:newimpls body (lift 1 top_arity))
      ()
  in
  let intern_body_lam = it_mkLambda_or_LetIn intern_body (curry_fun :: lift_lets @ fun_bl) in
  let prop = mkLambda (make_annot (Name argname) Sorts.Relevant, argtyp, top_arity_let) in
  (* XXX: Previous code did parallel evdref update, so possible old
     weak ordering semantics may bite here. *)
  let sigma, def =
    let sigma, h_a_term = Evd.fresh_global (Global.env ()) sigma fix_sub_ref in
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
  let make = Evarutil.nf_evar sigma make in
  let hook, recname, typ =
    if List.length binders_rel > 1 then
      let name = add_suffix recname "_func" in
      let hook { Declare.Hook.S.dref; uctx; _ } =
        let sigma = Evd.from_ctx uctx in
        let sigma, h_body = Evd.fresh_global (Global.env ()) sigma dref in
        let body = it_mkLambda_or_LetIn (mkApp (h_body, [|make|])) binders_rel in
        let ty = it_mkProd_or_LetIn top_arity binders_rel in
        let ty = EConstr.Unsafe.to_constr ty in
        let univs = Evd.check_univ_decl ~poly sigma udecl in
        (*FIXME poly? *)
        let ce = definition_entry ~types:ty ~univs (EConstr.to_constr sigma body) in
        (* FIXME: include locality *)
        let c = Declare.declare_constant ~name:recname ~kind:Decls.(IsDefinition Definition) (DefinitionEntry ce) in
        let gr = GlobRef.ConstRef c in
        if Impargs.is_implicit_args () || not (List.is_empty impls) then
          Impargs.declare_manual_implicits false gr impls
      in
      let typ = it_mkProd_or_LetIn top_arity binders in
      hook, name, typ
    else
      let typ = it_mkProd_or_LetIn top_arity binders_rel in
      let hook { Declare.Hook.S.dref; _ } =
        if Impargs.is_implicit_args () || not (List.is_empty impls) then
          Impargs.declare_manual_implicits false dref impls
      in hook, recname, typ
  in
  let hook = Declare.Hook.make hook in
  RetrieveObl.check_evars env sigma;
  let evars, _, evars_def, evars_typ =
    RetrieveObl.retrieve_obligations env recname sigma 0 def typ
  in
  let using =
    let terms = List.map EConstr.of_constr [evars_def; evars_typ] in
    Option.map (fun using -> Proof_using.definition_using env sigma ~fixnames:[] ~using ~terms) using
  in
  let uctx = Evd.evar_universe_context sigma in
  let cinfo = Declare.CInfo.make ~name:recname ~typ:evars_typ () in
  let kind = Decls.(IsDefinition Fixpoint) in
  let info = Declare.Info.make ?scope ?clearbody ~kind ~poly ~udecl ~hook ?typing_flags ?user_warns ~ntns ?using () in
  let pm, _ =
    Declare.Obls.add_definition ~pm ~cinfo ~info ~term:evars_def ~uctx evars in
  pm

let out_def = function
  | Some def -> def
  | None -> user_err Pp.(str "Program Fixpoint needs defined bodies.")

let collect_evars_of_term evd c ty =
  Evar.Set.union (Evd.evars_of_term evd c) (Evd.evars_of_term evd ty)

let do_program_recursive ~pm ~scope ?clearbody ~poly ?typing_flags ?user_warns ?using fixkind fixl =
  let cofix = fixkind = Declare.Obls.IsCoFixpoint in
  let (env, rec_sign, udecl, evd), fix, info =
    let env = Global.env () in
    let env = Environ.update_typing_flags ?typing_flags env in
    interp_recursive env ~cofix ~program_mode:true fixl
  in
    (* Program-specific code *)
    (* Get the interesting evars, those that were not instantiated *)
  let evd = Typeclasses.resolve_typeclasses ~filter:Typeclasses.no_goals ~fail:true env evd in
    (* Solve remaining evars *)
  let evd = nf_evar_map_undefined evd in
  let (fixnames,fixrs,fixdefs,fixtypes) = fix in
  let collect_evars name def typ impargs =
    (* Generalize by the recursive prototypes  *)
    let def = nf_evar evd (EConstr.it_mkNamedLambda_or_LetIn evd def rec_sign) in
    let typ = nf_evar evd (EConstr.it_mkNamedProd_or_LetIn evd typ rec_sign) in
    let deps = collect_evars_of_term evd def typ in
    let evars, _, def, typ =
      RetrieveObl.retrieve_obligations env name evd
        (List.length rec_sign) ~deps def typ in
    let cinfo = Declare.CInfo.make ~name ~typ ~impargs () in
    (cinfo, def, evars)
  in
  let fiximps = List.map pi2 info in
  let fixdefs = List.map out_def fixdefs in
  let defs = List.map4 collect_evars fixnames fixdefs fixtypes fiximps in
  let using =
    let terms = fixdefs @ fixtypes in
    Option.map (fun using -> Proof_using.definition_using env evd ~fixnames ~using ~terms) using in
  let () = if not cofix then begin
      let possible_indexes = List.map ComFixpoint.compute_possible_guardness_evidences info in
      (* XXX: are we allowed to have evars here? *)
      let fixtypes = List.map (EConstr.to_constr ~abort_on_undefined_evars:false evd) fixtypes in
      let fixdefs = List.map (EConstr.Vars.subst_vars evd (List.rev fixnames)) fixdefs in
      let fixdefs = List.map (EConstr.to_constr ~abort_on_undefined_evars:false evd) fixdefs in
      let fixdecls = Array.of_list (List.map2 (fun x r -> make_annot (Name x) r) fixnames fixrs),
        Array.of_list fixtypes,
        Array.of_list fixdefs
      in
      let evars = Evd.evar_handler evd in
      let indexes =
        let env = Global.env () in
        let env = Environ.update_typing_flags ?typing_flags env in
        Pretyping.search_guard ~evars env possible_indexes fixdecls in
      let env = Environ.update_typing_flags ?typing_flags env in
      List.iteri (fun i _ ->
          Inductive.check_fix ~evars env
            ((indexes,i),fixdecls))
        fixl
  end in
  let uctx = Evd.evar_universe_context evd in
  let kind = match fixkind with
  | Declare.Obls.IsFixpoint _ -> Decls.(IsDefinition Fixpoint)
  | Declare.Obls.IsCoFixpoint -> Decls.(IsDefinition CoFixpoint)
  in
  let ntns = List.map_append (fun { Vernacexpr.notations } -> List.map Metasyntax.prepare_where_notation notations ) fixl in
  let info = Declare.Info.make ~poly ~scope ?clearbody ~kind ~udecl ?typing_flags ?user_warns ~ntns ?using () in
  Declare.Obls.add_mutual_definitions ~pm defs ~info ~uctx fixkind

let do_fixpoint ~pm ~scope ?clearbody ~poly ?typing_flags ?user_warns ?using l =
  let g = List.map (fun { Vernacexpr.rec_order } -> rec_order) l in
    match g, l with
    | [Some { CAst.v = CWfRec (n,r) }],
      [ Vernacexpr.{fname={CAst.v=id}; univs; binders; rtype; body_def; notations} ] ->
        let recarg = mkIdentC n.CAst.v in
        build_wellfounded pm (id, univs, binders, rtype, out_def body_def) ~scope ?clearbody poly ?typing_flags ?user_warns ?using r recarg notations

    | [Some { CAst.v = CMeasureRec (n, m, r) }],
      [Vernacexpr.{fname={CAst.v=id}; univs; binders; rtype; body_def; notations }] ->
      (* We resolve here a clash between the syntax of Program Fixpoint and the one of funind *)
      let r = match n, r with
        | Some id, None ->
          let loc = id.CAst.loc in
          Some (CAst.make ?loc @@ CRef(qualid_of_ident ?loc id.CAst.v,None))
        | Some _, Some _ ->
          user_err Pp.(str"Measure takes only two arguments in Program Fixpoint.")
        | _, _ -> r
      in
        build_wellfounded pm (id, univs, binders, rtype, out_def body_def) ~scope ?clearbody poly ?typing_flags ?user_warns ?using
          (Option.default (CAst.make @@ CRef (lt_ref,None)) r) m notations

    | _, _ when List.for_all (fun ro -> match ro with None | Some { CAst.v = CStructRec _} -> true | _ -> false) g ->
      let annots = List.map (fun fix ->
          Vernacexpr.(ComFixpoint.adjust_rec_order ~structonly:true fix.binders fix.rec_order)) l in
      let fixkind = Declare.Obls.IsFixpoint annots in
      let l = List.map2 (fun fix rec_order -> { fix with Vernacexpr.rec_order }) l annots in
      do_program_recursive ~pm ~scope ?clearbody ~poly ?typing_flags ?user_warns ?using fixkind l
    | _, _ ->
      CErrors.user_err
        (str "Well-founded fixpoints not allowed in mutually recursive blocks.")

let do_cofixpoint ~pm ~scope ?clearbody ~poly ?typing_flags ?user_warns ?using fixl =
  let fixl = List.map (fun fix -> { fix with Vernacexpr.rec_order = None }) fixl in
  do_program_recursive ~pm ~scope ?clearbody ~poly ?typing_flags ?user_warns ?using Declare.Obls.IsCoFixpoint fixl
