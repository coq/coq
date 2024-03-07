(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module CVars = Vars

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

(* Wellfounded definition *)

open Coqlib

let init_constant sigma rf = Evd.fresh_global sigma rf
let fix_sub_ref () = lib_ref "program.wf.fix_sub"
let measure_on_R_ref () = lib_ref "program.wf.mr"
let well_founded sigma = init_constant (Global.env ()) sigma (lib_ref "core.wf.well_founded")

let mkSubset sigma name typ prop =
  let open EConstr in
  let sigma, app_h = Evd.fresh_global (Global.env ()) sigma (delayed_force build_sigma).typ in
  sigma, mkApp (app_h, [| typ; mkLambda (make_annot name ERelevance.relevant, typ, prop) |])

let make_qref s = qualid_of_string s
let lt_ref = make_qref "Init.Peano.lt"

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
  let arg = LocalAssum (make_annot (Name argname) ERelevance.relevant, argtyp) in
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
    sigma, LocalAssum (make_annot (Name argid') ERelevance.relevant, ss_term)
  in
  let sigma, intern_bl =
    let sigma, wfa = wfarg sigma 1 in
    sigma, wfa :: [arg]
  in
  let _intern_env = push_rel_context intern_bl env in
  let sigma, proj = Evd.fresh_global (Global.env ()) sigma (delayed_force build_sigma).Coqlib.proj1 in
  let wfargpred = mkLambda (make_annot (Name argid') ERelevance.relevant, argtyp, wf_rel_fun (mkRel 1) (mkRel 3)) in
  let projection = (* in wfarg :: arg :: before *)
    mkApp (proj, [| argtyp ; wfargpred ; mkRel 1 |])
  in
  let top_arity_let = it_mkLambda_or_LetIn top_arity letbinders in
  let intern_arity = substl [projection] top_arity_let in
  (* substitute the projection of wfarg for something,
     now intern_arity is in wfarg :: arg *)
  let sigma, wfa = wfarg sigma 1 in
  let intern_fun_arity_prod = it_mkProd_or_LetIn intern_arity [wfa] in
  let intern_fun_binder = LocalAssum (make_annot (Name (add_suffix recname "'")) ERelevance.relevant,
                                      intern_fun_arity_prod) in
  let recproofid = Id.of_string "recproof" in
  let sigma, curry_fun =
    let wfpred = mkLambda (make_annot (Name argid') ERelevance.relevant, argtyp, wf_rel_fun (mkRel 1) (mkRel (2 * len + 4))) in
    let sigma, intro = Evd.fresh_global (Global.env ()) sigma (delayed_force build_sigma).Coqlib.intro in
    let arg = mkApp (intro, [| argtyp; wfpred; lift 1 make; mkRel 1 |]) in
    let app = mkApp (mkRel (2 * len + 2 (* recproof + orig binders + current binders *)), [| arg |]) in
    let rcurry = mkApp (rel, [| measure; lift len measure |]) in
    let lam = LocalAssum (make_annot (Name recproofid) ERelevance.relevant, rcurry) in
    let body = it_mkLambda_or_LetIn app (lam :: binders_rel) in
    let ty = it_mkProd_or_LetIn (lift 1 top_arity) (lam :: binders_rel) in
    sigma, LocalDef (make_annot (Name recname) ERelevance.relevant, body, ty)
  in
  let fun_bl = intern_fun_binder :: [arg] in
  let lift_lets = lift_rel_context 1 letbinders in
  let sigma, intern_body =
    let ctx = LocalAssum (make_annot (Name recname) ERelevance.relevant, get_type curry_fun) :: binders_rel in
    let impl = CAst.make (Some (Name recproofid, true)) in
    let newimpls = impls @ impl :: arityimpls in
    let dummy_decl =
      (* Ensure the measure argument does not contribute to the computation of automatic implicit arguments *)
      LocalAssum (make_annot (Name recproofid) ERelevance.relevant, mkProp) in
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
  let prop = mkLambda (make_annot (Name argname) ERelevance.relevant, argtyp, top_arity_let) in
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
  let binders_rel = Evarutil.nf_rel_context_evar sigma binders_rel in
  let binders = Evarutil.nf_rel_context_evar sigma binders in
  let top_arity = Evarutil.nf_evar sigma top_arity in
  let make = Evarutil.nf_evar sigma make in
  let recname_func, typ =
    if List.length binders_rel > 1 then
      add_suffix recname "_func", it_mkProd_or_LetIn top_arity binders
    else
      recname, it_mkProd_or_LetIn top_arity binders_rel in
  let evars_def, evars_typ, uctx, evmap, evars =
    Declare.Obls.prepare_obligations ~name:recname_func ~body:def ~types:typ env sigma in
  let hook =
    if List.length binders_rel > 1 then
      let hook { Declare.Hook.S.dref; uctx; obls; _ } =
        let update c = CVars.replace_vars obls (evmap mkVar (Evarutil.nf_evar (Evd.from_ctx uctx) c)) in
        let make = update make in
        let top_arity = update top_arity in
        let binders_rel = Context.Rel.map_het (ERelevance.kind sigma) update binders_rel in
        let univs = UState.check_univ_decl ~poly uctx udecl in
        let h_body =
          let inst = UState.(match fst univs with
              | Polymorphic_entry uctx -> UVars.UContext.instance uctx
              | Monomorphic_entry _ -> UVars.Instance.empty) in
          Constr.mkRef (dref, inst) in
        let body = Term.it_mkLambda_or_LetIn (Constr.mkApp (h_body, [|make|])) binders_rel in
        let ty = Term.it_mkProd_or_LetIn top_arity binders_rel in
        let ce = definition_entry ~types:ty ~univs body in
        (* FIXME: include locality *)
        let c = Declare.declare_constant ~name:recname ~kind:Decls.(IsDefinition Definition) (DefinitionEntry ce) in
        let gr = GlobRef.ConstRef c in
        if Impargs.is_implicit_args () || not (List.is_empty impls) then
          Impargs.declare_manual_implicits false gr impls
      in
      hook
    else
      let hook { Declare.Hook.S.dref; _ } =
        if Impargs.is_implicit_args () || not (List.is_empty impls) then
          Impargs.declare_manual_implicits false dref impls
      in hook
  in
  let hook = Declare.Hook.make hook in
  let cinfo = Declare.CInfo.make ~name:recname_func ~typ:evars_typ () in
  let kind = Decls.(IsDefinition Fixpoint) in
  let info = Declare.Info.make ?scope ?clearbody ~kind ~poly ~udecl ~hook ?typing_flags ?user_warns ~ntns () in
  let pm, _ =
    Declare.Obls.add_definition ~pm ~cinfo ~info ~opaque:false ~body:evars_def ~uctx ?using evars in
  pm

let out_def = function
  | Some def -> def
  | None -> user_err Pp.(str "Program Fixpoint needs defined bodies.")

let collect_evars_of_term evd c ty =
  Evar.Set.union (Evd.evars_of_term evd c) (Evd.evars_of_term evd ty)

let do_program_recursive ~pm ~scope ?clearbody ~poly ?typing_flags ?user_warns ?using (rec_order, fixl) =
  let (env, rec_sign, evd), fix =
    let env = Global.env () in
    let env = Environ.update_typing_flags ?typing_flags env in
    interp_recursive_evars env ~program_mode:true (false, rec_order) fixl
  in
    (* Program-specific code *)
    (* Get the interesting evars, those that were not instantiated *)
  let evd = Typeclasses.resolve_typeclasses ~filter:Typeclasses.no_goals ~fail:true env evd in
    (* Solve remaining evars *)
  let evd = nf_evar_map_undefined evd in
  let ((fixnames,fixrs,fixdefs,fixtypes,fixctxs,fiximps),kind,possible_guard,udecl) = fix in
  let collect_evars name def typ impargs =
    (* Generalize by the recursive prototypes  *)
    let def = nf_evar evd def in
    let typ = nf_evar evd typ in
    let deps = collect_evars_of_term evd def typ in
    let evars, _, def, typ =
      RetrieveObl.retrieve_obligations env name evd
        (List.length rec_sign) ~deps def typ in
    (def, evars, typ)
  in
  let fixdefs = List.map out_def fixdefs in
  let bodies, obls, typs = List.split3 (List.map4 collect_evars fixnames fixdefs fixtypes fiximps) in
  let cinfo = List.map3 (fun name typ impargs -> Declare.CInfo.make ~name ~typ ~impargs ()) fixnames typs fiximps in
  let () =
    (* An early check of guardedness before working on the obligations *)
    let fixdecls =
      Array.of_list (List.map2 (fun x r -> make_annot (Name x) r) fixnames fixrs),
      Array.of_list fixtypes,
      Array.of_list fixdefs
    in
    ignore (Pretyping.esearch_guard env evd possible_guard fixdecls)
  in
  let uctx = Evd.evar_universe_context evd in
  let kind = Decls.(IsDefinition kind) in
  let ntns = List.map_append (fun { Vernacexpr.notations } -> List.map Metasyntax.prepare_where_notation notations ) fixl in
  let info = Declare.Info.make ~poly ~scope ?clearbody ~kind ~udecl ?typing_flags ?user_warns ~ntns () in
  Declare.Obls.add_mutual_definitions ~pm ~info ~cinfo ~opaque:false ~uctx ~bodies ~possible_guard ?using obls

let do_fixpoint ~pm ~scope ?clearbody ~poly ?typing_flags ?user_warns ?using (fix_order, l) =
  match fix_order, l with
    | [Some { CAst.v = CWfRec (n,r) }],
      [ Vernacexpr.{fname={CAst.v=id}; univs; binders; rtype; body_def; notations} ] ->
        let recarg = mkIdentC n.CAst.v in
        build_wellfounded pm (id, univs, binders, rtype, out_def body_def) ~scope ?clearbody poly ?typing_flags ?user_warns r recarg notations

    | [Some { CAst.v = CMeasureRec (n, m, r); loc }],
      [Vernacexpr.{fname={CAst.v=id}; univs; binders; rtype; body_def; notations }] ->
      (* We resolve here a clash between the syntax of Program Fixpoint and the one of funind *)
      let r = match n, r with
        | Some id, None ->
          let loc = id.CAst.loc in
          Some (CAst.make ?loc @@ CRef(qualid_of_ident ?loc id.CAst.v,None))
        | Some _, Some _ ->
          user_err ?loc Pp.(str"Measure takes only two arguments in Program Fixpoint.")
        | _, _ -> r
      in
        build_wellfounded pm (id, univs, binders, rtype, out_def body_def) ~scope ?clearbody poly ?typing_flags ?user_warns
          (Option.default (CAst.make @@ CRef (lt_ref,None)) r) m notations

    | _, _ when List.for_all (fun ro -> match ro with None | Some { CAst.v = CStructRec _} -> true | _ -> false) fix_order ->
      do_program_recursive ~pm ~scope ?clearbody ~poly ?typing_flags ?user_warns ?using (CFixRecOrder fix_order, l)
    | _, _ ->
      CErrors.user_err
        (str "Well-founded fixpoints not allowed in mutually recursive blocks.")

let do_cofixpoint ~pm ~scope ?clearbody ~poly ?typing_flags ?user_warns ?using fixl =
  do_program_recursive ~pm ~scope ?clearbody ~poly ?typing_flags ?user_warns ?using (CCoFixRecOrder, fixl)

let do_mutually_recursive ~pm ~scope ?clearbody ~poly ?typing_flags ?user_warns ?using (rec_order, l) =
  Vernacexpr.(match rec_order with
  | CFixRecOrder fix_order -> do_fixpoint ~pm ~scope ?clearbody ~poly ?typing_flags ?user_warns ?using (fix_order, l)
  | CCoFixRecOrder -> do_cofixpoint ~pm ~scope ?clearbody ~poly ?typing_flags ?user_warns ?using l
  | CUnknownRecOrder -> user_err Pp.(strbrk "Automatic detection of fix/cofix not implemented for Program."))
