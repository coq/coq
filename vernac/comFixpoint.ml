(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module CVars = Vars

open Pp
open Util
open Names
open Context
open EConstr
open Constrexpr
open Constrintern
open Vernacexpr

module RelDecl = Context.Rel.Declaration
module NamedDecl = Context.Named.Declaration

(* 3c| Fixpoints and co-fixpoints *)

(* An (unoptimized) function that maps preorders to partial orders...

   Input:  a list of associations (x,[y1;...;yn]), all yi distincts
           and different of x, meaning x<=y1, ..., x<=yn

   Output: a list of associations (x,Inr [y1;...;yn]), collecting all
           distincts yi greater than x, _or_, (x, Inl y) meaning that
           x is in the same class as y (in which case, x occurs
           nowhere else in the association map)

   partial_order : ('a * 'a list) list -> ('a * ('a,'a list) union) list
*)

let rec partial_order cmp = function
  | [] -> []
  | (x,xge)::rest ->
    let rec browse res xge' = function
    | [] ->
        let res = List.map (function
          | (z, Inr zge) when List.mem_f cmp x zge ->
            (z, Inr (List.union cmp zge xge'))
          | r -> r) res in
        (x,Inr xge')::res
    | y::xge ->
      let rec link y =
        try match List.assoc_f cmp y res with
        | Inl z -> link z
        | Inr yge ->
          if List.mem_f cmp x yge then
            let res = List.remove_assoc_f cmp y res in
            let res = List.map (function
              | (z, Inl t) ->
                  if cmp t y then (z, Inl x) else (z, Inl t)
              | (z, Inr zge) ->
                  if List.mem_f cmp y zge then
                    (z, Inr (List.add_set cmp x (List.remove cmp y zge)))
                  else
                    (z, Inr zge)) res in
            browse ((y,Inl x)::res) xge' (List.union cmp xge yge)
          else
            browse res (List.add_set cmp y (List.union cmp xge' yge)) xge
        with Not_found -> browse res (List.add_set cmp y xge') xge
      in link y
    in browse (partial_order cmp rest) [] xge

let string_of_kind = function
  | Decls.IsDefinition Fixpoint -> "fixpoint"
  | IsDefinition CoFixpoint -> "cofixpoint"
  | _ -> "declaration"

let non_full_mutual_message x xge y yge kind rest =
  let reason =
    if Id.List.mem x yge then
      Id.print y ++ str " depends on " ++ Id.print x ++ strbrk " but not conversely"
    else if Id.List.mem y xge then
      Id.print x ++ str " depends on " ++ Id.print y ++ strbrk " but not conversely"
    else
      Id.print y ++ str " and " ++ Id.print x ++ strbrk " are not mutually dependent" in
  let e = if List.is_empty rest then reason else strbrk "e.g., " ++ reason in
  let w =
    if kind <> Decls.IsDefinition CoFixpoint
    then strbrk "Well-foundedness check may fail unexpectedly." ++ fnl()
    else mt () in
  strbrk "Not a fully mutually defined " ++ str (string_of_kind kind) ++ fnl () ++
  str "(" ++ e ++ str ")." ++ fnl () ++ w

let warn_non_full_mutual =
  CWarnings.create ~name:"non-full-mutual" ~category:CWarnings.CoreCategories.fixpoints
         (fun (x,xge,y,yge,kind,rest) ->
          non_full_mutual_message x xge y yge kind rest)

let warn_non_recursive =
  CWarnings.create ~name:"non-recursive" ~category:CWarnings.CoreCategories.fixpoints
         (fun (x,kind) ->
          strbrk "Not a truly recursive " ++ str (string_of_kind kind) ++ str ".")

let check_true_recursivity env evd ~kind fixl =
  let names = List.map fst fixl in
  let preorder =
    List.map (fun (id,def) ->
      (id, List.filter (fun id' -> Termops.occur_var env evd id' def) names))
      fixl in
  let po = partial_order Id.equal preorder in
  match List.filter (function (_,Inr _) -> true | _ -> false) po with
    | (x,Inr xge)::(y,Inr yge)::rest ->
       warn_non_full_mutual (x,xge,y,yge,kind,rest)
    | _ ->
  match po with
    | [x,Inr []] -> warn_non_recursive (x,kind)
    | _ -> ()

(*****************************************************)
(* Utilities for Program Fixpoint with wf or measure *)

open Rocqlib
let init_constant sigma rf = Evd.fresh_global sigma rf
let fix_sub_ref () = lib_ref "program.wf.fix_sub"
let measure_on_R_ref () = lib_ref "program.wf.mr"
let well_founded sigma = init_constant (Global.env ()) sigma (lib_ref "core.wf.well_founded")
let mkSubset sigma name typ prop =
  let open EConstr in
  let sigma, app_h = Evd.fresh_global (Global.env ()) sigma (delayed_force build_sigma).typ in
  sigma, mkApp (app_h, [| typ; mkLambda (make_annot name ERelevance.relevant, typ, prop) |])

let ensure_program () =
  try fix_sub_ref (), measure_on_R_ref ()
  with NotFoundRef r ->
    CErrors.user_err
      Pp.(str r ++ spc() ++ str "not registered," ++ spc() ++
          str "you should try requiring library Corelib.Program.Wf.")

let recproofid = Id.of_string "recproof"
let argname = Id.of_string "recarg"

let encapsulate_Fix_sub env sigma recname ctx body ccl (extradecl, rel, relargty, measure_body) =
  let len = Context.Rel.length ctx in
  let fix_sub_ref, measure_on_R_ref = ensure_program () in
  (* We curry the binders [x1:A1;...;xn:An] into [x:{x1&...&xn};x1:=x.1;...;xn:=x.2...2] *)
  (* argtyp is [{x1&...&xn}], letbinders is [x1:=x.1;...;xn:=x.2...2], argvalue is [(x.1,...,x.2...2)] *)
  let open Combinators in
  let sigma, letbinders, {telescope_type = tuple_type; telescope_value = tuple_value} =
    telescope env sigma ctx in
  let tupled_ctx = letbinders @ [LocalAssum (make_annot (Name argname) ERelevance.relevant, tuple_type)] in
  (* The function measure has type [tuple_type -> relargty] *)
  let measure = it_mkLambda_or_LetIn measure_body tupled_ctx in
  (* The relation wf_rel_measure is [fun x y => rel (measure x) (measure y)] *)
  let sigma, comb = Evd.fresh_global (Global.env ()) sigma measure_on_R_ref in
  let rel_measure = mkApp (comb, [| tuple_type; relargty; rel; measure |]) in
  (* The statement that rel_measure is well-founded *)
  let sigma, wf_term = well_founded sigma in
  let wf_type = mkApp (wf_term, [| tuple_type ; rel_measure |]) in
  (* A combinator building [rel (measure x) (measure y)] *)
  let tupled_measure_body = it_mkLambda_or_LetIn measure_body letbinders in
  let make_applied_rel x y =
    mkApp (rel, [| Vars.subst1 x tupled_measure_body; Vars.subst1 y tupled_measure_body |]) in
  (* Conclusion of fixpoint in currified context *)
  let tupled_ccl = it_mkLambda_or_LetIn ccl letbinders in
  (* Making Fix_sub ready to take the extended body as argument *)
  let sigma, fix_sub =
    let sigma, fix_sub_term = Evd.fresh_global (Global.env ()) sigma fix_sub_ref in
    let sigma, wf_proof = Evarutil.new_evar env sigma
        ~src:(Loc.tag @@ Evar_kinds.QuestionMark {
            Evar_kinds.default_question_mark with Evar_kinds.qm_obligation=Evar_kinds.Define false;
          }) wf_type in
    let sigma = Evd.set_obligation_evar sigma (fst (destEvar sigma wf_proof)) in
    let ccl_pred = mkLambda (make_annot (Name argname) ERelevance.relevant, tuple_type, tupled_ccl) in
    let def = mkApp (fix_sub_term, [| tuple_type ; rel_measure ; wf_proof ; ccl_pred |]) in
    Typing.solve_evars env sigma def in
  let arg = RelDecl.LocalAssum (make_annot (Name argname) ERelevance.relevant, tuple_type) in
  let argid' = Id.of_string (Id.to_string argname ^ "'") in
  let sigma, wfa =
    let sigma, ss_term = mkSubset sigma (Name argid') tuple_type (make_applied_rel (mkRel 1) (mkRel 2)) in
    sigma, RelDecl.LocalAssum (make_annot (Name argid') ERelevance.relevant, ss_term) in
  let sigma, fix_sub_F_sub_ctx =
    let sigma, proj = Evd.fresh_global (Global.env ()) sigma (delayed_force build_sigma).Rocqlib.proj1 in
    let wfargpred = mkLambda (make_annot (Name argid') ERelevance.relevant, tuple_type, make_applied_rel (mkRel 1) (mkRel 3)) in
    let projection = (* in wfarg :: arg :: before *)
      mkApp (proj, [| tuple_type ; wfargpred ; mkRel 1 |])
    in
    let ccl_on_smaller_arg = Vars.substl [projection] (it_mkLambda_or_LetIn ccl letbinders) in
    (* substitute the projection of wfarg for something,
             now ccl_let is in wfarg :: arg *)
    let ccl_on_smaller_arg = it_mkProd_or_LetIn ccl_on_smaller_arg [wfa] in
    let recname' = Nameops.add_suffix recname "'" in
    let smaller_arg = RelDecl.LocalAssum (make_annot (Name recname') ERelevance.relevant,
                                          ccl_on_smaller_arg) in
    sigma, Vars.lift_rel_context 1 letbinders @ smaller_arg :: [arg] in
  let sigma, curryfier_body, curryfier_ty =
    (* In tupled_context where the function argument of Fix_sub (argid'), is inserted,
       that is, all expanded: [recarg;argid';letbinders], build the curryfying combinator
       [fun ctx (recproof : rel (measure ctx) (measure tupled_context)) => argid' (tuple_value,recproof)]
       of type
       [forall ctx (recproof : rel (measure ctx) (measure tupled_context)) => ccl] *)
    let sigma, intro = Evd.fresh_global (Global.env ()) sigma (delayed_force build_sigma).Rocqlib.intro in
    let app =
      let wfpred = mkLambda (make_annot (Name argid') ERelevance.relevant, tuple_type, make_applied_rel (mkRel 1) (mkRel (2 * len + 4))) in
      (* Build the sig pair [exist _ tuple_value recproof] *)
      let arg = mkApp (intro, [| tuple_type; wfpred; Vars.lift 1 tuple_value; mkRel 1 |]) in
      (* Build the body of combinator *)
      mkApp (mkRel (2 * len + 2 (* recproof + orig binders + current binders *)), [| arg |]) in
    let extended_ctx = extradecl :: ctx in
    let body = it_mkLambda_or_LetIn app extended_ctx in
    let ty = it_mkProd_or_LetIn (Vars.lift 1 ccl) extended_ctx in
    sigma, body, ty in
  (* Rephrase the body of the fixpoint as dependent in the telescope *)
  let body_ctx = RelDecl.LocalDef (make_annot (Name recname) ERelevance.relevant, curryfier_body, curryfier_ty) :: fix_sub_F_sub_ctx in
  let intern_body_lam = it_mkLambda_or_LetIn body body_ctx in
  (* Instantiate the argument Fix_sub_F of Fix_sub with the body of the fixpoint *)
  let sigma, fix_sub = Typing.solve_evars env sigma fix_sub in
  sigma, tupled_ctx, tuple_value, mkApp (fix_sub, [|intern_body_lam|])

let build_wellfounded env sigma poly udecl recname ctx body ccl impls rel_measure =
  let len = Context.Rel.length ctx in
  (* Restore body in the context of binders + extradecl *)
  let _, body = decompose_lambda_n_decls sigma (len + 1) body in
  (* Restore ccl in the context of binders *)
  let ccl = Vars.subst1 (mkRel 1) (snd (decompose_prod_n_decls sigma (len + 1) ccl)) in
  (* Apply the body to Program.Wf.Fix_sub *)
  let sigma, tupled_ctx, tuple_value, def = encapsulate_Fix_sub env sigma recname ctx body ccl rel_measure in
  (* Turn everything to constr *)
  let ctx = Evarutil.nf_rel_context_evar sigma ctx in
  let tupled_ctx = Evarutil.nf_rel_context_evar sigma tupled_ctx in
  let ccl = Evarutil.nf_evar sigma ccl in
  let tuple_value = Evarutil.nf_evar sigma tuple_value in
  (* Decide if using a curryfied indirection via recname_func *)
  let recname_func, typ =
    if len > 1 then
      Nameops.add_suffix recname "_func", it_mkProd_or_LetIn ccl tupled_ctx
    else
      recname, it_mkProd_or_LetIn ccl ctx in
  let body, typ, _uctx, evmap, obls =
    Declare.Obls.prepare_obligations ~name:recname_func ~body:def ~types:typ env sigma in
  let hook, impls =
    if len > 1 then
      let hook { Declare.Hook.S.dref; uctx; obls; _ } =
        let update c = CVars.replace_vars obls (evmap mkVar (Evarutil.nf_evar (Evd.from_ctx uctx) c)) in
        let tuple_value = update tuple_value in
        let ccl = update ccl in
        let ctx = Context.Rel.map_het (ERelevance.kind sigma) update ctx in
        let univs = UState.check_univ_decl ~poly uctx udecl in
        let h_body =
          let inst = UState.(match fst univs with
              | Polymorphic_entry uctx -> UVars.UContext.instance uctx
              | Monomorphic_entry _ -> UVars.Instance.empty) in
          Constr.mkRef (dref, inst) in
        let body = Term.it_mkLambda_or_LetIn (Constr.mkApp (h_body, [|tuple_value|])) ctx in
        let ty = Term.it_mkProd_or_LetIn ccl ctx in
        let ce = Declare.definition_entry ~types:ty ~univs body in
        (* FIXME: include locality *)
        let c = Declare.declare_constant ~name:recname ~kind:Decls.(IsDefinition Definition) (DefinitionEntry ce) in
        let gr = GlobRef.ConstRef c in
        if Impargs.is_implicit_args () || not (List.is_empty impls) then
          Impargs.declare_manual_implicits false gr impls
      in
      Some (Declare.Hook.make hook), []
    else
      None, impls
  in
  sigma, recname_func, body, typ, impls, obls, hook

(*********************************)
(* Interpretation of Co/Fixpoint *)

let make_qref s = Libnames.qualid_of_string s
let lt_ref = make_qref "Init.Peano.lt"

let position_of_argument ctx binders na =
  let exception Found of int in
  let name = Name na.CAst.v in
  try
    Context.Rel.fold_outside (fun decl n ->
        match Context.Rel.Declaration.(get_value decl, Name.equal (get_name decl) name) with
        | None, true -> raise (Found n)
        | Some _, true ->
          let loc = List.find_map (fun id -> if Name.equal name id.CAst.v then Some id.CAst.loc else None) (Constrexpr_ops.names_of_local_binders binders) in
          let loc = Option.default na.CAst.loc loc in
          CErrors.user_err ?loc
            (Name.print name ++ str" must be a proper parameter and not a local definition.")
        | None, false -> n + 1
        | Some _, false -> n (* let-ins don't count *))
      ~init:0 ctx |> ignore;
    CErrors.user_err ?loc:na.loc
      (str "No parameter named " ++ Id.print na.v ++ str".");
  with
    Found k -> k

(* Interpret the index of a recursion order annotation *)
let find_rec_annot ~program_mode ~function_mode env sigma Vernacexpr.{fname={CAst.loc}; binders} ctx typ = function
  | None ->
    let ctx', _ = Reductionops.whd_decompose_prod_decls (push_rel_context ctx env) sigma typ in
    let n = Context.Rel.nhyps ctx + Context.Rel.nhyps ctx' in
    if Int.equal n 0 then CErrors.user_err ?loc Pp.(str "A fixpoint needs at least one parameter.");
    None, List.interval 0 (n - 1)
  | Some CAst.{v=rec_order;loc} ->
    let default_order r = Option.default (CAst.make @@ CRef (lt_ref,None)) r in
    match rec_order with
    | CStructRec na -> None, [position_of_argument ctx binders na]
    | CWfRec (na,r) ->
      if function_mode then None, []
      else Some (r, Constrexpr_ops.mkIdentC na.CAst.v), [] (* useless for Program: will use Fix_sub *)
    | CMeasureRec (na, mes, rfel) ->
      if function_mode then
        let _ = match binders, na with
          | [CLocalDef({ CAst.v = Name id },_,_,_) | CLocalAssum([{ CAst.v = Name id }],_,_,_)], None -> ()
          | _, None -> CErrors.user_err ?loc Pp.(str "Decreasing argument must be specified in measure clause.")
          | _, Some na -> (* check that the name exists *) ignore (position_of_argument ctx binders na) in
        (* Dummy *) None, []
      else
        let r = match na, rfel with
          | Some id, None ->
            let loc = id.CAst.loc in
            CAst.make ?loc @@ CRef (Libnames.qualid_of_ident ?loc id.CAst.v,None)
          | Some _, Some _ -> CErrors.user_err ?loc Pp.(str"Measure takes three arguments only in Function.")
          | None, rfel -> default_order rfel in
        Some (r, mes), [] (* useless: will use Fix_sub *)

let interp_rec_annot ~program_mode ~function_mode env sigma fixl ctxl ccll rec_order =
  let open Pretyping in
  let nowf () = List.map (fun _ -> None) fixl in
  match rec_order with
    (* If recursive argument was not given by user, we try all args.
       An earlier approach was to look only for inductive arguments,
       but doing it properly involves delta-reduction, and it finally
       doesn't seem to worth the effort (except for huge mutual
       fixpoints ?) *)
    | CFixRecOrder fix_orders ->
      let fixwf, possible_guard = List.split (List.map4 (find_rec_annot ~program_mode ~function_mode env sigma) fixl ctxl ccll fix_orders) in
      fixwf, {possibly_cofix = false; possible_fix_indices = possible_guard}
    | CCoFixRecOrder -> nowf (), {possibly_cofix = true; possible_fix_indices = List.map (fun _ -> []) fixl}
    | CUnknownRecOrder -> nowf (), RecLemmas.find_mutually_recursive_statements sigma ctxl ccll

let interp_fix_context ~program_mode env sigma {Vernacexpr.binders} =
  let sigma, (impl_env, ((env', ctx), imps)) = interp_context_evars ~program_mode env sigma binders in
  sigma, (env', ctx, impl_env, imps)

let interp_fix_ccl ~program_mode sigma impls env fix =
  let flags = Pretyping.{ all_no_fail_flags with program_mode } in
  let sigma, (c, impl) = interp_type_evars_impls ~flags ~impls env sigma fix.Vernacexpr.rtype in
  let r = Retyping.relevance_of_type env sigma c in
  sigma, (c, r, impl)

let interp_fix_body ~program_mode env_rec ctx sigma impls fix ccl =
  Option.cata (fun body ->
    let env_rec_ctx = push_rel_context ctx env_rec in
    let sigma, body = interp_casted_constr_evars ~program_mode env_rec_ctx sigma ~impls body ccl in
    sigma, Some (it_mkLambda_or_LetIn body ctx)) (sigma, None) fix.Vernacexpr.body_def

let build_fix_type sigma ctx ccl (_, extradecl) =
  let ccl = it_mkProd_or_LetIn (Vars.lift (Context.Rel.length extradecl) ccl) extradecl in
  Evarutil.nf_evar sigma (it_mkProd_or_LetIn ccl ctx)

let build_dummy_fix_type sigma ctx ccl (_, extradecl) =
  (* Hack: the extra declarations are smashed to a dummy non-dependent
     so as not to contribute to the computation of implicit arguments *)
  let ccl = it_mkProd_or_LetIn (Vars.lift (Context.Rel.length extradecl) ccl) (List.map (RelDecl.map_type (fun _ -> mkProp)) extradecl) in
  Evarutil.nf_evar sigma (it_mkProd_or_LetIn ccl ctx)

(* Wellfounded definition *)

let encapsulate env sigma r t =
  (* Would probably be overkill to use a specific fix_proto in SProp when in SProp?? *)
  let fix_proto sigma =
    Evd.fresh_global (Global.env ()) sigma (Rocqlib.lib_ref "program.tactic.fix_proto") in
  let fix_proto_relevance = EConstr.ERelevance.relevant in
  let sigma, sort = Typing.type_of ~refresh:true env sigma t in
  try
    let sigma, h_term = fix_proto sigma in
    let app = EConstr.mkApp (h_term, [|sort; t|]) in
    let sigma, app = Typing.solve_evars env sigma app in
    sigma, fix_proto_relevance, app
  with e when CErrors.noncritical e -> sigma, r, t

type ('constr, 'relevance) fix_data = {
  fixnames : Names.Id.t list;
  fixrs    : 'relevance list;
  fixdefs  : 'constr option list;
  fixtypes : 'constr list;
  fixctxs  :  EConstr.rel_context list;
  fiximps  : (Names.Name.t * bool) option CAst.t list list;
  fixntns  : Metasyntax.notation_interpretation_decl list;
  fixwfs   : (rel_declaration * EConstr.t * EConstr.t * EConstr.t) option list;
}

let interp_wf ~program_mode env sigma recname ctx ccl = function
  | None -> sigma, ((false, []), None, [])
  | Some (r, measure) ->
    (* We have to insert an argument for the measure/wellfoundedness *)
    (* The extra implicit argument *)
    let impl = CAst.make (Some (Name recproofid, true)) in
    (* The well-founded relation *)
    let env_ctx = push_rel_context ctx env in
    let sigma, (rel, _) = interp_constr_evars_impls ~program_mode env sigma r in
    let relargty = Hipattern.is_homogeneous_relation ?loc:(Constrexpr_ops.constr_loc r) env_ctx sigma rel in
    (* The measure *)
    let sigma, measure = interp_casted_constr_evars ~program_mode env_ctx sigma measure relargty in
    let sigma, after, extradecl =
      if program_mode then
        let len = Context.Rel.length ctx in
        let applied_rel_measure = mkApp (rel, [| measure; Vars.lift len measure |]) in
        let extradecl = RelDecl.LocalAssum (make_annot (Name recproofid) ERelevance.relevant, applied_rel_measure) in
        sigma, true, extradecl
      else
        let sigma, wf_term = well_founded sigma in
        let applied_wf = mkApp (wf_term, [| relargty; rel; measure |]) in
        let extradecl = RelDecl.LocalAssum (make_annot (Name recproofid) ERelevance.relevant, applied_wf) in
        sigma, false, extradecl
    in
    sigma, ((after, [extradecl]), Some (extradecl, rel, relargty, measure), [impl])

let interp_mutual_definition env ~program_mode ~function_mode rec_order fixl =
  let open Context.Named.Declaration in
  let open EConstr in
  let fixnames = List.map (fun fix -> fix.Vernacexpr.fname.CAst.v) fixl in

  (* Interp arities allowing for unresolved types *)
  let sigma, decl = interp_mutual_univ_decl_opt env (List.map (fun Vernacexpr.{univs} -> univs) fixl) in
  let sigma, (fixenv, fixctxs, fixctximpenvs, fixctximps) =
    on_snd List.split4 @@
      List.fold_left_map (fun sigma -> interp_fix_context ~program_mode env sigma) sigma fixl in
  let sigma, (fixccls,fixrs,fixcclimps) =
    on_snd List.split3 @@
      List.fold_left3_map (interp_fix_ccl ~program_mode) sigma fixctximpenvs fixenv fixl in
  let fixwfs, possible_guard = interp_rec_annot ~program_mode ~function_mode env sigma fixl fixctxs fixccls rec_order in
  let sigma, (fixextras, fixwfs, fixwfimps) =
    on_snd List.split3 @@ (List.fold_left4_map (interp_wf ~program_mode env) sigma fixnames fixctxs fixccls fixwfs) in
  let fixtypes = List.map3 (build_fix_type sigma) fixctxs fixccls fixextras in
  let sigma, rec_sign =
    List.fold_left4
      (fun (sigma, rec_sign) id r t (_,extradecl) ->
         let sigma, r, t = if program_mode && List.is_empty extradecl then encapsulate env sigma r t else sigma, r, t in
         sigma, LocalAssum (Context.make_annot id r, t) :: rec_sign)
      (sigma, []) fixnames fixrs fixtypes fixextras
  in
  let fixrecimps = List.map3 (fun ctximps wfimps cclimps -> ctximps @ wfimps @ cclimps) fixctximps fixwfimps fixcclimps in
  let fiximps = List.map2 (fun ctximps cclimps -> ctximps @ cclimps) fixctximps fixcclimps in

  (* Interp bodies with rollback because temp use of notations/implicit *)
  let fixntns = List.map_append (fun { Vernacexpr.notations } -> List.map Metasyntax.prepare_where_notation notations ) fixl in
  let sigma, fixdefs =
    let force = List.map (fun (_,extra) -> Id.Set.of_list (List.map_filter (fun d -> Nameops.Name.to_option (RelDecl.get_name d)) extra)) fixextras in
    let dummy_fixtypes = List.map3 (build_dummy_fix_type sigma) fixctxs fixccls fixextras in
    let impls = compute_internalization_env env sigma ~force Recursive fixnames dummy_fixtypes fixrecimps in
    Metasyntax.with_syntax_protection (fun () ->
      List.iter (Metasyntax.set_notation_for_interpretation env impls) fixntns;
      List.fold_left5_map
        (fun sigma fixctximpenv (after,extradecl) ctx body ccl ->
           let impls = Id.Map.fold Id.Map.add fixctximpenv impls in
           let env', ctx =
             if after then env, List.map NamedDecl.to_rel_decl rec_sign @ ctx
             else push_named_context rec_sign env, extradecl@ctx in
           interp_fix_body ~program_mode env' ctx sigma impls body (Vars.lift (Context.Rel.length extradecl) ccl))
        sigma fixctximpenvs fixextras fixctxs fixl fixccls)
      () in

  (* Instantiate evars and check all are resolved *)
  let sigma = Evarconv.solve_unif_constraints_with_heuristics env sigma in
  let sigma = Evd.minimize_universes sigma in

  (* Build the fix declaration block *)
  let fix = {fixnames;fixrs;fixdefs;fixtypes;fixctxs;fiximps;fixntns;fixwfs} in
  (env, rec_sign, sigma), (fix, possible_guard, decl)

let check_recursive ~kind env evd {fixnames;fixdefs;fixwfs} =
  (* TO MOVE AT FINAL DEFINITION TIME? *)
  if List.for_all Option.has_some fixdefs && List.for_all Option.is_empty fixwfs then begin
    let fixdefs = List.map Option.get fixdefs in
    check_true_recursivity env evd ~kind (List.combine fixnames fixdefs)
  end

let ground_fixpoint env evd {fixnames;fixrs;fixdefs;fixtypes;fixctxs;fiximps;fixntns;fixwfs} =
  Pretyping.check_evars_are_solved ~program_mode:false env evd;
  let fixrs = List.map (fun r -> EConstr.ERelevance.kind evd r) fixrs in
  let fixdefs = List.map (fun c -> Option.map EConstr.(to_constr evd) c) fixdefs in
  let fixtypes = List.map EConstr.(to_constr evd) fixtypes in
  {fixnames;fixrs;fixdefs;fixtypes;fixctxs;fiximps;fixntns;fixwfs}

(** For Funind *)

let interp_fixpoint_short rec_order fixpoint_exprl =
  let env = Global.env () in
  let (_, _, sigma),(fix, _, _) = interp_mutual_definition ~program_mode:false ~function_mode:true env (CFixRecOrder rec_order) fixpoint_exprl in
  let sigma = Pretyping.(solve_remaining_evars all_no_fail_flags env sigma) in
  let typel = (ground_fixpoint env sigma fix).fixtypes in
  typel, sigma

let build_recthms {fixnames;fixtypes;fixctxs;fiximps} =
  List.map4 (fun name typ ctx impargs ->
      let args = List.map Context.Rel.Declaration.get_name ctx in
      Declare.CInfo.make ~name ~typ ~args ~impargs ()
    ) fixnames fixtypes fixctxs fiximps

let collect_evars_of_term evd c ty =
  Evar.Set.union (Evd.evars_of_term evd c) (Evd.evars_of_term evd ty)

let collect_evars env sigma rec_sign recname def typ =
  (* Generalize by the recursive prototypes  *)
  let deps = collect_evars_of_term sigma def typ in
  let evars, _, def, typ =
    RetrieveObl.retrieve_obligations env recname sigma
      (List.length rec_sign) ~deps def typ in
  (Some def, typ, evars)

let out_def = function
  | Some def -> def
  | None -> CErrors.user_err Pp.(str "Program Fixpoint needs defined bodies.")

let build_program_fixpoint env sigma rec_sign possible_guard fixnames fixrs fixdefs fixtypes fixwfs =
  assert (List.for_all Option.is_empty fixwfs);
  (* Get the interesting evars, those that were not instantiated *)
  let sigma = Typeclasses.resolve_typeclasses ~filter:Typeclasses.no_goals ~fail:true env sigma in
  (* Solve remaining evars *)
  let sigma = Evarutil.nf_evar_map_undefined sigma in
  let fixdefs = List.map out_def fixdefs in
  (* An early check of guardedness before working on the obligations *)
  let () =
    let fixdecls =
      Array.of_list (List.map2 (fun x r -> Context.make_annot (Name x) r) fixnames fixrs),
      Array.of_list fixtypes,
      Array.of_list fixdefs
    in
    ignore (Pretyping.esearch_guard env sigma possible_guard fixdecls) in
  List.split3 (List.map3 (collect_evars env sigma rec_sign) fixnames fixdefs fixtypes)

let finish_obligations env sigma rec_sign possible_guard poly udecl = function
  | {fixnames=[recname];fixrs;fixdefs=[body];fixtypes=[ccl];fixctxs=[ctx];fiximps=[imps];fixntns;fixwfs=[Some wf]} ->
    let sigma = Evarutil.nf_evar_map sigma in (* use nf_evar_map_undefined?? *)
    let sigma, recname, body, ccl, impls, obls, hook = build_wellfounded env sigma poly udecl recname ctx (Option.get body) ccl imps wf in
    let fixrs = List.map (EConstr.ERelevance.kind sigma) fixrs in
    sigma, {fixnames=[recname];fixrs;fixdefs=[Some body];fixtypes=[ccl];fixctxs=[ctx];fiximps=[impls];fixntns;fixwfs=[Some wf]}, [obls], hook
  | {fixnames;fixrs;fixdefs;fixtypes;fixctxs;fiximps;fixntns;fixwfs} ->
    let fixdefs, fixtypes, obls = build_program_fixpoint env sigma rec_sign possible_guard fixnames fixrs fixdefs fixtypes fixwfs in
    let fixrs = List.map (EConstr.ERelevance.kind sigma) fixrs in
    sigma, {fixnames;fixrs;fixdefs;fixtypes;fixctxs;fiximps;fixntns;fixwfs}, obls, None

let finish_regular env sigma use_inference_hook fix =
  let inference_hook = if use_inference_hook then Some Declare.Obls.program_inference_hook else None in
  let sigma = Pretyping.(solve_remaining_evars ?hook:inference_hook all_no_fail_flags env sigma) in
  sigma, ground_fixpoint env sigma fix, [], None

let do_mutually_recursive ?pm ~program_mode ?(use_inference_hook=false) ?scope ?clearbody ~kind ~poly ?typing_flags ?user_warns ?using (rec_order, fixl)
  : Declare.OblState.t option * Declare.Proof.t option =
  let env = Global.env () in
  let env = Environ.update_typing_flags ?typing_flags env in
  let (env,rec_sign,sigma),(fix,possible_guard,udecl) = interp_mutual_definition env ~program_mode ~function_mode:false rec_order fixl in
  check_recursive ~kind env sigma fix;
  let sigma, ({fixdefs=bodies;fixrs;fixtypes;fixwfs} as fix), obls, hook =
    match pm with
    | Some pm -> finish_obligations env sigma rec_sign possible_guard poly udecl fix
    | None -> finish_regular env sigma use_inference_hook fix in
  let info = Declare.Info.make ?scope ?clearbody ~kind ~poly ~udecl ?hook ?typing_flags ?user_warns ~ntns:fix.fixntns () in
  let cinfo = build_recthms fix in
  match pm with
  | Some pm ->
    (* Program Fixpoint struct *)
    let bodies = List.map Option.get bodies in
    Evd.check_univ_decl_early ~poly ~with_obls:true sigma udecl (bodies @ fixtypes);
    let sigma = if poly then sigma else Evd.fix_undefined_variables sigma in
    let uctx = Evd.ustate sigma in
    (match fixwfs, bodies, cinfo, obls with
    | [Some _], [body], [cinfo], [obls] ->
      (* Program Fixpoint wf/measure *)
      let pm, _ = Declare.Obls.add_definition ~pm ~cinfo ~info ~opaque:false ~body ~uctx ?using obls in
      Some pm, None
    | _ ->
      let possible_guard = (possible_guard, fixrs) in
      Some (Declare.Obls.add_mutual_definitions ~pm ~cinfo ~info ~opaque:false ~uctx ~bodies ~possible_guard ?using obls), None)
  | None ->
    try
      let bodies = List.map Option.get bodies in
      let uctx = Evd.ustate sigma in
      (* All bodies are defined *)
      let possible_guard = (possible_guard, fixrs) in
      let _ : GlobRef.t list =
        Declare.declare_mutual_definitions ~cinfo ~info ~opaque:false ~uctx ~possible_guard ~bodies ?using ()
      in
      None, None
    with Option.IsNone ->
      (* At least one undefined body *)
      Evd.check_univ_decl_early ~poly ~with_obls:false sigma udecl (Option.List.flatten bodies @ fixtypes);
      let possible_guard = (possible_guard, fixrs) in
      let lemma = Declare.Proof.start_mutual_definitions ~info ~cinfo ~bodies ~possible_guard ?using sigma in
      None, Some lemma
