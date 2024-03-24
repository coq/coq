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
open Util
open Names
open Constrexpr
open Constrintern
open Vernacexpr

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

let non_full_mutual_message x xge y yge isfix rest =
  let reason =
    if Id.List.mem x yge then
      Id.print y ++ str " depends on " ++ Id.print x ++ strbrk " but not conversely"
    else if Id.List.mem y xge then
      Id.print x ++ str " depends on " ++ Id.print y ++ strbrk " but not conversely"
    else
      Id.print y ++ str " and " ++ Id.print x ++ strbrk " are not mutually dependent" in
  let e = if List.is_empty rest then reason else strbrk "e.g., " ++ reason in
  let k = Decls.(match isfix with Fixpoint -> "defined fixpoint" | CoFixpoint -> "defined cofixpoint" | _ -> "dependent definition") in
  let w =
    if isfix <> Decls.CoFixpoint
    then strbrk "Well-foundedness check may fail unexpectedly." ++ fnl()
    else mt () in
  strbrk "Not a fully mutually " ++ str k ++ fnl () ++
  str "(" ++ e ++ str ")." ++ fnl () ++ w

let warn_non_full_mutual =
  CWarnings.create ~name:"non-full-mutual" ~category:CWarnings.CoreCategories.fixpoints
         (fun (x,xge,y,yge,isfix,rest) ->
          non_full_mutual_message x xge y yge isfix rest)

let warn_non_recursive =
  CWarnings.create ~name:"non-recursive" ~category:CWarnings.CoreCategories.fixpoints
         (fun (x,isfix) ->
          let k = Decls.(match isfix with Fixpoint -> "fixpoint" | CoFixpoint -> "cofixpoint" | _ -> "definition") in
          strbrk "Not a truly recursive " ++ str k ++ str ".")

let check_true_recursivity env evd ~isfix fixl =
  let names = List.map fst fixl in
  let preorder =
    List.map (fun (id,def) ->
      (id, List.filter (fun id' -> Termops.occur_var env evd id' def) names))
      fixl in
  let po = partial_order Id.equal preorder in
  match List.filter (function (_,Inr _) -> true | _ -> false) po with
    | (x,Inr xge)::(y,Inr yge)::rest ->
       warn_non_full_mutual (x,xge,y,yge,isfix,rest)
    | _ ->
  match po with
    | [x,Inr []] -> warn_non_recursive (x,isfix)
    | _ -> ()

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

let make_qref s = Libnames.qualid_of_string s
let lt_ref = make_qref "Init.Peano.lt"

(* Interpret the index of a recursion order annotation *)
let find_rec_annot ~program_mode ~function_mode Vernacexpr.{fname={CAst.loc}; binders} ctx = function
  | None ->
    if Int.equal (Context.Rel.nhyps ctx) 0 then CErrors.user_err ?loc Pp.(str "A fixpoint needs at least one parameter.");
    None, List.interval 0 (Context.Rel.nhyps ctx - 1)
  | Some CAst.{v=rec_order;loc} ->
    let default_order r = Option.default (CAst.make @@ CRef (lt_ref,None)) r in
    match rec_order with
    | CStructRec na -> None, [position_of_argument ctx binders na]
    | CMeasureRec _ | CWfRec _ when not (program_mode || function_mode) ->
      CErrors.user_err ?loc Pp.(str "Well-founded induction requires Program Fixpoint or Function.")
    | CWfRec (na,r) ->
      if program_mode then Some (r, Constrexpr_ops.mkIdentC na.CAst.v), [] (* useless: will use Fix_sub *)
      else if function_mode then None, []
      else assert false
    | CMeasureRec (na, mes, rfel) ->
      if program_mode then
        let r = match na, rfel with
          | Some id, None ->
            let loc = id.CAst.loc in
            CAst.make ?loc @@ CRef (Libnames.qualid_of_ident ?loc id.CAst.v,None)
          | Some _, Some _ -> CErrors.user_err ?loc Pp.(str"Measure takes only two arguments in Program Fixpoint.")
          | None, rfel -> default_order rfel in
        Some (r, mes), [] (* useless: will use Fix_sub *)
      else if function_mode then
        let _ = match binders, na with
          | [CLocalDef({ CAst.v = Name id },_,_,_) | CLocalAssum([{ CAst.v = Name id }],_,_,_)], None -> ()
          | _, None -> CErrors.user_err ?loc Pp.(str "Decreasing argument must be specified in measure clause.")
          | _, Some na -> (* check that the name exists *) ignore (position_of_argument ctx binders na) in
        (* Dummy *) None, []
      else
        assert false

let interp_rec_annot ~program_mode ~function_mode fixl ctxl rec_order =
  let open Pretyping in
  let fixkind, (possibly_cofix, fixwf_guard) =
    match rec_order with
    (* If recursive argument was not given by user, we try all args.
       An earlier approach was to look only for inductive arguments,
       but doing it properly involves delta-reduction, and it finally
       doesn't seem to worth the effort (except for huge mutual
       fixpoints ?) *)
    | CFixRecOrder fix_orders -> Decls.Fixpoint, (false, List.map3 (find_rec_annot ~program_mode ~function_mode) fixl ctxl fix_orders)
    | CCoFixRecOrder -> Decls.CoFixpoint, (true, List.map (fun _ -> (None, [])) fixl)
    | CUnknownRecOrder -> Decls.Definition, (true, List.map2 (fun fix ctx -> find_rec_annot ~program_mode ~function_mode fix ctx None) fixl ctxl) in
  let fixwf, possible_fix_indices = List.split fixwf_guard in
  (fixkind, fixwf, {possibly_cofix; possible_fix_indices})

let interp_fix_context ~program_mode env sigma {Vernacexpr.binders} =
  let sigma, (impl_env, ((env', ctx), imps)) = interp_context_evars ~program_mode env sigma binders in
  sigma, (env', ctx, impl_env, imps)

let interp_fix_ccl ~program_mode sigma impls env fix =
  let flags = Pretyping.{ all_no_fail_flags with program_mode } in
  let sigma, (c, impl) = interp_type_evars_impls ~flags ~impls env sigma fix.Vernacexpr.rtype in
  let r = Retyping.relevance_of_type env sigma c in
  sigma, (c, r, impl)

let interp_fix_body ~program_mode env_rec sigma impls ctx fix ccl =
  let open EConstr in
  Option.cata (fun body ->
    let env = push_rel_context ctx env_rec in
    let sigma, body = interp_casted_constr_evars ~program_mode env sigma ~impls body ccl in
    sigma, Some (it_mkLambda_or_LetIn body ctx)) (sigma, None) fix.Vernacexpr.body_def

let build_fix_type sigma ctx ccl =
  Evarutil.nf_evar sigma (EConstr.it_mkProd_or_LetIn ccl ctx)

(* Jump over let-bindings. *)

type ('constr, 'types, 'r) recursive_preentry =
  (Id.t list * 'r list * 'constr option list * 'types list * EConstr.rel_context list * Impargs.manual_implicits list) *
  Decls.definition_object_kind * Pretyping.possible_guard * UState.universe_decl

(* Wellfounded definition *)

let encapsulate env sigma r t =
  (* Would probably be overkill to use a specific fix_proto in SProp when in SProp?? *)
  let fix_proto sigma =
    Evd.fresh_global (Global.env ()) sigma (Coqlib.lib_ref "program.tactic.fix_proto") in
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
}

let recproofid = Id.of_string "recproof"

let imp_of_wf = function
  | None -> []
  | Some _ -> [CAst.make (Some (Name recproofid, true))]

let interp_recursive_evars env ~program_mode ~function_mode rec_order fixl =
  let open Context.Named.Declaration in
  let open EConstr in
  let fixnames = List.map (fun fix -> fix.Vernacexpr.fname.CAst.v) fixl in

  (* Interp arities allowing for unresolved types *)
  let sigma, decl = interp_mutual_univ_decl_opt env (List.map (fun Vernacexpr.{univs} -> univs) fixl) in
  let sigma, (fixenv, fixctxs, fixctximpenvs, fixctximps) =
    on_snd List.split4 @@
      List.fold_left_map (fun sigma -> interp_fix_context ~program_mode env sigma) sigma fixl in
  let fixkind, fixwfs, possible_guard = interp_rec_annot ~program_mode ~function_mode fixl fixctxs rec_order in
  let sigma, (fixccls,fixrs,fixcclimps) =
    on_snd List.split3 @@
      List.fold_left3_map (interp_fix_ccl ~program_mode) sigma fixctximpenvs fixenv fixl in
  let fixtypes = List.map2 (build_fix_type sigma) fixctxs fixccls in
  let fiximps = List.map3 (fun ctximps wf cclimps -> ctximps @ imp_of_wf wf @ cclimps) fixctximps fixwfs fixcclimps in
  let sigma, rec_sign =
    List.fold_left3
      (fun (sigma, env') id r t ->
         let sigma, r, t = if program_mode then encapsulate env sigma r t else sigma, r, t in
         sigma, LocalAssum (Context.make_annot id r, t) :: env')
      (sigma,[]) fixnames fixrs fixtypes
  in
  let env_rec = push_named_context rec_sign env in

  (* Get interpretation metadatas *)
  let impls = compute_internalization_env env sigma Recursive fixnames fixtypes fiximps in

  (* Interp bodies with rollback because temp use of notations/implicit *)
  let fixntns = List.map_append (fun { Vernacexpr.notations } -> List.map Metasyntax.prepare_where_notation notations ) fixl in
  let sigma, fixdefs =
    Metasyntax.with_syntax_protection (fun () ->
      List.iter (Metasyntax.set_notation_for_interpretation env_rec impls) fixntns;
      List.fold_left4_map
        (fun sigma fixctximpenv -> interp_fix_body ~program_mode env_rec sigma (Id.Map.fold Id.Map.add fixctximpenv impls))
        sigma fixctximpenvs fixctxs fixl fixccls)
      () in

  (* Instantiate evars and check all are resolved *)
  let sigma = Evarconv.solve_unif_constraints_with_heuristics env_rec sigma in
  let sigma = Evd.minimize_universes sigma in

  (* Build the fix declaration block *)
  let fix = {fixnames;fixrs;fixdefs;fixtypes;fixctxs;fiximps;fixntns} in
  (env, rec_sign, sigma), (fix, fixkind, possible_guard, decl)

let check_recursive ~isfix env evd {fixnames;fixdefs} =
  if List.for_all Option.has_some fixdefs then begin
    let fixdefs = List.map Option.get fixdefs in
    check_true_recursivity env evd ~isfix (List.combine fixnames fixdefs)
  end

let ground_fixpoint env evd {fixnames;fixrs;fixdefs;fixtypes;fixctxs;fiximps;fixntns} =
  Pretyping.check_evars_are_solved ~program_mode:false env evd;
  let fixrs = List.map (fun r -> EConstr.ERelevance.kind evd r) fixrs in
  let fixdefs = List.map (fun c -> Option.map EConstr.(to_constr evd) c) fixdefs in
  let fixtypes = List.map EConstr.(to_constr evd) fixtypes in
  {fixnames;fixrs;fixdefs;fixtypes;fixctxs;fiximps;fixntns}

(** For Funind *)

let interp_fixpoint_short rec_order fixpoint_exprl =
  let env = Global.env () in
  let (_, _, sigma),(fix, _, _, _) = interp_recursive_evars ~program_mode:false ~function_mode:true env (CFixRecOrder rec_order) fixpoint_exprl in
  let sigma = Pretyping.(solve_remaining_evars all_no_fail_flags env sigma) in
  let typel = (ground_fixpoint env sigma fix).fixtypes in
  let uctx = Evd.evar_universe_context sigma in
  typel, uctx

let build_recthms {fixnames;fixtypes;fixctxs;fiximps} =
  List.map4 (fun name typ ctx impargs ->
      let args = List.map Context.Rel.Declaration.get_name ctx in
      Declare.CInfo.make ~name ~typ ~args ~impargs ()
    ) fixnames fixtypes fixctxs fiximps

let collect_evars_of_term evd c ty =
  Evar.Set.union (Evd.evars_of_term evd c) (Evd.evars_of_term evd ty)

let out_def = function
  | Some def -> def
  | None -> CErrors.user_err Pp.(str "Program Fixpoint needs defined bodies.")

let collect_evars env sigma rec_sign name def typ =
  (* Generalize by the recursive prototypes  *)
  let deps = collect_evars_of_term sigma def typ in
  let evars, _, def, typ =
    RetrieveObl.retrieve_obligations env name sigma
      (List.length rec_sign) ~deps def typ in
  (Some def, typ, evars)

let finish_program env sigma rec_sign possible_guard {fixnames;fixrs;fixdefs;fixtypes;fixctxs;fiximps;fixntns} =
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
  let fixdefs, fixtypes, obls = List.split3 (List.map3 (collect_evars env sigma rec_sign) fixnames fixdefs fixtypes) in
  let fixrs = List.map (EConstr.ERelevance.kind sigma) fixrs in
  sigma, {fixnames;fixrs;fixdefs;fixtypes;fixctxs;fiximps;fixntns}, obls

let finish_regular env sigma fix =
  let sigma = Pretyping.(solve_remaining_evars all_no_fail_flags env sigma) in
  sigma, ground_fixpoint env sigma fix, []

let do_mutually_recursive ?pm ?scope ?clearbody ~poly ?typing_flags ?user_warns ?using (rec_order, fixl)
  : Declare.OblState.t option * Declare.Proof.t option =
  let env = Global.env () in
  let env = Environ.update_typing_flags ?typing_flags env in
  let (env,rec_sign,sigma),(fix,isfix,possible_guard,udecl) = interp_recursive_evars env ~program_mode:(Option.has_some pm) ~function_mode:false rec_order fixl in
  check_recursive ~isfix env sigma fix;
  let kind = Decls.IsDefinition isfix in
  let sigma, ({fixdefs=bodies;fixrs} as fix), obls =
    match pm with
    | Some pm -> finish_program env sigma rec_sign possible_guard fix
    | None -> finish_regular env sigma fix in
  let uctx = Evd.evar_universe_context sigma in
  let info = Declare.Info.make ?scope ?clearbody ~kind ~poly ~udecl ?typing_flags ?user_warns ~ntns:fix.fixntns () in
  let cinfo = build_recthms fix in
  match pm with
  | Some pm ->
    let bodies = List.map Option.get bodies in
    Some (Declare.Obls.add_mutual_definitions ~pm ~cinfo ~info ~opaque:false ~uctx ~bodies ~possible_guard ?using obls), None
  | None ->
    try
      let bodies = List.map Option.get bodies in
      (* All bodies are defined *)
      let _ : GlobRef.t list =
        Declare.declare_mutual_definitions ~cinfo ~info ~opaque:false ~uctx
          ~possible_guard ~bodies:(bodies,fixrs) ?using ()
      in
      None, None
    with Option.IsNone ->
      (* At least one undefined body *)
      let evd = Evd.from_ctx uctx in
      let lemma = Declare.Proof.start_mutual_definitions ~info ~cinfo
          ~bodies ~possible_guard ?using evd in
      None, Some lemma
