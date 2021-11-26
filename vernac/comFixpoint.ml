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
open Constrintern

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
  let k = if isfix then "fixpoint" else "cofixpoint" in
  let w =
    if isfix
    then strbrk "Well-foundedness check may fail unexpectedly." ++ fnl()
    else mt () in
  strbrk "Not a fully mutually defined " ++ str k ++ fnl () ++
  str "(" ++ e ++ str ")." ++ fnl () ++ w

let warn_non_full_mutual =
  CWarnings.create ~name:"non-full-mutual" ~category:"fixpoints"
         (fun (x,xge,y,yge,isfix,rest) ->
          non_full_mutual_message x xge y yge isfix rest)

let warn_non_recursive =
  CWarnings.create ~name:"non-recursive" ~category:"fixpoints"
         (fun (x,isfix) ->
          let k = if isfix then "fixpoint" else "cofixpoint" in
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

let interp_fix_context ~program_mode ~cofix env sigma fix =
  let before, after =
    if not cofix
    then Constrexpr_ops.split_at_annot fix.Vernacexpr.binders fix.Vernacexpr.rec_order
    else [], fix.Vernacexpr.binders in
  let sigma, (impl_env, ((env', ctx), imps)) = interp_context_evars ~program_mode env sigma before in
  let sigma, (impl_env', ((env'', ctx'), imps')) =
    interp_context_evars ~program_mode ~impl_env env' sigma after
  in
  let annot = Option.map (fun _ -> List.length (Termops.assums_of_rel_context ctx)) fix.Vernacexpr.rec_order in
  sigma, ((env'', ctx' @ ctx), (impl_env',imps @ imps'), annot)

let interp_fix_ccl ~program_mode sigma impls (env,_) fix =
  let flags = Pretyping.{ all_no_fail_flags with program_mode } in
  let sigma, (c, impl) = interp_type_evars_impls ~flags ~impls env sigma fix.Vernacexpr.rtype in
  let r = Retyping.relevance_of_type env sigma c in
  sigma, (c, r, impl)

let interp_fix_body ~program_mode env_rec sigma impls (_,ctx) fix ccl =
  let open EConstr in
  Option.cata (fun body ->
    let env = push_rel_context ctx env_rec in
    let sigma, body = interp_casted_constr_evars ~program_mode env sigma ~impls body ccl in
    sigma, Some (it_mkLambda_or_LetIn body ctx)) (sigma, None) fix.Vernacexpr.body_def

let build_fix_type (_,ctx) ccl = EConstr.it_mkProd_or_LetIn ccl ctx

let prepare_recursive_declaration fixnames fixrs fixtypes fixdefs =
  let defs = List.map (Vars.subst_vars (List.rev fixnames)) fixdefs in
  let names = List.map2 (fun id r -> Context.make_annot (Name id) r) fixnames fixrs in
  (Array.of_list names, Array.of_list fixtypes, Array.of_list defs)

(* Jump over let-bindings. *)

let compute_possible_guardness_evidences (ctx,_,recindex) =
  (* A recursive index is characterized by the number of lambdas to
     skip before finding the relevant inductive argument *)
  match recindex with
  | Some i -> [i]
  | None ->
      (* If recursive argument was not given by user, we try all args.
         An earlier approach was to look only for inductive arguments,
         but doing it properly involves delta-reduction, and it finally
         doesn't seem to worth the effort (except for huge mutual
         fixpoints ?) *)
      List.interval 0 (Context.Rel.nhyps ctx - 1)

type ('constr, 'types) recursive_preentry =
  Id.t list * Sorts.relevance list * 'constr option list * 'types list

(* Wellfounded definition *)

let fix_proto sigma =
  Evd.fresh_global (Global.env ()) sigma (Coqlib.lib_ref "program.tactic.fix_proto")

let interp_recursive env ~program_mode ~cofix (fixl : 'a Vernacexpr.fix_expr_gen list) =
  let open Context.Named.Declaration in
  let open EConstr in
  let fixnames = List.map (fun fix -> fix.Vernacexpr.fname.CAst.v) fixl in

  (* Interp arities allowing for unresolved types *)
  let all_universes =
    List.fold_right (fun sfe acc ->
        match sfe.Vernacexpr.univs , acc with
        | None , acc -> acc
        | x , None -> x
        | Some ls , Some us ->
          let open UState in
          let lsu = ls.univdecl_instance and usu = us.univdecl_instance in
           if not (CList.for_all2eq (fun x y -> Id.equal x.CAst.v y.CAst.v) lsu usu) then
             CErrors.user_err Pp.(str "(co)-recursive definitions should all have the same universe binders");
           Some us) fixl None in
  let sigma, decl = interp_univ_decl_opt env all_universes in
  let sigma, (fixctxs, fiximppairs, fixannots) =
    on_snd List.split3 @@
      List.fold_left_map (fun sigma -> interp_fix_context ~program_mode env sigma ~cofix) sigma fixl in
  let fixctximpenvs, fixctximps = List.split fiximppairs in
  let sigma, (fixccls,fixrs,fixcclimps) =
    on_snd List.split3 @@
      List.fold_left3_map (interp_fix_ccl ~program_mode) sigma fixctximpenvs fixctxs fixl in
  let fixtypes = List.map2 build_fix_type fixctxs fixccls in
  let fixtypes = List.map (fun c -> Evarutil.nf_evar sigma c) fixtypes in
  let fiximps = List.map3
    (fun ctximps cclimps (_,ctx) -> ctximps@cclimps)
    fixctximps fixcclimps fixctxs in
  let sigma, rec_sign =
    List.fold_left2
      (fun (sigma, env') id t ->
         if program_mode then
           let sigma, sort = Typing.type_of ~refresh:true env sigma t in
           let sigma, fixprot =
             try
               let sigma, h_term = fix_proto sigma in
               let app = mkApp (h_term, [|sort; t|]) in
               Typing.solve_evars env sigma app
             with e when CErrors.noncritical e -> sigma, t
           in
           sigma, LocalAssum (Context.make_annot id Sorts.Relevant,fixprot) :: env'
         else sigma, LocalAssum (Context.make_annot id Sorts.Relevant,t) :: env')
      (sigma,[]) fixnames fixtypes
  in
  let env_rec = push_named_context rec_sign env in

  (* Get interpretation metadatas *)
  let impls = compute_internalization_env env sigma Recursive fixnames fixtypes fiximps in

  (* Interp bodies with rollback because temp use of notations/implicit *)
  let sigma, fixdefs =
    Metasyntax.with_syntax_protection (fun () ->
      let notations = List.map_append (fun { Vernacexpr.notations } -> List.map Metasyntax.prepare_where_notation notations) fixl in
      List.iter (Metasyntax.set_notation_for_interpretation env_rec impls) notations;
      List.fold_left4_map
        (fun sigma fixctximpenv -> interp_fix_body ~program_mode env_rec sigma (Id.Map.fold Id.Map.add fixctximpenv impls))
        sigma fixctximpenvs fixctxs fixl fixccls)
      () in

  (* Instantiate evars and check all are resolved *)
  let sigma = Evarconv.solve_unif_constraints_with_heuristics env_rec sigma in
  let sigma = Evd.minimize_universes sigma in
  let fixctxs = List.map (fun (_,ctx) -> ctx) fixctxs in

  (* Build the fix declaration block *)
  (env,rec_sign,decl,sigma), (fixnames,fixrs,fixdefs,fixtypes), List.combine3 fixctxs fiximps fixannots

let check_recursive ~isfix env evd (fixnames,_,fixdefs,_) =
  if List.for_all Option.has_some fixdefs then begin
    let fixdefs = List.map Option.get fixdefs in
    check_true_recursivity env evd ~isfix (List.combine fixnames fixdefs)
  end

let ground_fixpoint env evd (fixnames,fixrs,fixdefs,fixtypes) =
  Pretyping.check_evars_are_solved ~program_mode:false env evd;
  let fixdefs = List.map (fun c -> Option.map EConstr.(to_constr evd) c) fixdefs in
  let fixtypes = List.map EConstr.(to_constr evd) fixtypes in
  Evd.evar_universe_context evd, (fixnames,fixrs,fixdefs,fixtypes)

(* XXX: Unify with interp_recursive  *)
let interp_fixpoint ?(check_recursivity=true) ?typing_flags ~cofix l :
  ( (Constr.t, Constr.types) recursive_preentry *
    UState.universe_decl * UState.t *
    (EConstr.rel_context * Impargs.manual_implicits * int option) list) =
  let env = Global.env () in
  let env = Environ.update_typing_flags ?typing_flags env in
  let (env,_,pl,evd),fix,info = interp_recursive env ~program_mode:false ~cofix l in
  if check_recursivity then check_recursive ~isfix:(not cofix) env evd fix;
  let evd = Pretyping.(solve_remaining_evars all_no_fail_flags env evd) in
  let uctx,fix = ground_fixpoint env evd fix in
  (fix,pl,uctx,info)

let build_recthms ~indexes ?using fixnames fixtypes fiximps =
  let fix_kind, cofix = match indexes with
    | Some indexes -> Decls.Fixpoint, false
    | None -> Decls.CoFixpoint, true
  in
  let thms =
    List.map3 (fun name typ (ctx,impargs,_) ->
        let env = Global.env() in
        let evd = Evd.from_env env in
        let terms = [EConstr.of_constr typ] in
        let using = Option.map (fun using -> Proof_using.definition_using env evd ~using ~terms) using in
        let args = List.map Context.Rel.Declaration.get_name ctx in
        Declare.CInfo.make ~name ~typ ~args ~impargs ?using ()
      ) fixnames fixtypes fiximps
  in
  fix_kind, cofix, thms

let declare_fixpoint_interactive_generic ?indexes ~scope ~poly ?typing_flags ((fixnames,_fixrs,fixdefs,fixtypes),udecl,ctx,fiximps) ntns =
  let fix_kind, cofix, thms = build_recthms ~indexes fixnames fixtypes fiximps in
  let indexes = Option.default [] indexes in
  let init_terms = Some fixdefs in
  let evd = Evd.from_ctx ctx in
  let info = Declare.Info.make ~poly ~scope ~kind:(Decls.IsDefinition fix_kind) ~udecl ?typing_flags () in
  let lemma =
    Declare.Proof.start_mutual_with_initialization ~info
      evd ~mutual_info:(cofix,indexes,init_terms) ~cinfo:thms None in
  (* Declare notations *)
  List.iter (Metasyntax.add_notation_interpretation ~local:(scope=Locality.Discharge) (Global.env())) ntns;
  lemma

let declare_fixpoint_generic ?indexes ?scope ~poly ?typing_flags ?using ((fixnames,fixrs,fixdefs,fixtypes),udecl,uctx,fiximps) ntns =
  (* We shortcut the proof process *)
  let fix_kind, cofix, fixitems = build_recthms ~indexes ?using fixnames fixtypes fiximps in
  let fixdefs = List.map Option.get fixdefs in
  let rec_declaration = prepare_recursive_declaration fixnames fixrs fixtypes fixdefs in
  let fix_kind = Decls.IsDefinition fix_kind in
  let info = Declare.Info.make ?scope ~kind:fix_kind ~poly ~udecl ?typing_flags () in
  let cinfo = fixitems in
  let _ : GlobRef.t list =
    Declare.declare_mutually_recursive ~cinfo ~info ~opaque:false ~uctx
      ~possible_indexes:indexes ~ntns ~rec_declaration
  in
  ()

let extract_decreasing_argument ~structonly { CAst.v = v; _ } =
  let open Constrexpr in
  match v with
  | CStructRec na -> na
  | (CWfRec (na,_) | CMeasureRec (Some na,_,_)) when not structonly -> na
  | CMeasureRec (None,_,_) when not structonly ->
    CErrors.user_err Pp.(str "Decreasing argument must be specified in measure clause.")
  | _ ->
    CErrors.user_err Pp.(str "Well-founded induction requires Program Fixpoint or Function.")

(* This is a special case: if there's only one binder, we pick it as
   the recursive argument if none is provided. *)
let adjust_rec_order ~structonly binders rec_order =
  let rec_order = Option.map (fun rec_order ->
      let open Constrexpr in
      match binders, rec_order with
      | [CLocalAssum([{ CAst.v = Name x }],_,_)], { CAst.v = CMeasureRec(None, mes, rel); CAst.loc } ->
        CAst.make ?loc @@ CMeasureRec(Some (CAst.make x), mes, rel)
      | [CLocalDef({ CAst.v = Name x },_,_)], { CAst.v = CMeasureRec(None, mes, rel); CAst.loc } ->
        CAst.make ?loc @@ CMeasureRec(Some (CAst.make x), mes, rel)
      | _, x -> x) rec_order
  in
  Option.map (extract_decreasing_argument ~structonly) rec_order

let do_fixpoint_common ?typing_flags (fixl : Vernacexpr.fixpoint_expr list) =
  let fixl = List.map (fun fix ->
      Vernacexpr.{ fix
                   with rec_order = adjust_rec_order ~structonly:true fix.binders fix.rec_order }) fixl in
  let ntns = List.map_append (fun { Vernacexpr.notations } -> List.map Metasyntax.prepare_where_notation notations ) fixl in
  let (_, _, _, info as fix) = interp_fixpoint ~cofix:false ?typing_flags fixl in
  fixl, ntns, fix, List.map compute_possible_guardness_evidences info

let do_fixpoint_interactive ~scope ~poly ?typing_flags l : Declare.Proof.t =
  let fixl, ntns, fix, possible_indexes = do_fixpoint_common ?typing_flags l in
  let lemma = declare_fixpoint_interactive_generic ~indexes:possible_indexes ~scope ~poly ?typing_flags fix ntns in
  lemma

let do_fixpoint ?scope ~poly ?typing_flags ?using l =
  let fixl, ntns, fix, possible_indexes = do_fixpoint_common ?typing_flags l in
  declare_fixpoint_generic ~indexes:possible_indexes ?scope ~poly ?typing_flags ?using fix ntns

let do_cofixpoint_common (fixl : Vernacexpr.cofixpoint_expr list) =
  let fixl = List.map (fun fix -> {fix with Vernacexpr.rec_order = None}) fixl in
  let ntns = List.map_append (fun { Vernacexpr.notations } -> List.map Metasyntax.prepare_where_notation notations ) fixl in
  interp_fixpoint ~cofix:true fixl, ntns

let do_cofixpoint_interactive ~scope ~poly l =
  let cofix, ntns = do_cofixpoint_common l in
  let lemma = declare_fixpoint_interactive_generic ~scope ~poly cofix ntns in
  lemma

let do_cofixpoint ~scope ~poly ?using l =
  let cofix, ntns = do_cofixpoint_common l in
  declare_fixpoint_generic ~scope ~poly ?using cofix ntns
