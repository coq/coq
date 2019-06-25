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
open Termops
open Declare
open Names
open Constrexpr
open Constrexpr_ops
open Constrintern
open Decl_kinds
open Pretyping
open Evarutil
open Evarconv

module RelDecl = Context.Rel.Declaration

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
            browse ((y,Inl x)::res) xge' (List.union cmp xge (List.remove cmp x yge))
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

let check_mutuality env evd isfix fixl =
  let names = List.map fst fixl in
  let preorder =
    List.map (fun (id,def) ->
      (id, List.filter (fun id' -> not (Id.equal id id') && occur_var env evd id' def) names))
      fixl in
  let po = partial_order Id.equal preorder in
  match List.filter (function (_,Inr _) -> true | _ -> false) po with
    | (x,Inr xge)::(y,Inr yge)::rest ->
       warn_non_full_mutual (x,xge,y,yge,isfix,rest)
    | _ -> ()

type structured_fixpoint_expr = {
  fix_name : Id.t;
  fix_univs : universe_decl_expr option;
  fix_annot : lident option;
  fix_binders : local_binder_expr list;
  fix_body : constr_expr option;
  fix_type : constr_expr
}

let interp_fix_context ~program_mode ~cofix env sigma fix =
  let before, after = if not cofix then split_at_annot fix.fix_binders fix.fix_annot else [], fix.fix_binders in
  let sigma, (impl_env, ((env', ctx), imps)) = interp_context_evars ~program_mode env sigma before in
  let sigma, (impl_env', ((env'', ctx'), imps')) =
    interp_context_evars ~program_mode ~impl_env ~shift:(Context.Rel.nhyps ctx) env' sigma after
  in
  let annot = Option.map (fun _ -> List.length (assums_of_rel_context ctx)) fix.fix_annot in
  sigma, ((env'', ctx' @ ctx), (impl_env',imps @ imps'), annot)

let interp_fix_ccl ~program_mode sigma impls (env,_) fix =
  let sigma, (c, impl) = interp_type_evars_impls ~program_mode ~impls env sigma fix.fix_type in
  let r = Retyping.relevance_of_type env sigma c in
  sigma, (c, r, impl)

let interp_fix_body ~program_mode env_rec sigma impls (_,ctx) fix ccl =
  let open EConstr in
  Option.cata (fun body ->
    let env = push_rel_context ctx env_rec in
    let sigma, body = interp_casted_constr_evars ~program_mode env sigma ~impls body ccl in
    sigma, Some (it_mkLambda_or_LetIn body ctx)) (sigma, None) fix.fix_body

let build_fix_type (_,ctx) ccl = EConstr.it_mkProd_or_LetIn ccl ctx

let prepare_recursive_declaration fixnames fixrs fixtypes fixdefs =
  let defs = List.map (subst_vars (List.rev fixnames)) fixdefs in
  let names = List.map2 (fun id r -> make_annot (Name id) r) fixnames fixrs in
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

type recursive_preentry =
  Id.t list * Sorts.relevance list * constr option list * types list

(* Wellfounded definition *)

let fix_proto sigma =
  Evarutil.new_global sigma (Coqlib.lib_ref "program.tactic.fix_proto")

let interp_recursive ~program_mode ~cofix fixl notations =
  let open Context.Named.Declaration in
  let open EConstr in
  let env = Global.env() in
  let fixnames = List.map (fun fix -> fix.fix_name) fixl in

  (* Interp arities allowing for unresolved types *)
  let all_universes =
    List.fold_right (fun sfe acc ->
        match sfe.fix_univs , acc with
        | None , acc -> acc
        | x , None -> x
        | Some ls , Some us ->
          let open UState in
          let lsu = ls.univdecl_instance and usu = us.univdecl_instance in
           if not (CList.for_all2eq (fun x y -> Id.equal x.CAst.v y.CAst.v) lsu usu) then
             user_err Pp.(str "(co)-recursive definitions should all have the same universe binders");
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
  let fixtypes = List.map (fun c -> nf_evar sigma c) fixtypes in
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
           sigma, LocalAssum (make_annot id Sorts.Relevant,fixprot) :: env'
         else sigma, LocalAssum (make_annot id Sorts.Relevant,t) :: env')
      (sigma,[]) fixnames fixtypes
  in
  let env_rec = push_named_context rec_sign env in

  (* Get interpretation metadatas *)
  let impls = compute_internalization_env env sigma Recursive fixnames fixtypes fiximps in

  (* Interp bodies with rollback because temp use of notations/implicit *)
  let sigma, fixdefs =
    Metasyntax.with_syntax_protection (fun () ->
      List.iter (Metasyntax.set_notation_for_interpretation env_rec impls) notations;
      List.fold_left4_map
        (fun sigma fixctximpenv -> interp_fix_body ~program_mode env_rec sigma (Id.Map.fold Id.Map.add fixctximpenv impls))
        sigma fixctximpenvs fixctxs fixl fixccls)
      () in

  (* Instantiate evars and check all are resolved *)
  let sigma = solve_unif_constraints_with_heuristics env_rec sigma in
  let sigma = Evd.minimize_universes sigma in
  let fixctxs = List.map (fun (_,ctx) -> ctx) fixctxs in

  (* Build the fix declaration block *)
  (env,rec_sign,decl,sigma), (fixnames,fixrs,fixdefs,fixtypes), List.combine3 fixctxs fiximps fixannots

let check_recursive isfix env evd (fixnames,_,fixdefs,_) =
  if List.for_all Option.has_some fixdefs then begin
    let fixdefs = List.map Option.get fixdefs in
    check_mutuality env evd isfix (List.combine fixnames fixdefs)
  end

let ground_fixpoint env evd (fixnames,fixrs,fixdefs,fixtypes) =
  check_evars_are_solved ~program_mode:false env evd;
  let fixdefs = List.map (fun c -> Option.map EConstr.(to_constr evd) c) fixdefs in
  let fixtypes = List.map EConstr.(to_constr evd) fixtypes in
  Evd.evar_universe_context evd, (fixnames,fixrs,fixdefs,fixtypes)

let interp_fixpoint ~cofix l ntns =
  let (env,_,pl,evd),fix,info = interp_recursive ~program_mode:false ~cofix l ntns in
  check_recursive true env evd fix;
  let uctx,fix = ground_fixpoint env evd fix in
  (fix,pl,uctx,info)

let declare_fixpoint_interactive_generic ?indexes ~scope ~poly ((fixnames,_fixrs,fixdefs,fixtypes),udecl,ctx,fiximps) ntns =
  let fix_kind, cofix, indexes = match indexes with
    | Some indexes -> Fixpoint, false, indexes
    | None -> CoFixpoint, true, []
  in
  let thms =
    List.map3 (fun name t (ctx,impargs,_) ->
        { Lemmas.Recthm.name; typ = EConstr.of_constr t
        ; args = List.map RelDecl.get_name ctx; impargs})
      fixnames fixtypes fiximps in
  let init_tac =
    Some (List.map (Option.cata (EConstr.of_constr %> Tactics.exact_no_check) Tacticals.New.tclIDTAC) fixdefs) in
  let evd = Evd.from_ctx ctx in
  let lemma =
    Lemmas.start_lemma_with_initialization ~poly ~scope ~kind:(DefinitionBody fix_kind) ~udecl
      evd (Some(cofix,indexes,init_tac)) thms None in
  (* Declare notations *)
  List.iter (Metasyntax.add_notation_interpretation (Global.env())) ntns;
  lemma

let declare_fixpoint_generic ?indexes ~scope ~poly ((fixnames,fixrs,fixdefs,fixtypes),pl,ctx,fiximps) ntns =
  let indexes, cofix, fix_kind =
    match indexes with
    | Some indexes -> indexes, false, Fixpoint
    | None -> [], true, CoFixpoint
  in
  (* We shortcut the proof process *)
  let fixdefs = List.map Option.get fixdefs in
  let fixdecls = prepare_recursive_declaration fixnames fixrs fixtypes fixdefs in
  let vars, fixdecls, gidx =
    if not cofix then
      let env = Global.env() in
      let indexes = search_guard env indexes fixdecls in
      let vars = Vars.universes_of_constr (mkFix ((indexes,0),fixdecls)) in
      let fixdecls = List.map_i (fun i _ -> mkFix ((indexes,i),fixdecls)) 0 fixnames in
      vars, fixdecls, Some indexes
    else (* cofix *)
      let fixdecls = List.map_i (fun i _ -> mkCoFix (i,fixdecls)) 0 fixnames in
      let vars = Vars.universes_of_constr (List.hd fixdecls) in
      vars, fixdecls, None
  in
  let fiximps = List.map (fun (n,r,p) -> r) fiximps in
  let evd = Evd.from_ctx ctx in
  let evd = Evd.restrict_universe_context evd vars in
  let ctx = Evd.check_univ_decl ~poly evd pl in
  let pl = Evd.universe_binders evd in
  let mk_pure c = (c, Univ.ContextSet.empty), Evd.empty_side_effects in
  let fixdecls = List.map mk_pure fixdecls in
  ignore (List.map4 (fun name -> DeclareDef.declare_fix ~name ~scope ~kind:fix_kind pl ctx)
            fixnames fixdecls fixtypes fiximps);
  recursive_message (not cofix) gidx fixnames;
  List.iter (Metasyntax.add_notation_interpretation (Global.env())) ntns;
  ()

let extract_decreasing_argument ~structonly = function { CAst.v = v } -> match v with
  | CStructRec na -> na
  | (CWfRec (na,_) | CMeasureRec (Some na,_,_)) when not structonly -> na
  | CMeasureRec (None,_,_) when not structonly ->
    user_err Pp.(str "Decreasing argument must be specified in measure clause.")
  | _ -> user_err Pp.(str
           "Well-founded induction requires Program Fixpoint or Function.")

let extract_fixpoint_components ~structonly l =
  let fixl, ntnl = List.split l in
  let fixl = List.map (fun (({CAst.v=id},pl),ann,bl,typ,def) ->
      (* This is a special case: if there's only one binder, we pick it as the
      recursive argument if none is provided. *)
      let ann = Option.map (fun ann -> match bl, ann with
        | [CLocalAssum([{ CAst.v = Name x }],_,_)], { CAst.v = CMeasureRec(None, mes, rel); CAst.loc } ->
          CAst.make ?loc @@ CMeasureRec(Some (CAst.make x), mes, rel)
        | [CLocalDef({ CAst.v = Name x },_,_)], { CAst.v = CMeasureRec(None, mes, rel); CAst.loc } ->
          CAst.make ?loc @@ CMeasureRec(Some (CAst.make x), mes, rel)
        | _, x -> x) ann
      in
      let ann = Option.map (extract_decreasing_argument ~structonly) ann in
      {fix_name = id; fix_annot = ann; fix_univs = pl;
       fix_binders = bl; fix_body = def; fix_type = typ}) fixl in
  fixl, List.flatten ntnl

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

let do_fixpoint_common l =
  let fixl, ntns = extract_fixpoint_components ~structonly:true l in
  let (_, _, _, info as fix) = interp_fixpoint ~cofix:false fixl ntns in
  fixl, ntns, fix, List.map compute_possible_guardness_evidences info

let do_fixpoint_interactive ~scope ~poly l : Lemmas.t =
  let fixl, ntns, fix, possible_indexes = do_fixpoint_common l in
  let lemma = declare_fixpoint_interactive_generic ~indexes:possible_indexes ~scope ~poly fix ntns in
  if not (check_safe ()) then Feedback.feedback Feedback.AddedAxiom else ();
  lemma

let do_fixpoint ~scope ~poly l =
  let fixl, ntns, fix, possible_indexes = do_fixpoint_common l in
  declare_fixpoint_generic ~indexes:possible_indexes ~scope ~poly fix ntns;
  if not (check_safe ()) then Feedback.feedback Feedback.AddedAxiom else ()

let do_cofixpoint_common l =
  let fixl,ntns = extract_cofixpoint_components l in
  ntns, interp_fixpoint ~cofix:true fixl ntns

let do_cofixpoint_interactive ~scope ~poly l =
  let ntns, cofix = do_cofixpoint_common l in
  let lemma = declare_fixpoint_interactive_generic ~scope ~poly cofix ntns in
  if not (check_safe ()) then Feedback.feedback Feedback.AddedAxiom else ();
  lemma

let do_cofixpoint ~scope ~poly l =
  let ntns, cofix = do_cofixpoint_common l in
  declare_fixpoint_generic ~scope ~poly cofix ntns;
  if not (check_safe ()) then Feedback.feedback Feedback.AddedAxiom else ()
