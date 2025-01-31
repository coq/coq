(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Declarations
open Environ
open Names
open Univ
open UVars
open Util

[@@@ocaml.warning "+9+27"]

exception InductiveMismatch of MutInd.t * string

let check mind field b = if not b then raise (InductiveMismatch (mind,field))

let anon_univ_names u =
  let nqs, nus = UVars.Instance.length u in
  Array.make nqs Anonymous, Array.make nus Anonymous

let template_univ_entry {template_context; template_pseudo_sort_poly; template_param_arguments=_} =
  let template_univs, template_csts = template_context in
  let bind_qvars, default_qvars = match template_pseudo_sort_poly with
    | TemplateUnivOnly -> [||], [||]
    | TemplatePseudoSortPoly ->
      [|Sorts.Quality.QVar (Sorts.QVar.make_var 0)|], [|Sorts.Quality.qtype|]
  in
  let default_univs = Array.of_list @@ Level.Set.elements template_univs in
  let bind_univs = Array.init (Array.length default_univs) Level.var in
  let usubst = Array.fold_left2 (fun acc bind_u default_u ->
      Level.Map.add default_u bind_u acc)
      Level.Map.empty
      bind_univs default_univs
  in

  let csts = Constraints.fold (fun (u,d,v) acc ->
      let u = Univ.subst_univs_level_level usubst u in
      let () = assert (not @@ Level.Map.mem v usubst) in
      Constraints.add (u,d,v) acc)
      template_csts
      Constraints.empty
  in
  let inst = Instance.of_array (bind_qvars,bind_univs) in
  let uctx = UContext.make (anon_univ_names inst) (inst,csts) in

  let default_univs = UVars.Instance.of_array (default_qvars,default_univs) in

  template_pseudo_sort_poly, usubst, Entries.Template_ind_entry {uctx; default_univs}

let to_entry mind (mb:mutual_inductive_body) : Entries.mutual_inductive_entry =
  let open Entries in
  let nparams = List.length mb.mind_params_ctxt in (* include letins *)
  let mind_entry_record = match mb.mind_record with
    | NotRecord -> None | FakeRecord -> Some None
    | PrimRecord data -> Some (Some (Array.map (fun (x,_,_,_) -> x) data))
  in
  let template = Option.map template_univ_entry mb.mind_template in
  let mind_entry_universes = match mb.mind_universes with
    | Monomorphic ->
      (* We only need to rebuild the set of constraints for template polymorphic
        inductive types. The set of monomorphic constraints is already part of
        the graph at that point, but we need to emulate a broken bound variable
        mechanism for template inductive types. *)
      begin match template with
      | None -> Monomorphic_ind_entry
      | Some (_,_,template) -> template
      end
    | Polymorphic auctx -> Polymorphic_ind_entry (AbstractContext.repr auctx)
  in
  let ntyps = Array.length mb.mind_packets in
  let concl_template_univs = match mb.mind_packets, template with
    | _, None -> Level.Set.empty
    | [|_|], Some (TemplateUnivOnly,_,_) -> Level.Set.empty
    | [|ind|], Some (TemplatePseudoSortPoly,_,_) ->
      begin match ind.mind_arity with
      | RegularArity _ -> assert false
      | TemplateArity ar -> match ar.template_level with
        | SProp | Prop | Set -> Level.Set.empty
        | QSort _ -> assert false
        | Type u -> Universe.levels u
      end
    | _, Some _ -> assert false
  in
  let mind_entry_params = match template with
    | None -> mb.mind_params_ctxt
    | Some (_,usubst,_) ->
      let open Context.Rel.Declaration in
      mb.mind_params_ctxt |> List.map (function
          | LocalDef _ as d -> d
          | LocalAssum (na,t) as d ->
            let ctx, c = Term.decompose_prod_decls t in
            match Constr.kind c with
            | Sort (Type u) -> begin match Universe.level u with
                | Some u -> begin match Level.Map.find_opt u usubst with
                    | Some u' ->
                      let u' = Universe.make u' in
                      let s = if Level.Set.mem u concl_template_univs then
                          Sorts.qsort (Sorts.QVar.make_var 0) u'
                        else Sorts.sort_of_univ u'
                      in
                      LocalAssum (na,Term.mkArity (ctx, s))
                    | None -> d
                  end
                | None -> d
              end
            | _ -> d)
  in
  let mind_entry_inds = Array.map_to_list (fun ind ->
      let mind_entry_arity =
        match ind.mind_arity, template with
        | RegularArity ar, None ->
          let ctx, arity = Term.decompose_prod_n_decls nparams ar.mind_user_arity in
          ignore ctx; (* we will check that the produced user_arity is equal to the input *)
          arity
        | TemplateArity ar, Some (pseudo_sort_poly,usubst,_) ->
          let ctx = ind.mind_arity_ctxt in
          let ctx = List.firstn (List.length ctx - nparams) ctx in
          let concl = match ar.template_level with
            | SProp | Prop | Set as concl -> concl
            | QSort _ -> assert false
            | Type u ->
              let u' = Univ.subst_univs_level_universe usubst u in
              match pseudo_sort_poly with
              | TemplateUnivOnly -> Sorts.sort_of_univ u'
              | TemplatePseudoSortPoly ->
                Sorts.qsort (Sorts.QVar.make_var 0) u'
          in
          Term.mkArity (ctx, concl)
        | RegularArity _, Some _ | TemplateArity _, None -> assert false
      in
      {
        mind_entry_typename = ind.mind_typename;
        mind_entry_arity;
        mind_entry_consnames = Array.to_list ind.mind_consnames;
        mind_entry_lc = Array.map_to_list (fun c ->
            let c = Inductive.abstract_constructor_type_relatively_to_inductive_types_context ntyps mind c in
            let ctx, c = Term.decompose_prod_n_decls nparams c in
            ignore ctx; (* we will check that the produced user_lc is equal to the input *)
            c
          ) ind.mind_user_lc;
      })
      mb.mind_packets
  in
  let mind_entry_variance = Option.map (Array.map (fun v -> Some v)) mb.mind_variance in
  {
    mind_entry_record;
    mind_entry_finite = mb.mind_finite;
    mind_entry_params;
    mind_entry_inds;
    mind_entry_universes;
    mind_entry_variance;
    mind_entry_private = mb.mind_private;
  }

let check_arity env ar1 ar2 = match ar1, ar2 with
  | RegularArity ar, RegularArity {mind_user_arity;mind_sort} ->
    Constr.equal ar.mind_user_arity mind_user_arity &&
    Sorts.equal ar.mind_sort mind_sort
  | TemplateArity ar, TemplateArity {template_level} ->
    UGraph.check_leq_sort (universes env) template_level ar.template_level
    (* template_level is inferred by indtypes, so functor application can produce a smaller one *)
  | (RegularArity _ | TemplateArity _), _ -> assert false

let check_template_pseudo_sort_poly a b =
  match a, b with
  | TemplatePseudoSortPoly, TemplatePseudoSortPoly
  | TemplateUnivOnly, TemplateUnivOnly -> true
  | (TemplatePseudoSortPoly | TemplateUnivOnly), _ -> false

let check_template ar1 ar2 = match ar1, ar2 with
| None, None -> true
| Some ar, Some {template_context; template_param_arguments; template_pseudo_sort_poly} ->
  List.equal Bool.equal ar.template_param_arguments template_param_arguments &&
  ContextSet.equal template_context ar.template_context &&
  check_template_pseudo_sort_poly template_pseudo_sort_poly ar.template_pseudo_sort_poly
| None, Some _ | Some _, None -> false

(* if the generated inductive is squashed the original one must be squashed *)
let check_squashed orig generated = match orig, generated with
  | None, None -> true
  | Some _, None ->
    (* the inductive is from functor instantiation which removed the need for squash *)
    true
  | None, Some _ ->
    (* missing squash *)
    false
  | Some s1, Some s2 ->
    (* functor instantiation can change sort qualities
       (from Type -> Prop)
       Condition: every quality which can make the generated inductive
       squashed must also make the original inductive squashed *)
    match s1, s2 with
    | AlwaysSquashed, AlwaysSquashed -> true
    | AlwaysSquashed, SometimesSquashed _ -> true
    | SometimesSquashed _, AlwaysSquashed -> false
    | SometimesSquashed s1, SometimesSquashed s2 ->
      Sorts.Quality.Set.subset s2 s1

(* Use [eq_ind_chk] because when we rebuild the recargs we have lost
   the knowledge of who is the canonical version.
   Try with to see test-suite/coqchk/include.v *)
let eq_recarg_type ty1 ty2 = match ty1, ty2 with
  | RecArgInd ind1, RecArgInd ind2 -> eq_ind_chk ind1 ind2
  | RecArgPrim c1, RecArgPrim c2 -> Names.Constant.CanOrd.equal c1 c2
  | (RecArgInd _ | RecArgPrim _), _ -> false

let eq_recarg r1 r2 = match r1, r2 with
  | Norec, Norec -> true
  | Mrec ty1, Mrec ty2 -> eq_recarg_type ty1 ty2
  | (Norec | Mrec _), _ -> false

let eq_reloc_tbl = Array.equal (fun x y -> Int.equal (fst x) (fst y) && Int.equal (snd x) (snd y))

let eq_in_context (ctx1, t1) (ctx2, t2) =
  Context.Rel.equal Sorts.relevance_equal Constr.equal ctx1 ctx2 && Constr.equal t1 t2

let check_packet env mind ind
    { mind_typename; mind_arity_ctxt; mind_arity; mind_consnames; mind_user_lc;
      mind_nrealargs; mind_nrealdecls; mind_squashed; mind_nf_lc;
      mind_consnrealargs; mind_consnrealdecls; mind_recargs; mind_relevance;
      mind_nb_constant; mind_nb_args; mind_reloc_tbl } =
  let check = check mind in

  ignore mind_typename; (* passed through *)
  check "mind_arity_ctxt" (Context.Rel.equal Sorts.relevance_equal Constr.equal ind.mind_arity_ctxt mind_arity_ctxt);
  check "mind_arity" (check_arity env ind.mind_arity mind_arity);
  ignore mind_consnames; (* passed through *)
  check "mind_user_lc" (Array.equal Constr.equal ind.mind_user_lc mind_user_lc);
  check "mind_nrealargs" Int.(equal ind.mind_nrealargs mind_nrealargs);
  check "mind_nrealdecls" Int.(equal ind.mind_nrealdecls mind_nrealdecls);
  check "mind_squashed" (check_squashed ind.mind_squashed mind_squashed);

  check "mind_nf_lc" (Array.equal eq_in_context ind.mind_nf_lc mind_nf_lc);
  (* NB: here syntactic equality is not just an optimisation, we also
     care about the shape of the terms *)

  check "mind_consnrealargs" (Array.equal Int.equal ind.mind_consnrealargs mind_consnrealargs);
  check "mind_consnrealdecls" (Array.equal Int.equal ind.mind_consnrealdecls mind_consnrealdecls);

  check "mind_recargs" (Rtree.equal eq_recarg ind.mind_recargs mind_recargs);

  check "mind_relevant" (Sorts.relevance_equal ind.mind_relevance mind_relevance);

  check "mind_nb_args" Int.(equal ind.mind_nb_args mind_nb_args);
  check "mind_nb_constant" Int.(equal ind.mind_nb_constant mind_nb_constant);
  check "mind_reloc_tbl" (eq_reloc_tbl ind.mind_reloc_tbl mind_reloc_tbl);

  ()

let check_same_record r1 r2 = match r1, r2 with
  | NotRecord, NotRecord | FakeRecord, FakeRecord -> true
  | PrimRecord r1, PrimRecord r2 ->
    (* The kernel doesn't care about the names, we just need to check
       that the saved types are correct. *)
    Array.for_all2 (fun (_,_,r1,tys1) (_,_,r2,tys2) ->
        Array.equal Sorts.relevance_equal r1 r2 &&
        Array.equal Constr.equal tys1 tys2)
      r1 r2
  | (NotRecord | FakeRecord | PrimRecord _), _ -> false

let check_inductive env mind mb =
  let entry = to_entry mind mb in
  let { mind_packets; mind_record; mind_finite; mind_ntypes; mind_hyps; mind_univ_hyps;
        mind_nparams; mind_nparams_rec; mind_params_ctxt;
        mind_universes; mind_template; mind_variance; mind_sec_variance;
        mind_private; mind_typing_flags; }
    =
    (* Locally set typing flags for further typechecking *)
    let env = CheckFlags.set_local_flags mb.mind_typing_flags env in
    let mib, not_prim_record = Indtypes.check_inductive env ~sec_univs:None mind entry in
    assert (Option.is_empty not_prim_record);
    mib
  in
  let check = check mind in

  Array.iter2 (check_packet env mind) mb.mind_packets mind_packets;
  check "mind_record" (check_same_record mb.mind_record mind_record);
  check "mind_finite" (mb.mind_finite == mind_finite);
  check "mind_ntypes" Int.(equal mb.mind_ntypes mind_ntypes);
  check "mind_hyps" (List.is_empty mind_hyps);
  check "mind_univ_hyps" (UVars.Instance.is_empty mind_univ_hyps);
  check "mind_nparams" Int.(equal mb.mind_nparams mind_nparams);

  check "mind_nparams_rec" (mb.mind_nparams_rec <= mind_nparams_rec);
  (* module substitution can increase the real number of recursively
     uniform parameters, so be tolerant and use [<=]. *)

  check "mind_params_ctxt" (Context.Rel.equal Sorts.relevance_equal Constr.equal mb.mind_params_ctxt mind_params_ctxt);
  ignore mind_universes; (* Indtypes did the necessary checking *)
  check "mind_template" (check_template mb.mind_template mind_template);
  check "mind_variance" (Option.equal (Array.equal UVars.Variance.equal)
                           mb.mind_variance mind_variance);
  check "mind_sec_variance" (Option.is_empty mind_sec_variance);
  ignore mind_private; (* passed through Indtypes *)

  ignore mind_typing_flags;
  (* TODO non oracle flags *)

  add_mind mind mb env

let check_inductive env mind mb : Environ.env =
  NewProfile.profile "check_inductive"
    ~args:(fun () -> [("name", `String (MutInd.to_string mind))])
    (fun () -> check_inductive env mind mb)
    ()
