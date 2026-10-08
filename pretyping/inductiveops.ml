(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CErrors
open Util
open Names
open EConstr
open Vars
open Context
open Declarations
open Environ
open Reductionops
open Context.Rel.Declaration

(* The following three functions are similar to the ones defined in
   Inductive, but they expect an env *)

let type_of_inductive env (ind,u) =
 let u = EConstr.Unsafe.to_instance u in
 let (mib,_ as specif) = Inductive.lookup_mind_specif env ind in
 EConstr.check_hyps_inclusion env (GlobRef.IndRef ind) mib.mind_hyps;
 let t = Inductive.type_of_inductive (specif,u) in
 EConstr.of_constr @@ Arguments_renaming.rename_type env t (IndRef ind)

let e_type_of_inductive env sigma (ind,u) =
 let (mib,_ as specif) = Inductive.lookup_mind_specif env ind in
 EConstr.check_hyps_inclusion env (GlobRef.IndRef ind) mib.mind_hyps;
 let t = Inductive.type_of_inductive (specif, EConstr.Unsafe.to_instance u) in
 EConstr.of_constr (Arguments_renaming.rename_type env t (IndRef ind))

(* Return type as quoted by the user *)
let type_of_constructor env (cstr,u) =
 let u = EConstr.Unsafe.to_instance u in
 let (mib,_ as specif) =
   Inductive.lookup_mind_specif env (inductive_of_constructor cstr) in
 EConstr.check_hyps_inclusion env (GlobRef.ConstructRef cstr) mib.mind_hyps;
 let t = Inductive.type_of_constructor (cstr,u) specif in
 EConstr.of_constr @@ Arguments_renaming.rename_type env t (ConstructRef cstr)

let e_type_of_constructor env sigma (cstr,u) =
 let (mib,_ as specif) =
   Inductive.lookup_mind_specif env (inductive_of_constructor cstr) in
 EConstr.check_hyps_inclusion env (GlobRef.ConstructRef cstr) mib.mind_hyps;
 let t = Inductive.type_of_constructor (cstr,EConstr.Unsafe.to_instance u) specif in
 EConstr.of_constr (Arguments_renaming.rename_type env t (ConstructRef cstr))

(* Return constructor types in user form *)
let type_of_constructors env (ind,u as indu) =
  let indu = on_snd EConstr.Unsafe.to_instance indu in
  let specif = Inductive.lookup_mind_specif env ind in
  Array.map EConstr.of_constr (Inductive.type_of_constructors indu specif)

(* Return constructor types in normal form *)
let arities_of_constructors env (ind,u as indu) =
  let indu = on_snd EConstr.Unsafe.to_instance indu in
  let specif = Inductive.lookup_mind_specif env ind in
  Array.map EConstr.of_constr (Inductive.arities_of_constructors indu specif)

(* [inductive_family] = [inductive_instance] applied to global parameters *)
type inductive_family = inductive puniverses * constr list

let make_ind_family (mis, params) = (mis,params)
let dest_ind_family (mis,params) : inductive_family = (mis,params)

let map_ind_family f (mis,params) = (mis, List.map f params)

let liftn_inductive_family n d = map_ind_family (liftn n d)
let lift_inductive_family n = liftn_inductive_family n 1

let substnl_ind_family l n = map_ind_family (substnl l n)

let relevance_of_inductive env ind =
  let ind = on_snd EConstr.Unsafe.to_instance ind in
  ERelevance.make @@ Inductive.relevance_of_inductive env ind

let relevance_of_inductive_family env (ind,_ : inductive_family) =
  relevance_of_inductive env ind

type inductive_type = IndType of inductive_family * EConstr.constr list

let ind_of_ind_type = function IndType (((ind,_),_),_) -> ind

let make_ind_type (indf, realargs) = IndType (indf,realargs)
let dest_ind_type (IndType (indf,realargs)) = (indf,realargs)

let map_inductive_type f (IndType (indf, realargs)) =
  IndType (map_ind_family f indf, List.map f realargs)

let liftn_inductive_type n d = map_inductive_type (EConstr.Vars.liftn n d)
let lift_inductive_type n = liftn_inductive_type n 1

let substnl_ind_type l n = map_inductive_type (EConstr.Vars.substnl l n)

let relevance_of_inductive_type env (IndType (indf, _)) =
  relevance_of_inductive_family env indf

let mkAppliedInd (IndType ((ind,params), realargs)) =
  applist (mkIndU ind, params @ realargs)

let dest_recarg p = match Rtree.Kind.kind p with
| Rtree.Kind.Node (ra, _) -> ra
| Rtree.Kind.Var _ -> assert false

let dest_subterms p = match Rtree.Kind.kind p with
| Rtree.Kind.Node (ra, cstrs) ->
  let () = assert (match ra with Norec -> false | _ -> true) in
  cstrs
| Rtree.Kind.Var _ -> assert false

let mis_is_recursive mip =
  let ra = mip.mind_automaton in
  let trans = Rtree.Automaton.transitions ra (Rtree.Automaton.initial ra) in
  let check tr = match Rtree.Automaton.data ra tr with Mrec _ -> true | Norec -> false in
  Array.exists (fun v -> Array.exists check v) trans

let mis_is_nested env kn mib =
  Array.exists (fun mip ->
    let ra = mip.mind_automaton in
    let trans = Rtree.Automaton.transitions ra (Rtree.Automaton.initial ra) in
    Array.exists (fun rvec ->
      Array.exists (fun tr ->
        match Rtree.Automaton.data ra tr with
        | Mrec (RecArgInd (kni, _)) -> not @@ QMutInd.equal env kn kni
        | Mrec (RecArgPrim _) | Norec -> false
      ) rvec
    ) trans
  ) mib.mind_packets

let mis_nf_constructor_type ((_,j),u) (mib,mip) =
  let nconstr = Array.length mip.mind_consnames in
  if j > nconstr then user_err Pp.(str "Not enough constructors in the type.");
  let (ctx, cty) = mip.mind_nf_lc.(j - 1) in
  subst_instance_constr u (EConstr.it_mkProd_or_LetIn (EConstr.of_constr cty) (EConstr.of_rel_context ctx))

(* Number of constructors *)

let nconstructors env ind =
  let (_,mip) = Inductive.lookup_mind_specif env ind in
  Array.length mip.mind_consnames

(* Arity of constructors excluding parameters, excluding local defs *)

let constructors_nrealargs env ind =
  let (_,mip) = Inductive.lookup_mind_specif env ind in
  mip.mind_consnrealargs

(* Arity of constructors excluding parameters, including local defs *)

let constructors_nrealdecls env ind =
  let (_,mip) = Inductive.lookup_mind_specif env ind in
  mip.mind_consnrealdecls

(* Arity of constructors including parameters, excluding local defs *)

let constructor_nallargs env (ind,j) =
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
  mip.mind_consnrealargs.(j-1) + mib.mind_nparams

(* Arity of constructors including params, including local defs *)

let constructor_nalldecls env (ind,j) = (* TOCHANGE en decls *)
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
  mip.mind_consnrealdecls.(j-1) + Context.Rel.length (mib.mind_params_ctxt)

(* Arity of constructors excluding params, excluding local defs *)

let constructor_nrealargs env (ind,j) =
  let (_,mip) = Inductive.lookup_mind_specif env ind in
  mip.mind_consnrealargs.(j-1)

(* Arity of constructors excluding params, including local defs *)

let constructor_nrealdecls env (ind,j) = (* TOCHANGE en decls *)
  let (_,mip) = Inductive.lookup_mind_specif env ind in
  mip.mind_consnrealdecls.(j-1)

(* Length of arity, excluding params, excluding local defs *)

let inductive_nrealargs env ind =
  let (_,mip) = Inductive.lookup_mind_specif env ind in
  mip.mind_nrealargs

(* Length of arity, excluding params, including local defs *)

let inductive_nrealdecls env ind =
  let (_,mip) = Inductive.lookup_mind_specif env ind in
  mip.mind_nrealdecls

(* Full length of arity (w/o local defs) *)

let inductive_nallargs env ind =
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
  mib.mind_nparams + mip.mind_nrealargs

(* Length of arity (w/o local defs) *)

let inductive_nparams env ind =
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
  mib.mind_nparams

(* Length of arity (with local defs) *)

let inductive_nparamdecls env ind =
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
  Context.Rel.length mib.mind_params_ctxt

(* Full length of arity (with local defs) *)

let inductive_nalldecls env ind =
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
  Context.Rel.length (mib.mind_params_ctxt) + mip.mind_nrealdecls

(* Others *)

let get_template_instance mib u = match Declareops.inductive_template mib with
| None -> u
| Some templ ->
  let () = assert (UVars.Instance.is_empty (EConstr.Unsafe.to_instance u)) in
  EInstance.make (UVars.Instance.of_level_instance templ.template_defaults)

let inductive_paramdecls env (ind,u) =
  let u = EConstr.Unsafe.to_instance u in
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
  EConstr.of_rel_context @@ Inductive.inductive_paramdecls (mib,u)

let inductive_alldecls env (ind,u) =
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
  let u = get_template_instance mib u in
  Vars.subst_instance_context u (EConstr.of_rel_context mip.mind_arity_ctxt)

let inductive_alltags env ind =
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
  Context.Rel.to_tags mip.mind_arity_ctxt

let constructor_alltags env (ind,j) =
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
  Context.Rel.to_tags (fst mip.mind_nf_lc.(j-1))

let inductive_has_local_defs env ind =
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
  let l1 = Context.Rel.length (mib.mind_params_ctxt) + mip.mind_nrealdecls in
  let l2 = mib.mind_nparams + mip.mind_nrealargs in
  not (Int.equal l1 l2)

let squash_elim_sort sigma squash rtnsort =
  let open Inductive in
  let add_unif_if_cannot_elim_into pb starget =
    let q = Sorts.quality starget in
    let q' = ESorts.quality sigma rtnsort in
    if Inductive.eliminates_to (Evd.elim_graph sigma) q q'
    then sigma
    else pb sigma (ESorts.make starget) rtnsort in
  match squash with
  | SquashToSet ->
     add_unif_if_cannot_elim_into Evd.set_eq_sort Sorts.set
     (* Squashed inductive in Set, only happens with impredicative Set *)
  | SquashToQuality (QConstant QProp) ->
     add_unif_if_cannot_elim_into Evd.set_eq_sort Sorts.prop
     (* Squashed inductive in Prop, return sort must be Prop or SProp *)
  | SquashToQuality (QConstant QSProp) ->
     add_unif_if_cannot_elim_into Evd.set_eq_sort Sorts.sprop
     (* Squashed inductive in SProp, return sort must be SProp. *)
  | SquashToQuality (QConstant QType) ->
     add_unif_if_cannot_elim_into Evd.set_leq_sort Sorts.set
     (* Sort poly squash to type *)
  | SquashToQuality (QGlobal _ as q) ->
    add_unif_if_cannot_elim_into Evd.set_leq_sort (Sorts.make q Univ.Universe.type0)
    (* sort poly squash to global *)
  | SquashToQuality (QVar q) ->
     let q' = ESorts.quality sigma rtnsort in
     let g = Evd.elim_graph sigma in
     if Inductive.eliminates_to g (QVar q) q' then sigma
     else Evd.set_elim_to sigma (QVar q) q'

let is_squashed sigma (specif,u) =
  Inductive.is_squashed_gen
    (Evd.elim_graph sigma)
    (UState.nf_quality (Evd.ustate sigma))
    (specif,EConstr.Unsafe.to_instance u)

let is_allowed_elimination sigma ((_,mip) as specif,u) s =
  match mip.mind_record with
  | PrimRecord _ -> true
  | NotRecord | FakeRecord ->
    let s = EConstr.ESorts.kind sigma s in
    let g = Evd.elim_graph sigma in
    Inductive.allowed_elimination_gen g
      (UState.nf_quality (Evd.ustate sigma))
      (Inductive.is_allowed_elimination_actions g s)
      (specif,EConstr.Unsafe.to_instance u)
      s

let make_allowed_elimination_actions sigma s =
  Inductive.{
    not_squashed = Some sigma
  ; squashed_to_set_below = Some sigma
  ; squashed_to_set_above = (
    try Some (Evd.set_leq_sort sigma s ESorts.set)
    with QGraph.EliminationError _ | UGraph.UniverseInconsistency _ -> None)
  ; squashed_to_quality = fun indq ->
      let sq = EConstr.ESorts.quality sigma s in
      if Inductive.eliminates_to (Evd.elim_graph sigma) indq sq
      then Some sigma
      else
        try Some (Evd.set_elim_to sigma indq sq)
        with QGraph.EliminationError _ | UGraph.UniverseInconsistency _ -> None }

let make_allowed_elimination sigma ((_,mip) as specif,u) s =
  match mip.mind_record with
  | PrimRecord _ -> Some sigma
  | NotRecord | FakeRecord ->
    Inductive.allowed_elimination_gen
      (Evd.elim_graph sigma)
      (UState.nf_quality (Evd.ustate sigma))
      (make_allowed_elimination_actions sigma s)
      (specif,EConstr.Unsafe.to_instance u)
      (EConstr.ESorts.kind sigma s)

(* XXX questionable for sort poly inductives *)
let elim_sort (mib,mip) =
  let is_record =
    match mip.mind_record with
    | NotRecord | FakeRecord -> false
    | PrimRecord _ -> true in
  let has_args mip =
    let rec types_prod t = match Constr.kind t with
      | Prod(_,ct,t) -> ct::(types_prod t)
      | _ -> []
    in
    let field_types =
      List.skipn mib.mind_nparams (types_prod mip.mind_user_lc.(0)) in
    List.exists (fun t -> List.length (types_prod t) > 1) field_types in
  (* Allow large elimination on non-squashed inductives except when it's
     a primitive record in SProp such that any of its "subconstructors" has
     arguments. We'd wish for a more uniform management of this case in the
     future. *)
  if Option.is_empty mip.mind_squashed &&
       not (is_record && has_args mip && Sorts.is_sprop mip.mind_sort)
  then UnivGen.QualityOrSet.qtype
  else if Sorts.is_set mip.mind_sort then Set
  else UnivGen.QualityOrSet.of_quality @@ Sorts.quality mip.mind_sort

let top_allowed_sort env (kn,i as ind) =
  let specif = Inductive.lookup_mind_specif env ind in
  elim_sort specif

let constant_sorts_below top =
  List.filter
    (UnivGen.QualityOrSet.eliminates_to top)
    (UnivGen.QualityOrSet.all_constants)

let sorts_for_schemes specif =
  constant_sorts_below (elim_sort specif)

let has_valid_relevance sigma u ind_relevance flds =
  match ERelevance.kind sigma ind_relevance with
  | Sorts.Irrelevant -> true
  | Sorts.Relevant -> Array.exists (fun r -> Sorts.is_relevant @@ ERelevance.kind sigma r) flds
  | Sorts.RelevanceVar qv ->
    Array.for_all (fun r -> match ERelevance.kind sigma r with
        | Sorts.Relevant -> true
        | Sorts.Irrelevant -> false
        | Sorts.RelevanceVar qv' -> Sorts.QVar.equal qv qv') flds

let always_dependent_elim (mib,mip) =
  match mip.mind_record with
  | NotRecord | FakeRecord -> true
  | PrimRecord r -> match r.has_eta with
    | AlwaysEta -> true
    | NoEta | MaybeEta -> mip.mind_relevance == Irrelevant

let has_dependent_elim sigma (mib,mip) u =
  match mip.mind_record with
  | NotRecord | FakeRecord -> true
  | PrimRecord r ->
    match r.has_eta with
    | AlwaysEta -> true
    | NoEta ->
      let ind_relevance =
        EConstr.Vars.subst_instance_relevance u (ERelevance.make mip.mind_relevance)
      in
      ERelevance.is_irrelevant sigma ind_relevance
    | MaybeEta ->
      let ind_relevance =
        EConstr.Vars.subst_instance_relevance u (ERelevance.make mip.mind_relevance)
      in
      let flds =
        Array.map (fun r -> EConstr.Vars.subst_instance_relevance u (ERelevance.make r)) r.relevances
      in
      has_valid_relevance sigma u ind_relevance flds

(* Annotation for cases *)
let make_case_info env ind style =
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
  let print_info = { Constr.style } in
  { Constr.ci_ind     = ind;
    ci_npar    = mib.mind_nparams;
    ci_cstr_ndecls = mip.mind_consnrealdecls;
    ci_cstr_nargs = mip.mind_consnrealargs;
    ci_pp_info = print_info }

(*s Useful functions *)

type constructor_summary = {
  cs_name : Id.t;
  cs_cstr : constructor puniverses;
  cs_params : constr list;
  cs_nargs : int;
  cs_args : EConstr.rel_context;
  cs_concl_realargs : constr array
}

let lift_constructor n cs = {
  cs_name = cs.cs_name;
  cs_cstr = cs.cs_cstr;
  cs_params = List.map (lift n) cs.cs_params;
  cs_nargs = cs.cs_nargs;
  cs_args = Vars.lift_rel_context n cs.cs_args;
  cs_concl_realargs = Array.map (liftn n (cs.cs_nargs+1)) cs.cs_concl_realargs
}

(* Accept either all parameters or only recursively uniform ones *)
let instantiate_params t params sign =
  let nnonrecpar = Context.Rel.nhyps sign - List.length params in
  (* Adjust the signature if recursively non-uniform parameters are not here *)
  let _,sign = Context.Rel.chop_nhyps nnonrecpar sign in
  let _,t = Term.decompose_prod_n_decls (Context.Rel.length sign) t in
  let subst = subst_of_rel_context_instance_list sign params in
  substl subst (EConstr.of_constr t)

let instantiate_constructor_params (_,u as cstru) (mib,_ as mind_specif) params =
  let typi = mis_nf_constructor_type cstru mind_specif in
  let ctx = Vars.subst_instance_context u (EConstr.of_rel_context mib.mind_params_ctxt) in
  instantiate_params (EConstr.Unsafe.to_constr typi) params ctx

let get_constructor ((ind,u),mib,mip,params) j =
  assert (j <= Array.length mip.mind_consnames);
  let typi = instantiate_constructor_params ((ind,j),u) (mib,mip) params in
  let typi = EConstr.Unsafe.to_constr typi in
  let (args,ccl) = Term.decompose_prod_decls typi in
  let (_,allargs) = Constr.decompose_app_list ccl in
  let vargs = List.skipn (List.length params) allargs in
  let name = mip.mind_consnames.(j-1) in
  { cs_name = name;
    cs_cstr = (ith_constructor_of_inductive ind j,u);
    cs_params = params;
    cs_nargs = Context.Rel.length args;
    cs_args = EConstr.of_rel_context args;
    cs_concl_realargs = Array.map_of_list EConstr.of_constr vargs }

let get_constructors env (ind,params) =
  let (mib,mip) = Inductive.lookup_mind_specif env (fst ind) in
  Array.init (Array.length mip.mind_consnames)
    (fun j -> get_constructor (ind,mib,mip,params) (j+1))

let get_projections = Environ.get_projections

(* ************************************* *)
module Internal = struct
(* FIXME temporary copy of [Typeops] functions: previously, there was an hack in
   place to make the kernel aware of [QVar]s eliminating to [Prop]. It's not
   working anymore with the [QGraph], so we redefine [nf_relevance] and
   [should_invert_case] to work with the [QGraph] in [sigma] (which knows the
   relevant [QVar]s *)
let nf_relevance sigma = function
  | Sorts.RelevanceVar q as r ->
     if UState.is_above_prop (Evd.ustate sigma) q
     then Sorts.Relevant
     else r
  | (Sorts.Irrelevant | Sorts.Relevant) as r -> r

let should_invert_case env sigma r (ci : Constr.case_info) =
  Sorts.relevance_equal (nf_relevance sigma r) Sorts.Relevant &&
    let mib,mip = Inductive.lookup_mind_specif env ci.ci_ind in
    (* mind_relevance cannot be a pseudo sort poly variable so don't use check_relevance *)
    Sorts.relevance_equal mip.mind_relevance Sorts.Irrelevant &&
      match Array.length mip.mind_nf_lc with
      | 0 -> true
      | 1 ->
         List.length (fst mip.mind_nf_lc.(0)) = List.length mib.mind_params_ctxt
      | _ -> false
end
(* ************************************* *)

let make_case_invert env sigma (IndType (((ind,u),params),indices)) ~case_relevance:r ci =
  let r = ERelevance.kind sigma r in
  if Internal.should_invert_case env sigma r ci
  then Constr.CaseInvert {indices=Array.of_list indices}
  else Constr.NoInvert

let make_project env sigma ind pred c branches ps =
  assert(Array.length branches == 1);
  let na, ty, t = destLambda sigma pred in
  let _, u = destInd sigma (fst (decompose_app sigma ty)) in
  let mib, mip as specif = Inductive.lookup_mind_specif env ind in
  let () =
    if (* dependent *) not (Vars.noccurn sigma 1 t) &&
         not (has_dependent_elim sigma specif u) then
      Pretype_errors.error_not_allowed_dependent_elimination env sigma false ind
  in
  let branch = branches.(0) in
  let ctx, br = decompose_lambda_n_decls sigma mip.mind_consnrealdecls.(0) branch in
  let mkProj i c =
    let p, r = ps.(i) in
    let r = EConstr.Vars.subst_instance_relevance u (ERelevance.make r) in
    mkProj (Projection.make p true, r, c)
  in
  let proj = match EConstr.destRel sigma br with
    | exception Constr.DestKO -> None
    | i ->
      begin match List.skipn (i-1) ctx with
      | exception Failure _ -> None
      | ctx -> match ctx with
        | [] -> None
        | LocalDef _ :: _ ->
          (* XXX Maybe we should produce the applied constant for this letin pseudoprojection?
             We would have to get the params etc*)
          None
        | LocalAssum _ :: ctx ->
          (* This match is just a projection *)
          Some (mkProj (Context.Rel.nhyps ctx) c)
      end
  in
  match proj with
  | Some proj -> proj
  | None ->
  let n, len, ctx =
    List.fold_right
      (fun decl (i, j, ctx) ->
         match decl with
         | LocalAssum (na, ty) ->
           let t = mkProj i (mkRel j) in
           (i + 1, j + 1, LocalDef (na, t, Vars.liftn 1 j ty) :: ctx)
         | LocalDef (na, b, ty) ->
           (i, j + 1, LocalDef (na, Vars.liftn 1 j b, Vars.liftn 1 j ty) :: ctx))
      ctx (0, 1, [])
  in
  mkLetIn (na, c, ty, it_mkLambda_or_LetIn (Vars.liftn 1 (mip.mind_consnrealdecls.(0) + 1) br) ctx)

let simple_make_case_or_project env sigma ci pred invert c branches =
  let ind = ci.Constr.ci_ind in
  let projs = get_projections env ind in
  match projs with
  | None -> mkCase (EConstr.contract_case env sigma (ci, pred, invert, c, branches))
  | Some ps -> make_project env sigma ind (fst pred) c branches ps

let make_case_or_project env sigma indt ci pred c branches =
  let IndType (((ind,_),_),_) = indt in
  let projs = get_projections env ind in
  match projs with
  | None ->
     let invert = make_case_invert env sigma indt ~case_relevance:(snd pred) ci in
     mkCase (EConstr.contract_case env sigma (ci, pred, invert, c, branches))
  | Some ps -> make_project env sigma ind (fst pred) c branches ps

(* substitution in a signature *)

let substnl_rel_context subst n sign =
  let rec aux n = function
  | d::sign -> substnl_decl subst n d :: aux (n+1) sign
  | [] -> []
  in List.rev (aux n (List.rev sign))

let substl_rel_context subst = substnl_rel_context subst 0

let get_arity env ((ind,u),params) =
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
  let parsign =
    (* Dynamically detect if called with an instance of recursively
       uniform parameter only or also of recursively non-uniform
       parameters *)
    let u = EConstr.Unsafe.to_instance u in
    let nparams = List.length params in
    if Int.equal nparams mib.mind_nparams then
      Inductive.inductive_paramdecls (mib,u)
    else begin
      assert (Int.equal nparams mib.mind_nparams_rec);
      snd (Inductive.inductive_nonrec_rec_paramdecls (mib,u))
    end in
  let parsign = EConstr.of_rel_context parsign in
  let arproperlength = List.length mip.mind_arity_ctxt - List.length parsign in
  let arsign,_ = List.chop arproperlength mip.mind_arity_ctxt in
  let arsign = EConstr.of_rel_context arsign in
  let subst = subst_of_rel_context_instance_list parsign params in
  let arsign = Vars.subst_instance_context u arsign in
  substl_rel_context subst arsign

(* Functions to build standard types related to inductive *)
let build_dependent_constructor cs =
  applist
    (mkConstructU cs.cs_cstr,
     (List.map (lift cs.cs_nargs) cs.cs_params)
      @(Context.Rel.instance_list mkRel 0 cs.cs_args))

let build_dependent_inductive env ((ind, params) as indf) =
  let arsign = get_arity env indf in
  let nrealargs = List.length arsign in
  applist
    (mkIndU ind,
     (List.map (lift nrealargs) params)@(Context.Rel.instance_list mkRel 0 arsign))

(* builds the arity of an elimination predicate in sort [s] *)

let make_arity_signature env sigma dep (ind, _ as indf) =
  let arsign = get_arity env indf in
  let r = relevance_of_inductive env ind in
  let anon = make_annot Anonymous r in
  if dep then
    (* We need names everywhere *)
    Namegen.name_context env sigma
      ((LocalAssum (anon, build_dependent_inductive env indf)) :: arsign)
      (* Costly: would be better to name once for all at definition time *)
  else
    (* No need to enforce names *)
    arsign

let make_arity env sigma dep indf s =
  it_mkProd_or_LetIn (mkSort s) (make_arity_signature env sigma dep indf)

(**************************************************)

(** From a rel context describing the constructor arguments,
    build an expansion function.
    The term built is expecting to be substituted first by
    a substitution of the form [params, x : ind params] *)
let compute_projections env (kn, i as ind) =
  let mib = Environ.lookup_mind kn env in
  let u = UVars.make_abstract_instance (Declareops.inductive_polymorphic_context mib) in
  let u = EInstance.make u in
  let x = match mib.mind_packets.(i).mind_record with
  | NotRecord | FakeRecord ->
    anomaly Pp.(str "Trying to build primitive projections for a non-primitive record")
  | PrimRecord { id ; _ } ->
    make_annot (Name id) (ERelevance.make mib.mind_packets.(i).mind_relevance)
  in
  let pkt = mib.mind_packets.(i) in
  let { mind_nparams = nparamargs; mind_params_ctxt = params } = mib in
  let params = EConstr.of_rel_context params in
  let ctx, _ = pkt.mind_nf_lc.(0) in
  let ctx, paramslet = List.chop pkt.mind_consnrealdecls.(0) ctx in
  let ctx = EConstr.of_rel_context ctx in
  (* We build a substitution smashing the lets in the record parameters so
     that typechecking projections requires just a substitution and not
     matching with a parameter context. *)
  let indty =
    (* [ty] = [Ind inst] is typed in context [params] *)
    let inst = Context.Rel.instance mkRel 0 paramslet in
    let indu = mkIndU (ind, u) in
    let ty = mkApp (indu, inst) in
    (* [Ind inst] is typed in context [params-wo-let] *)
    ty
  in
  let projections decl (proj_arg, j, pbs, subst) =
    match decl with
    | LocalDef (na,c,t) ->
        (* From [params, field1,..,fieldj |- c(params,field1,..,fieldj)]
           to [params, x:I, field1,..,fieldj |- c(params,field1,..,fieldj)] *)
        let c = liftn 1 j c in
        (* From [params, x:I, field1,..,fieldj |- c(params,field1,..,fieldj)]
           to [params, x:I |- c(params,proj1 x,..,projj x)] *)
        let c1 = substl subst c in
        (* From [params, x:I |- subst:field1,..,fieldj]
           to [params, x:I |- subst:field1,..,fieldj+1] where [subst]
           is represented with instance of field1 last *)
        let subst = c1 :: subst in
        (proj_arg, j+1, pbs, subst)
    | LocalAssum (na,t) ->
      match na.binder_name with
      | Name _lab ->
        let proj_relevant = na.binder_relevance in
        let kn = Projection.Repr.make ind ~proj_npars:mib.mind_nparams ~proj_arg in
        (* from [params, field1,..,fieldj |- t(params,field1,..,fieldj)]
           to [params, x:I, field1,..,fieldj |- t(params,field1,..,fieldj] *)
        let t = liftn 1 j t in
        (* from [params, x:I, field1,..,fieldj |- t(params,field1,..,fieldj)]
           to [params-wo-let, x:I |- t(params,proj1 x,..,projj x)] *)
        (* from [params, x:I, field1,..,fieldj |- t(field1,..,fieldj)]
           to [params, x:I |- t(proj1 x,..,projj x)] *)
        let ty = substl subst t in
        let term = mkProj (Projection.make kn true, proj_relevant, mkRel 1) in
        let fterm = mkProj (Projection.make kn false, proj_relevant, mkRel 1) in
        let etab = it_mkLambda_or_LetIn (mkLambda (x, indty, term)) params in
        let etat = it_mkProd_or_LetIn (mkProd (x, indty, ty)) params in
        let body = (etab, etat) in
        (proj_arg + 1, j + 1, body :: pbs, fterm :: subst)
      | Anonymous ->
        anomaly Pp.(str "Trying to build primitive projections for a non-primitive record")
  in
  let (_, _, pbs, subst) =
    List.fold_right projections ctx (0, 1, [], [])
  in
  Array.rev_of_list pbs

(**************************************************)

let extract_mrectype sigma t =
  let open EConstr in
  let (t, l) = decompose_app_list sigma t in
  match EConstr.kind sigma t with
    | Ind ind -> (ind, l)
    | _ -> raise Not_found

let find_mrectype_vect env sigma c =
  let (t, l) = EConstr.decompose_app sigma (whd_all env sigma c) in
  match EConstr.kind sigma t with
    | Ind ind -> (ind, l)
    | _ -> raise Not_found

let find_mrectype env sigma c =
  let (ind, v) = find_mrectype_vect env sigma c in (ind, Array.to_list v)

let find_rectype env sigma c =
  let open EConstr in
  let (t, l) = decompose_app_list sigma (whd_all env sigma c) in
  match EConstr.kind sigma t with
    | Ind (ind,u) ->
        let (mib,mip) = Inductive.lookup_mind_specif env ind in
        if mib.mind_nparams > List.length l then raise Not_found;
        let (par,rargs) = List.chop mib.mind_nparams l in
        let indu = (ind, u) in
        IndType ((indu, par), rargs)
    | _ -> raise Not_found

let find_inductive env sigma c =
  let open EConstr in
  let (t, l) = decompose_app_list sigma (whd_all env sigma c) in
  match EConstr.kind sigma t with
    | Ind ind
        when (fst (Inductive.lookup_mind_specif env (fst ind))).mind_finite <> CoFinite ->
        (ind, l)
    | _ -> raise Not_found

let find_coinductive env sigma c =
  let open EConstr in
  let (t, l) = decompose_app_list sigma (whd_all env sigma c) in
  match EConstr.kind sigma t with
    | Ind ind
        when (fst (Inductive.lookup_mind_specif env (fst ind))).mind_finite == CoFinite ->
        (ind, l)
    | _ -> raise Not_found


(* Type of Case predicates *)
let arity_of_case_predicate env (ind,params) dep k =
  let arsign = get_arity env (ind,params) in
  let r = relevance_of_inductive env ind in
  let mind = build_dependent_inductive env (ind,params) in
  let concl = if dep then mkArrow mind r (mkSort k) else mkSort k in
  it_mkProd_or_LetIn concl arsign

let type_of_projection_constant env (p,u) =
  let _, pty = lookup_projection p env in
  EConstr.Vars.subst_instance_constr u (EConstr.of_constr pty)

let type_of_projection_knowing_arg env sigma p c ty =
  let open EConstr.Vars in
  let IndType(pars,realargs) =
    try find_rectype env sigma ty
    with Not_found ->
      raise (Invalid_argument "type_of_projection_knowing_arg_type: not an inductive type")
  in
  let (_,u), pars = dest_ind_family pars in
  substl (c :: List.rev pars) (type_of_projection_constant env (p,u))

(***********************************************)
(* Guard condition *)

(* A function which checks that a term well typed verifies both
   syntactic conditions *)

let control_only_guard env sigma c =
  let evars = Evd.evar_handler sigma in
  let c = Evarutil.nf_evar sigma c in
  let check_fix_cofix e c =
    (* [c] has already been normalized upfront *)
    let c = EConstr.Unsafe.to_constr c in
    match Constr.kind c with
    | CoFix (_,(_,_,_) as cofix) ->
      Inductive.check_cofix ~evars e cofix
    | Fix fix ->
      Inductive.check_fix ~evars e fix
    | _ -> ()
  in
  let rec iter env c =
    check_fix_cofix env c;
    EConstr.iter_with_full_binders env sigma EConstr.push_rel iter env c
  in
  try iter env c
  with Type_errors.TypeError (env, e) ->
    raise (Pretype_errors.PretypeError
             (env, sigma,
              TypingError (Pretype_errors.of_type_error e)))

(** Generalize template polymorphic universe variables, subtitute the instance,
    and returns the context of parameters, the new evar_map, and the
    substitution for the template variable if there is one. *)
let paramdecls_fresh_template sigma (mib,u) =
  match mib.mind_universes with
  | Polymorphic _ ->
    let params = Inductive.inductive_paramdecls (mib, EConstr.Unsafe.to_instance u) in
    sigma, EConstr.of_rel_context params, None
  | Template templ ->
    assert (EConstr.EInstance.is_empty u);
    let sigma, univs = List.fold_left_map (fun sigma -> function
        | None -> sigma, (fun ~default -> assert false)
        | Some s ->
          let sigma, u = match snd (Inductive.Template.bind_kind s) with
            | None -> sigma, Univ.Universe.type0
            | Some _ ->
              let sigma, u = Evd.new_univ_level_variable UState.univ_rigid sigma in
              sigma, Univ.Universe.make u
          in
          sigma, fun ~default -> Inductive.TemplateUniv u)
        sigma
        templ.template_param_arguments
    in
    let csts, params, sub = Inductive.instantiate_template_universes mib univs in
    let sigma = Evd.add_poly_constraints ~src:UState.Internal sigma csts in
    (sigma, EConstr.of_rel_context params, Some sub)
