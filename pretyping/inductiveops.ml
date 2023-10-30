(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
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
open Term
open Constr
open Vars
open Context
open Declarations
open Declareops
open Environ
open Reductionops
open Context.Rel.Declaration

(* The following three functions are similar to the ones defined in
   Inductive, but they expect an env *)

let type_of_inductive env (ind,u) =
 let (mib,_ as specif) = Inductive.lookup_mind_specif env ind in
 Typeops.check_hyps_inclusion env (GlobRef.IndRef ind) mib.mind_hyps;
 let t = Inductive.type_of_inductive (specif,u) in
 Arguments_renaming.rename_type t (IndRef ind)

let e_type_of_inductive env sigma (ind,u) =
 let (mib,_ as specif) = Inductive.lookup_mind_specif env ind in
 Reductionops.check_hyps_inclusion env sigma (GlobRef.IndRef ind) mib.mind_hyps;
 let t = Inductive.type_of_inductive (specif, EConstr.Unsafe.to_instance u) in
 EConstr.of_constr (Arguments_renaming.rename_type t (IndRef ind))

(* Return type as quoted by the user *)
let type_of_constructor env (cstr,u) =
 let (mib,_ as specif) =
   Inductive.lookup_mind_specif env (inductive_of_constructor cstr) in
 Typeops.check_hyps_inclusion env (GlobRef.ConstructRef cstr) mib.mind_hyps;
 let t = Inductive.type_of_constructor (cstr,u) specif in
 Arguments_renaming.rename_type t (ConstructRef cstr)

let e_type_of_constructor env sigma (cstr,u) =
 let (mib,_ as specif) =
   Inductive.lookup_mind_specif env (inductive_of_constructor cstr) in
 Reductionops.check_hyps_inclusion env sigma (GlobRef.ConstructRef cstr) mib.mind_hyps;
 let t = Inductive.type_of_constructor (cstr,EConstr.Unsafe.to_instance u) specif in
 EConstr.of_constr (Arguments_renaming.rename_type t (ConstructRef cstr))

(* Return constructor types in user form *)
let type_of_constructors env (ind,u as indu) =
 let specif = Inductive.lookup_mind_specif env ind in
  Inductive.type_of_constructors indu specif

(* Return constructor types in normal form *)
let arities_of_constructors env (ind,u as indu) =
 let specif = Inductive.lookup_mind_specif env ind in
  Inductive.arities_of_constructors indu specif

(* [inductive_family] = [inductive_instance] applied to global parameters *)
type inductive_family = pinductive * constr list

let make_ind_family (mis, params) = (mis,params)
let dest_ind_family (mis,params) : inductive_family = (mis,params)

let map_ind_family f (mis,params) = (mis, List.map f params)

let liftn_inductive_family n d = map_ind_family (liftn n d)
let lift_inductive_family n = liftn_inductive_family n 1

let substnl_ind_family l n = map_ind_family (substnl l n)

let relevance_of_inductive_family env (ind,_ : inductive_family) =
  Inductive.relevance_of_inductive env ind

type inductive_type = IndType of inductive_family * EConstr.constr list

let ind_of_ind_type = function IndType (((ind,_),_),_) -> ind

let make_ind_type (indf, realargs) = IndType (indf,realargs)
let dest_ind_type (IndType (indf,realargs)) = (indf,realargs)

let map_inductive_type f (IndType (indf, realargs)) =
  let f' c = EConstr.Unsafe.to_constr (f (EConstr.of_constr c)) in
  IndType (map_ind_family f' indf, List.map f realargs)

let liftn_inductive_type n d = map_inductive_type (EConstr.Vars.liftn n d)
let lift_inductive_type n = liftn_inductive_type n 1

let substnl_ind_type l n = map_inductive_type (EConstr.Vars.substnl l n)

let relevance_of_inductive_type env (IndType (indf, _)) =
  relevance_of_inductive_family env indf

let mkAppliedInd (IndType ((ind,params), realargs)) =
  let open EConstr in
  let ind = on_snd EInstance.make ind in
  applist (mkIndU ind, (List.map EConstr.of_constr params)@realargs)

(* Does not consider imbricated or mutually recursive types *)
let mis_is_recursive_subset listind rarg =
  let one_is_rec rvec =
    List.exists
      (fun ra ->
        match dest_recarg ra with
          | Mrec (RecArgInd ind) -> List.exists (Names.Ind.CanOrd.equal ind) listind
          | Mrec (RecArgPrim _) | Norec -> false) rvec
  in
  Array.exists one_is_rec (dest_subterms rarg)

let mis_is_recursive ((ind,_),mib,mip) =
  mis_is_recursive_subset (List.init mib.mind_ntypes (fun i -> (ind,i)))
    mip.mind_recargs

let mis_nf_constructor_type ((_,j),u) (mib,mip) =
  let nconstr = Array.length mip.mind_consnames in
  if j > nconstr then user_err Pp.(str "Not enough constructors in the type.");
  let (ctx, cty) = mip.mind_nf_lc.(j - 1) in
  subst_instance_constr u (Term.it_mkProd_or_LetIn cty ctx)

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

let inductive_paramdecls env (ind,u) =
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
    Inductive.inductive_paramdecls (mib,u)

let inductive_alldecls env (ind,u) =
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
    Vars.subst_instance_context u mip.mind_arity_ctxt

let inductive_alltags env ind =
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
  Context.Rel.to_tags mip.mind_arity_ctxt

let constructor_alltags env (ind,j) =
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
  Context.Rel.to_tags (fst mip.mind_nf_lc.(j-1))

let constructor_has_local_defs env (indsp,j) =
  let (mib,mip) = Inductive.lookup_mind_specif env indsp in
  let l1 = mip.mind_consnrealdecls.(j-1) + Context.Rel.length (mib.mind_params_ctxt) in
  let l2 = recarg_length mip.mind_recargs j + mib.mind_nparams in
  not (Int.equal l1 l2)

let inductive_has_local_defs env ind =
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
  let l1 = Context.Rel.length (mib.mind_params_ctxt) + mip.mind_nrealdecls in
  let l2 = mib.mind_nparams + mip.mind_nrealargs in
  not (Int.equal l1 l2)

(* XXX use above_prop from the ustate *)
let quality_leq q q' =
  let open Sorts.Quality in
  match q, q' with
  | QVar q, QVar q' -> Sorts.QVar.equal q q'
  | QConstant q, QConstant q' ->
    begin match q, q' with
    | QSProp, _
    | _, QType
    | QProp, QProp
      -> true
    | (QProp|QType), _ -> false
    end
  | (QVar _|QConstant _), _ -> false

type squash = SquashToSet | SquashToQuality of Sorts.Quality.t

let is_squashed sigma ((_,mip),u) =
  match mip.mind_arity with
  | TemplateArity _ -> None (* template is never squashed *)
  | RegularArity a ->
    match mip.mind_squashed with
    | None -> None
    | Some squash ->
      let indq = EConstr.ESorts.quality sigma
          (EConstr.ESorts.make @@ UVars.subst_instance_sort u a.mind_sort)
      in
      match squash with
      | AlwaysSquashed -> begin match a.mind_sort with
          | Sorts.Set -> Some SquashToSet
          | _ -> Some (SquashToQuality indq)
        end
      | SometimesSquashed squash ->
        (* impredicative set squashes are always AlwaysSquashed,
           so here if inds=Set it is a sort poly squash (see "foo6" in test sort_poly.v) *)
        if Sorts.Quality.Set.for_all (fun q ->
            let q = UVars.subst_instance_quality u q in
            let q = UState.nf_quality (Evd.evar_universe_context sigma) q in
            quality_leq q indq) squash
        then None
        else Some (SquashToQuality indq)

let is_allowed_elimination sigma ((mib,_),_ as specifu) s =
  let open Sorts in
  match mib.mind_record with
  | PrimRecord _ -> true
  | NotRecord | FakeRecord ->
    match is_squashed sigma specifu with
    | None -> true
    | Some SquashToSet ->
      begin match EConstr.ESorts.kind sigma s with
      | SProp|Prop|Set -> true
      | QSort _ | Type _ ->
        (* XXX in [Type u] case, should we check [u == set] in the ugraph? *)
        false
      end
    | Some (SquashToQuality indq) -> quality_leq (EConstr.ESorts.quality sigma s) indq

let elim_sort (_,mip) =
  if Option.is_empty mip.mind_squashed then Sorts.InType
  else Inductive.inductive_sort_family mip

let top_allowed_sort env (kn,i as ind) =
  let specif = Inductive.lookup_mind_specif env ind in
  elim_sort specif

let sorts_below top =
  List.filter (fun s ->
      Sorts.family_equal s top
      || match s, top with
      | InQSort, _ -> assert false
      | _, InQSort -> false
      | InSProp, _ -> true
      | InProp, InSet -> true
      | _, InType -> true
      | (InProp|InSet|InType), _ -> false)
    Sorts.[InSProp;InProp;InSet;InType]

let sorts_for_schemes specif =
  sorts_below (elim_sort specif)

let has_dependent_elim (mib,mip) =
  match mib.mind_record with
  | PrimRecord _ -> mib.mind_finite == BiFinite || mip.mind_relevance == Irrelevant
  | NotRecord | FakeRecord -> true

(* Annotation for cases *)
let make_case_info env ind style =
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
  let ind_tags =
    Context.Rel.to_tags (List.firstn mip.mind_nrealdecls mip.mind_arity_ctxt) in
  let cstr_tags =
    Array.map2 (fun (d, _) n ->
      Context.Rel.to_tags (List.firstn n d))
      mip.mind_nf_lc mip.mind_consnrealdecls in
  let print_info = { ind_tags; cstr_tags; style } in
  { ci_ind     = ind;
    ci_npar    = mib.mind_nparams;
    ci_cstr_ndecls = mip.mind_consnrealdecls;
    ci_cstr_nargs = mip.mind_consnrealargs;
    ci_pp_info = print_info }

(*s Useful functions *)

type constructor_summary = {
  cs_cstr : pconstructor;
  cs_params : constr list;
  cs_nargs : int;
  cs_args : Constr.rel_context;
  cs_concl_realargs : constr array
}

let lift_constructor n cs = {
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
  let _,t = decompose_prod_n_decls (Context.Rel.length sign) t in
  let subst = subst_of_rel_context_instance_list sign params in
  substl subst t

let instantiate_constructor_params (_,u as cstru) (mib,_ as mind_specif) params =
  let typi = mis_nf_constructor_type cstru mind_specif in
  let ctx = Vars.subst_instance_context u mib.mind_params_ctxt in
  instantiate_params typi params ctx

let get_constructor ((ind,u),mib,mip,params) j =
  assert (j <= Array.length mip.mind_consnames);
  let typi = instantiate_constructor_params ((ind,j),u) (mib,mip) params in
  let (args,ccl) = decompose_prod_decls typi in
  let (_,allargs) = decompose_app_list ccl in
  let vargs = List.skipn (List.length params) allargs in
  { cs_cstr = (ith_constructor_of_inductive ind j,u);
    cs_params = params;
    cs_nargs = Context.Rel.length args;
    cs_args = args;
    cs_concl_realargs = Array.of_list vargs }

let get_constructors env (ind,params) =
  let (mib,mip) = Inductive.lookup_mind_specif env (fst ind) in
  Array.init (Array.length mip.mind_consnames)
    (fun j -> get_constructor (ind,mib,mip,params) (j+1))

let get_projections = Environ.get_projections

let make_case_invert env (IndType (((ind,u),params),indices)) ~case_relevance:r ci =
  if Typeops.should_invert_case env r ci
  then CaseInvert {indices=Array.of_list indices}
  else NoInvert

let make_project env sigma ind pred c branches ps =
  let open EConstr in
  assert(Array.length branches == 1);
  let na, ty, t = destLambda sigma pred in
  let mib, mip as specif = Inductive.lookup_mind_specif env ind in
  let () =
    if (* dependent *) not (Vars.noccurn sigma 1 t) &&
         not (has_dependent_elim specif) then
      user_err
        Pp.(str"Dependent case analysis not allowed" ++
              str" on inductive type " ++ Termops.pr_global_env env (IndRef ind) ++ str ".")
  in
  let branch = branches.(0) in
  let ctx, br = decompose_lambda_n_decls sigma mip.mind_consnrealdecls.(0) branch in
  let _, u = destInd sigma (fst (decompose_app sigma ty)) in
  let u = Unsafe.to_instance u in
  let mkProj i c =
    let p, r = ps.(i) in
    let r = UVars.subst_instance_relevance u r in
    mkProj (Projection.make p true, r, c)
  in
  let proj = match EConstr.destRel sigma br with
    | exception DestKO -> None
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
  mkLetIn (na, c, ty, it_mkLambda_or_LetIn (Vars.liftn 1 (Array.length ps + 1) br) ctx)

let simple_make_case_or_project env sigma ci pred invert c branches =
  let open EConstr in
  let ind = ci.ci_ind in
  let projs = get_projections env ind in
  match projs with
  | None -> mkCase (EConstr.contract_case env sigma (ci, pred, invert, c, branches))
  | Some ps -> make_project env sigma ind (fst pred) c branches ps

let make_case_or_project env sigma indt ci pred c branches =
  let open EConstr in
  let IndType (((ind,_),_),_) = indt in
  let projs = get_projections env ind in
  match projs with
  | None ->
     let invert = make_case_invert env indt ~case_relevance:(snd pred) ci in
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
    let nparams = List.length params in
    if Int.equal nparams mib.mind_nparams then
      Inductive.inductive_paramdecls (mib,u)
    else begin
      assert (Int.equal nparams mib.mind_nparams_rec);
      snd (Inductive.inductive_nonrec_rec_paramdecls (mib,u))
    end in
  let arproperlength = List.length mip.mind_arity_ctxt - List.length parsign in
  let arsign,_ = List.chop arproperlength mip.mind_arity_ctxt in
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
  let r = Inductive.relevance_of_inductive env ind in
  let anon = make_annot Anonymous r in
  let arsign = List.map (fun d -> Termops.map_rel_decl EConstr.of_constr d) arsign in
  if dep then
    (* We need names everywhere *)
    Namegen.name_context env sigma
      ((LocalAssum (anon,EConstr.of_constr (build_dependent_inductive env indf)))::arsign)
      (* Costly: would be better to name once for all at definition time *)
  else
    (* No need to enforce names *)
    arsign

let make_arity env sigma dep indf s =
  let open EConstr in
  it_mkProd_or_LetIn (mkSort s) (make_arity_signature env sigma dep indf)

(**************************************************)

(** From a rel context describing the constructor arguments,
    build an expansion function.
    The term built is expecting to be substituted first by
    a substitution of the form [params, x : ind params] *)
let compute_projections env (kn, i as ind) =
  let open Term in
  let mib = Environ.lookup_mind kn env in
  let u = UVars.make_abstract_instance (Declareops.inductive_polymorphic_context mib) in
  let x = match mib.mind_record with
  | NotRecord | FakeRecord ->
    anomaly Pp.(str "Trying to build primitive projections for a non-primitive record")
  | PrimRecord info ->
    let id, _, _, _ = info.(i) in
    make_annot (Name id) mib.mind_packets.(i).mind_relevance
  in
  let pkt = mib.mind_packets.(i) in
  let { mind_nparams = nparamargs; mind_params_ctxt = params } = mib in
  let ctx, _ = pkt.mind_nf_lc.(0) in
  let ctx, paramslet = List.chop pkt.mind_consnrealdecls.(0) ctx in
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
      | Name id ->
        let lab = Label.of_id id in
        let proj_relevant = na.binder_relevance in
        let kn = Projection.Repr.make ind ~proj_npars:mib.mind_nparams ~proj_arg lab in
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
        let l = List.map EConstr.Unsafe.to_constr l in
        let (par,rargs) = List.chop mib.mind_nparams l in
        let indu = (ind, EInstance.kind sigma u) in
        IndType((indu, par),List.map EConstr.of_constr rargs)
    | _ -> raise Not_found

let find_inductive env sigma c =
  let open EConstr in
  let (t, l) = decompose_app_list sigma (whd_all env sigma c) in
  match EConstr.kind sigma t with
    | Ind ind
        when (fst (Inductive.lookup_mind_specif env (fst ind))).mind_finite <> CoFinite ->
        let l = List.map EConstr.Unsafe.to_constr l in
        (ind, l)
    | _ -> raise Not_found

let find_coinductive env sigma c =
  let open EConstr in
  let (t, l) = decompose_app_list sigma (whd_all env sigma c) in
  match EConstr.kind sigma t with
    | Ind ind
        when (fst (Inductive.lookup_mind_specif env (fst ind))).mind_finite == CoFinite ->
        let l = List.map EConstr.Unsafe.to_constr l in
        (ind, l)
    | _ -> raise Not_found


(* Type of Case predicates *)
let arity_of_case_predicate env (ind,params) dep k =
  let arsign = get_arity env (ind,params) in
  let r = Inductive.relevance_of_inductive env ind in
  let mind = build_dependent_inductive env (ind,params) in
  let concl = if dep then mkArrow mind r (mkSort k) else mkSort k in
  Term.it_mkProd_or_LetIn concl arsign

(***********************************************)
(* Inferring the sort of parameters of a polymorphic inductive type
   knowing the sort of the conclusion *)

let univ_level_mem l s = match s with
| Prop | Set | SProp -> false
| Type u -> Univ.univ_level_mem l u
| QSort (_, u) -> assert false (* template cannot contain sort variables *)

(* Compute the inductive argument types: replace the sorts
   that appear in the type of the inductive by the sort of the
   conclusion, and the other ones by fresh universes. *)
let rec instantiate_universes env evdref scl is = function
  | (LocalDef _ as d)::sign, exp ->
      d :: instantiate_universes env evdref scl is (sign, exp)
  | d::sign, None::exp ->
      d :: instantiate_universes env evdref scl is (sign, exp)
  | (LocalAssum (na,ty))::sign, Some l::exp ->
      let ctx,_ = Reduction.dest_arity env ty in
      let u = Univ.Universe.make l in
      let s =
        (* Does the sort of parameter [u] appear in (or equal)
           the sort of inductive [is] ? *)
        if univ_level_mem l is then
          scl (* constrained sort: replace by scl *)
        else
          (* unconstrained sort: replace by fresh universe *)
          let evm, s = Evd.new_sort_variable Evd.univ_flexible !evdref in
          let evm = Evd.set_leq_sort env evm s (EConstr.ESorts.make (Sorts.sort_of_univ u)) in
            evdref := evm; s
      in
      let s = EConstr.ESorts.kind !evdref s in
      (LocalAssum (na,mkArity(ctx,s))) :: instantiate_universes env evdref scl is (sign, exp)
  | sign, [] -> sign (* Uniform parameters are exhausted *)
  | [], _ -> assert false

let type_of_inductive_knowing_conclusion env sigma ((mib,mip),u) conclty =
  match mip.mind_arity with
  | RegularArity s -> sigma, EConstr.of_constr (subst_instance_constr u s.mind_user_arity)
  | TemplateArity ar ->
    let templ = match mib.mind_template with
    | None -> assert false
    | Some t -> t
    in
    let _,scl = splay_arity env sigma conclty in
    let ctx = List.rev mip.mind_arity_ctxt in
    let evdref = ref sigma in
    let ctx =
      instantiate_universes
        env evdref scl ar.template_level (ctx,templ.template_param_levels) in
    let scl = EConstr.ESorts.kind !evdref scl in
      !evdref, EConstr.of_constr (mkArity (List.rev ctx,scl))

let type_of_projection_constant env (p,u) =
  let _, pty = lookup_projection p env in
  Vars.subst_instance_constr u pty

let type_of_projection_knowing_arg env sigma p c ty =
  let c = EConstr.Unsafe.to_constr c in
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
  let c = Evarutil.nf_evar sigma c in
  let check_fix_cofix e c =
    (* [c] has already been normalized upfront *)
    let c = EConstr.Unsafe.to_constr c in
    match kind c with
    | CoFix (_,(_,_,_) as cofix) ->
      Inductive.check_cofix e cofix
    | Fix fix ->
      Inductive.check_fix e fix
    | _ -> ()
  in
  let rec iter env c =
    check_fix_cofix env c;
    EConstr.iter_with_full_binders env sigma EConstr.push_rel iter env c
  in
  try iter env c
  with Type_errors.TypeError (env, e) ->
    raise (Pretype_errors.PretypeError (env, sigma, TypingError (Type_errors.map_ptype_error EConstr.of_constr e)))
