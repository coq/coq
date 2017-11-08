(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open CErrors
open Util
open Names
open Univ
open Term
open Constr
open Vars
open Termops
open Declarations
open Declareops
open Environ
open Reductionops
open Context.Rel.Declaration

(* The following three functions are similar to the ones defined in
   Inductive, but they expect an env *)

let type_of_inductive env (ind,u) =
 let (mib,_ as specif) = Inductive.lookup_mind_specif env ind in
 Typeops.check_hyps_inclusion env mkInd ind mib.mind_hyps;
 Inductive.type_of_inductive env (specif,u)

(* Return type as quoted by the user *)
let type_of_constructor env (cstr,u) =
 let (mib,_ as specif) =
   Inductive.lookup_mind_specif env (inductive_of_constructor cstr) in
 Typeops.check_hyps_inclusion env mkConstruct cstr mib.mind_hyps;
 Inductive.type_of_constructor (cstr,u) specif

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
let dest_ind_family (mis,params) = (mis,params)

let map_ind_family f (mis,params) = (mis, List.map f params)

let liftn_inductive_family n d = map_ind_family (liftn n d)
let lift_inductive_family n = liftn_inductive_family n 1

let substnl_ind_family l n = map_ind_family (substnl l n)


type inductive_type = IndType of inductive_family * EConstr.constr list

let make_ind_type (indf, realargs) = IndType (indf,realargs)
let dest_ind_type (IndType (indf,realargs)) = (indf,realargs)

let map_inductive_type f (IndType (indf, realargs)) =
  let f' c = EConstr.Unsafe.to_constr (f (EConstr.of_constr c)) in
  IndType (map_ind_family f' indf, List.map f realargs)

let liftn_inductive_type n d = map_inductive_type (EConstr.Vars.liftn n d)
let lift_inductive_type n = liftn_inductive_type n 1

let substnl_ind_type l n = map_inductive_type (EConstr.Vars.substnl l n)

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
	  | Mrec (_,i) -> Int.List.mem i listind
          | _ -> false) rvec
  in
  Array.exists one_is_rec (dest_subterms rarg)

let mis_is_recursive (ind,mib,mip) =
  mis_is_recursive_subset (List.interval 0 (mib.mind_ntypes - 1))
    mip.mind_recargs

let mis_nf_constructor_type ((ind,u),mib,mip) j =
  let specif = mip.mind_nf_lc
  and ntypes = mib.mind_ntypes
  and nconstr = Array.length mip.mind_consnames in
  let make_Ik k = mkIndU (((fst ind),ntypes-k-1),u) in
  if j > nconstr then user_err Pp.(str "Not enough constructors in the type.");
    substl (List.init ntypes make_Ik) (subst_instance_constr u specif.(j-1))

(* Number of constructors *)

let nconstructors ind =
  let (_,mip) = Global.lookup_inductive ind in
  Array.length mip.mind_consnames

let nconstructors_env env ind =
  let (_,mip) = Inductive.lookup_mind_specif env ind in
  Array.length mip.mind_consnames

(* Arity of constructors excluding parameters, excluding local defs *)

let constructors_nrealargs ind =
  let (_,mip) = Global.lookup_inductive ind in
  mip.mind_consnrealargs

let constructors_nrealargs_env env ind =
  let (_,mip) = Inductive.lookup_mind_specif env ind in
  mip.mind_consnrealargs

(* Arity of constructors excluding parameters, including local defs *)

let constructors_nrealdecls ind =
  let (_,mip) = Global.lookup_inductive ind in
  mip.mind_consnrealdecls

let constructors_nrealdecls_env env ind =
  let (_,mip) = Inductive.lookup_mind_specif env ind in
  mip.mind_consnrealdecls

(* Arity of constructors including parameters, excluding local defs *)

let constructor_nallargs (indsp,j) =
  let (mib,mip) = Global.lookup_inductive indsp in
  mip.mind_consnrealargs.(j-1) + mib.mind_nparams

let constructor_nallargs_env env ((kn,i),j) =
  let mib = Environ.lookup_mind kn env in
  let mip = mib.mind_packets.(i) in
  mip.mind_consnrealargs.(j-1) + mib.mind_nparams

(* Arity of constructors including params, including local defs *)

let constructor_nalldecls (indsp,j) = (* TOCHANGE en decls *)
  let (mib,mip) = Global.lookup_inductive indsp in
  mip.mind_consnrealdecls.(j-1) + Context.Rel.length (mib.mind_params_ctxt)

let constructor_nalldecls_env env ((kn,i),j) = (* TOCHANGE en decls *)
  let mib = Environ.lookup_mind kn env in
  let mip = mib.mind_packets.(i) in
  mip.mind_consnrealdecls.(j-1) + Context.Rel.length (mib.mind_params_ctxt)

(* Arity of constructors excluding params, excluding local defs *)

let constructor_nrealargs (ind,j) =
  let (_,mip) = Global.lookup_inductive ind in
  mip.mind_consnrealargs.(j-1)

let constructor_nrealargs_env env (ind,j) =
  let (_,mip) = Inductive.lookup_mind_specif env ind in
  mip.mind_consnrealargs.(j-1)

(* Arity of constructors excluding params, including local defs *)

let constructor_nrealdecls (ind,j) = (* TOCHANGE en decls *)
  let (_,mip) = Global.lookup_inductive ind in
  mip.mind_consnrealdecls.(j-1)

let constructor_nrealdecls_env env (ind,j) = (* TOCHANGE en decls *)
  let (_,mip) = Inductive.lookup_mind_specif env ind in
  mip.mind_consnrealdecls.(j-1)

(* Length of arity, excluding params, excluding local defs *)

let inductive_nrealargs ind =
  let (_,mip) = Global.lookup_inductive ind in
  mip.mind_nrealargs

let inductive_nrealargs_env env ind =
  let (_,mip) = Inductive.lookup_mind_specif env ind in
  mip.mind_nrealargs

(* Length of arity, excluding params, including local defs *)

let inductive_nrealdecls ind =
  let (_,mip) = Global.lookup_inductive ind in
  mip.mind_nrealdecls

let inductive_nrealdecls_env env ind =
  let (_,mip) = Inductive.lookup_mind_specif env ind in
  mip.mind_nrealdecls

(* Full length of arity (w/o local defs) *)

let inductive_nallargs ind =
  let (mib,mip) = Global.lookup_inductive ind in
  mib.mind_nparams + mip.mind_nrealargs

let inductive_nallargs_env env ind =
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
  mib.mind_nparams + mip.mind_nrealargs

(* Length of arity (w/o local defs) *)

let inductive_nparams ind =
  let (mib,mip) = Global.lookup_inductive ind in
  mib.mind_nparams

let inductive_nparams_env env ind =
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
  mib.mind_nparams

(* Length of arity (with local defs) *)

let inductive_nparamdecls ind =
  let (mib,mip) = Global.lookup_inductive ind in
  Context.Rel.length mib.mind_params_ctxt

let inductive_nparamdecls_env env ind =
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
  Context.Rel.length mib.mind_params_ctxt

(* Full length of arity (with local defs) *)

let inductive_nalldecls ind =
  let (mib,mip) = Global.lookup_inductive ind in
  Context.Rel.length (mib.mind_params_ctxt) + mip.mind_nrealdecls

let inductive_nalldecls_env env ind =
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
  Context.Rel.length (mib.mind_params_ctxt) + mip.mind_nrealdecls

(* Others *)

let inductive_paramdecls (ind,u) =
  let (mib,mip) = Global.lookup_inductive ind in
    Inductive.inductive_paramdecls (mib,u)

let inductive_paramdecls_env env (ind,u) =
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
    Inductive.inductive_paramdecls (mib,u)

let inductive_alldecls (ind,u) =
  let (mib,mip) = Global.lookup_inductive ind in
    Vars.subst_instance_context u mip.mind_arity_ctxt

let inductive_alldecls_env env (ind,u) =
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
    Vars.subst_instance_context u mip.mind_arity_ctxt

let constructor_has_local_defs (indsp,j) =
  let (mib,mip) = Global.lookup_inductive indsp in
  let l1 = mip.mind_consnrealdecls.(j-1) + Context.Rel.length (mib.mind_params_ctxt) in
  let l2 = recarg_length mip.mind_recargs j + mib.mind_nparams in
  not (Int.equal l1 l2)

let inductive_has_local_defs ind =
  let (mib,mip) = Global.lookup_inductive ind in
  let l1 = Context.Rel.length (mib.mind_params_ctxt) + mip.mind_nrealdecls in
  let l2 = mib.mind_nparams + mip.mind_nrealargs in
  not (Int.equal l1 l2)

let allowed_sorts env (kn,i as ind) =
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
  mip.mind_kelim

let projection_nparams_env env p = 
  let pb = lookup_projection p env in
    pb.proj_npars

let projection_nparams p = projection_nparams_env (Global.env ()) p

let has_dependent_elim mib =
  match mib.mind_record with
  | Some (Some _) -> mib.mind_finite == Decl_kinds.BiFinite
  | _ -> true

(* Annotation for cases *)
let make_case_info env ind style =
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
  let ind_tags =
    Context.Rel.to_tags (List.firstn mip.mind_nrealdecls mip.mind_arity_ctxt) in
  let cstr_tags =
    Array.map2 (fun c n ->
      let d,_ = decompose_prod_assum c in
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
  cs_args : Context.Rel.t;
  cs_concl_realargs : constr array
}

let lift_constructor n cs = {
  cs_cstr = cs.cs_cstr;
  cs_params = List.map (lift n) cs.cs_params;
  cs_nargs = cs.cs_nargs;
  cs_args = lift_rel_context n cs.cs_args;
  cs_concl_realargs = Array.map (liftn n (cs.cs_nargs+1)) cs.cs_concl_realargs
}

(* Accept either all parameters or only recursively uniform ones *)
let instantiate_params t params sign =
  let nnonrecpar = Context.Rel.nhyps sign - List.length params in
  (* Adjust the signature if recursively non-uniform parameters are not here *)
  let _,sign = context_chop nnonrecpar sign in
  let _,t = decompose_prod_n_assum (Context.Rel.length sign) t in
  let subst = subst_of_rel_context_instance sign params in
  substl subst t

let get_constructor ((ind,u as indu),mib,mip,params) j =
  assert (j <= Array.length mip.mind_consnames);
  let typi = mis_nf_constructor_type (indu,mib,mip) j in
  let ctx = Vars.subst_instance_context u mib.mind_params_ctxt in
  let typi = instantiate_params typi params ctx in
  let (args,ccl) = decompose_prod_assum typi in
  let (_,allargs) = decompose_app ccl in
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

let get_projections env (ind,params) =
  let (mib,mip) = Inductive.lookup_mind_specif env (fst ind) in
    match mib.mind_record with
    | Some (Some (id, projs, pbs)) -> Some projs
    | _ -> None

let make_case_or_project env sigma indf ci pred c branches =
  let open EConstr in
  let projs = get_projections env indf in
  match projs with
  | None -> (mkCase (ci, pred, c, branches))
  | Some ps ->
     assert(Array.length branches == 1);
     let () =
       let _, _, t = destLambda sigma pred in
       let (ind, _), _ = dest_ind_family indf in
       let mib, _ = Inductive.lookup_mind_specif env ind in
       if (* dependent *) not (Vars.noccurn sigma 1 t) &&
          not (has_dependent_elim mib) then
       user_err ~hdr:"make_case_or_project"
		    Pp.(str"Dependent case analysis not allowed" ++
		     str" on inductive type " ++ Names.MutInd.print (fst ind))
     in
     let branch = branches.(0) in
     let ctx, br = decompose_lam_n_assum sigma (Array.length ps) branch in
     let n, subst =
       List.fold_right
         (fun decl (i, subst) ->
	  match decl with
	  | LocalAssum (na, t) ->
	     let t = mkProj (Projection.make ps.(i) true, c) in
	     (i + 1, t :: subst)
	  | LocalDef (na, b, t) -> (i, Vars.substl subst b :: subst))
	 ctx (0, [])
     in Vars.substl subst br

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
      mib.mind_params_ctxt
    else begin
      assert (Int.equal nparams mib.mind_nparams_rec);
      let nnonrecparamdecls = mib.mind_nparams - mib.mind_nparams_rec in
      snd (Termops.context_chop nnonrecparamdecls mib.mind_params_ctxt)
    end in
  let parsign = Vars.subst_instance_context u parsign in
  let arproperlength = List.length mip.mind_arity_ctxt - List.length parsign in
  let arsign,_ = List.chop arproperlength mip.mind_arity_ctxt in
  let subst = subst_of_rel_context_instance parsign params in
  let arsign = Vars.subst_instance_context u arsign in
  (substl_rel_context subst arsign, Inductive.inductive_sort_family mip)

(* Functions to build standard types related to inductive *)
let build_dependent_constructor cs =
  applist
    (mkConstructU cs.cs_cstr,
     (List.map (lift cs.cs_nargs) cs.cs_params)
      @(Context.Rel.to_extended_list mkRel 0 cs.cs_args))

let build_dependent_inductive env ((ind, params) as indf) =
  let arsign,_ = get_arity env indf in
  let nrealargs = List.length arsign in
  applist
    (mkIndU ind,
     (List.map (lift nrealargs) params)@(Context.Rel.to_extended_list mkRel 0 arsign))

(* builds the arity of an elimination predicate in sort [s] *)

let make_arity_signature env sigma dep indf =
  let (arsign,_) = get_arity env indf in
  let arsign = List.map (fun d -> Termops.map_rel_decl EConstr.of_constr d) arsign in
  if dep then
    (* We need names everywhere *)
    Namegen.name_context env sigma
      ((LocalAssum (Anonymous,EConstr.of_constr (build_dependent_inductive env indf)))::arsign)
      (* Costly: would be better to name once for all at definition time *)
  else
    (* No need to enforce names *)
    arsign

let make_arity env sigma dep indf s =
  let open EConstr in
  it_mkProd_or_LetIn (mkSort s) (make_arity_signature env sigma dep indf)

(* [p] is the predicate and [cs] a constructor summary *)
let build_branch_type env sigma dep p cs =
  let base = appvect (lift cs.cs_nargs p, cs.cs_concl_realargs) in
  if dep then
    EConstr.Unsafe.to_constr (Namegen.it_mkProd_or_LetIn_name env sigma
      (EConstr.of_constr (applist (base,[build_dependent_constructor cs])))
      (List.map (fun d -> Termops.map_rel_decl EConstr.of_constr d) cs.cs_args))
  else
    Term.it_mkProd_or_LetIn base cs.cs_args

(**************************************************)

let extract_mrectype sigma t =
  let open EConstr in
  let (t, l) = decompose_app sigma t in
  match EConstr.kind sigma t with
    | Ind ind -> (ind, l)
    | _ -> raise Not_found

let find_mrectype_vect env sigma c =
  let (t, l) = Termops.decompose_app_vect sigma (whd_all env sigma c) in
  match EConstr.kind sigma t with
    | Ind ind -> (ind, l)
    | _ -> raise Not_found

let find_mrectype env sigma c =
  let (ind, v) = find_mrectype_vect env sigma c in (ind, Array.to_list v)

let find_rectype env sigma c =
  let open EConstr in
  let (t, l) = decompose_app sigma (whd_all env sigma c) in
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
  let (t, l) = decompose_app sigma (whd_all env sigma c) in
  match EConstr.kind sigma t with
    | Ind ind
        when (fst (Inductive.lookup_mind_specif env (fst ind))).mind_finite <> Decl_kinds.CoFinite ->
        let l = List.map EConstr.Unsafe.to_constr l in
        (ind, l)
    | _ -> raise Not_found

let find_coinductive env sigma c =
  let open EConstr in
  let (t, l) = decompose_app sigma (whd_all env sigma c) in
  match EConstr.kind sigma t with
    | Ind ind
        when (fst (Inductive.lookup_mind_specif env (fst ind))).mind_finite == Decl_kinds.CoFinite ->
        let l = List.map EConstr.Unsafe.to_constr l in
        (ind, l)
    | _ -> raise Not_found


(***********************************************)
(* find appropriate names for pattern variables. Useful in the Case
   and Inversion (case_then_using et case_nodep_then_using) tactics. *)

let is_predicate_explicitly_dep env sigma pred arsign =
  let rec srec env pval arsign =
    let pv' = whd_all env sigma pval in
    match EConstr.kind sigma pv', arsign with
      | Lambda (na,t,b), (LocalAssum _)::arsign ->
	  srec (push_rel_assum (na, t) env) b arsign
      | Lambda (na,_,t), _ ->

       (* The following code has an impact on the introduction names
	  given by the tactics "case" and "inversion": when the
	  elimination is not dependent, "case" uses Anonymous for
	  inductive types in Prop and names created by mkProd_name for
	  inductive types in Set/Type while "inversion" uses anonymous
	  for inductive types both in Prop and Set/Type !!

	  Previously, whether names were created or not relied on
	  whether the predicate created in Indrec.make_case_com had a
	  dependent arity or not. To avoid different predicates
	  printed the same in v8, all predicates built in indrec.ml
	  got a dependent arity (Aug 2004). The new way to decide
	  whether names have to be created or not is to use an
	  Anonymous or Named variable to enforce the expected
	  dependency status (of course, Anonymous implies non
	  dependent, but not conversely).

          From Coq > 8.2, using or not the the effective dependency of
          the predicate is parametrable! *)

          begin match na with
          | Anonymous -> false
          | Name _ -> true
          end

      | _ -> anomaly (Pp.str "Non eta-expanded dep-expanded \"match\" predicate.")
  in
  srec env (EConstr.of_constr pred) arsign

let is_elim_predicate_explicitly_dependent env sigma pred indf =
  let arsign,_ = get_arity env indf in
  is_predicate_explicitly_dep env sigma pred arsign

let set_names env sigma n brty =
  let open EConstr in
  let (ctxt,cl) = decompose_prod_n_assum sigma n brty in
  EConstr.Unsafe.to_constr (Namegen.it_mkProd_or_LetIn_name env sigma cl ctxt)

let set_pattern_names env sigma ind brv =
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
  let arities =
    Array.map
      (fun c ->
        Context.Rel.length ((prod_assum c)) -
        mib.mind_nparams)
      mip.mind_nf_lc in
  Array.map2 (set_names env sigma) arities brv

let type_case_branches_with_names env sigma indspec p c =
  let (ind,args) = indspec in
  let args = List.map EConstr.Unsafe.to_constr args in
  let (mib,mip as specif) = Inductive.lookup_mind_specif env (fst ind) in
  let nparams = mib.mind_nparams in
  let (params,realargs) = List.chop nparams args in
  let lbrty = Inductive.build_branches_type ind specif params p in
  (* Build case type *)
  let conclty = lambda_appvect_assum (mip.mind_nrealdecls+1) p (Array.of_list (realargs@[c])) in
  (* Adjust names *)
  if is_elim_predicate_explicitly_dependent env sigma p (ind,params) then
    (set_pattern_names env sigma (fst ind) (Array.map EConstr.of_constr lbrty), conclty)
  else (lbrty, conclty)

(* Type of Case predicates *)
let arity_of_case_predicate env (ind,params) dep k =
  let arsign,_ = get_arity env (ind,params) in
  let mind = build_dependent_inductive env (ind,params) in
  let concl = if dep then mkArrow mind (mkSort k) else mkSort k in
  Term.it_mkProd_or_LetIn concl arsign

(***********************************************)
(* Inferring the sort of parameters of a polymorphic inductive type
   knowing the sort of the conclusion *)


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
	  let evm = Evd.set_leq_sort env evm s (Sorts.sort_of_univ u) in
	    evdref := evm; s
      in
      (LocalAssum (na,mkArity(ctx,s))) :: instantiate_universes env evdref scl is (sign, exp)
  | sign, [] -> sign (* Uniform parameters are exhausted *)
  | [], _ -> assert false

let type_of_inductive_knowing_conclusion env sigma ((mib,mip),u) conclty =
  match mip.mind_arity with
  | RegularArity s -> sigma, EConstr.of_constr (subst_instance_constr u s.mind_user_arity)
  | TemplateArity ar ->
    let _,scl = splay_arity env sigma conclty in
    let scl = EConstr.ESorts.kind sigma scl in
    let ctx = List.rev mip.mind_arity_ctxt in
    let evdref = ref sigma in
    let ctx =
      instantiate_universes
        env evdref scl ar.template_level (ctx,ar.template_param_levels) in
      !evdref, EConstr.of_constr (mkArity (List.rev ctx,scl))

let type_of_projection_knowing_arg env sigma p c ty =
  let c = EConstr.Unsafe.to_constr c in
  let IndType(pars,realargs) =
    try find_rectype env sigma ty
    with Not_found ->
      raise (Invalid_argument "type_of_projection_knowing_arg_type: not an inductive type")
  in
  let (_,u), pars = dest_ind_family pars in
  substl (c :: List.rev pars) (Typeops.type_of_projection_constant env (p,u))

(***********************************************)
(* Guard condition *)

(* A function which checks that a term well typed verifies both
   syntactic conditions *)

let control_only_guard env c =
  let check_fix_cofix e c = match kind c with
    | CoFix (_,(_,_,_) as cofix) ->
      Inductive.check_cofix e cofix
    | Fix (_,(_,_,_) as fix) ->
      Inductive.check_fix e fix
    | _ -> ()
  in
  let rec iter env c =
    check_fix_cofix env c;
    iter_constr_with_full_binders push_rel iter env c
  in
  iter env c

(* inference of subtyping condition for inductive types *)

let infer_inductive_subtyping_arity_constructor
    (env, evd, csts) (subst : constr -> constr) (arcn : types) is_arity (params : Context.Rel.t) =
  let numchecked = ref 0 in
  let numparams = Context.Rel.nhyps params in
  let update_contexts (env, evd, csts) csts' =
    (Environ.add_constraints csts' env, Evd.add_constraints evd csts', Univ.Constraint.union csts csts')
  in
  let basic_check (env, evd, csts) tp =
    let result =
      if !numchecked >= numparams then
        let csts' =
          Reduction.infer_conv_leq ~evars:(Evd.existential_opt_value evd) env (Evd.universes evd) tp (subst tp)
        in update_contexts (env, evd, csts) csts'
      else
        (env, evd, csts)
    in
    numchecked := !numchecked + 1; result
  in
  let infer_typ typ ctxs =
   match typ with
     | LocalAssum (_, typ') ->
       begin
         try
           let (env, evd, csts) = basic_check ctxs typ' in (Environ.push_rel typ env, evd, csts)
         with Reduction.NotConvertible -> 
           anomaly ~label:"inference of record/inductive subtyping relation failed"
             (Pp.str "Can't infer subtyping for record/inductive type")
       end
     | _ -> anomaly (Pp.str "")
  in
  let arcn' = Term.it_mkProd_or_LetIn arcn params in
  let typs, codom = Reduction.dest_prod env arcn' in
  let last_contexts = Context.Rel.fold_outside infer_typ typs ~init:(env, evd, csts) in
  if not is_arity then basic_check last_contexts codom else last_contexts

let infer_inductive_subtyping env evd mind_ent =
  let { Entries.mind_entry_params = params;
        Entries.mind_entry_inds = entries;
        Entries.mind_entry_universes = ground_univs;
      } = mind_ent
  in
  let uinfind =
    match ground_univs with
    | Entries.Monomorphic_ind_entry _
    | Entries.Polymorphic_ind_entry _ -> ground_univs
    | Entries.Cumulative_ind_entry cumi -> 
      begin
        let uctx = Univ.CumulativityInfo.univ_context cumi in
        let sbsubst = Univ.CumulativityInfo.subtyping_susbst cumi in
        let dosubst = subst_univs_level_constr sbsubst in
        let instance_other = 
          Univ.subst_univs_level_instance sbsubst (Univ.UContext.instance uctx) 
        in
        let constraints_other = 
          Univ.subst_univs_level_constraints
            sbsubst (Univ.UContext.constraints uctx) 
        in
        let uctx_other = Univ.UContext.make (instance_other, constraints_other) in
        let env = Environ.push_context uctx env in
        let env = Environ.push_context uctx_other env in
        let evd = 
          Evd.merge_universe_context
            evd (UState.of_context_set (Univ.ContextSet.of_context uctx_other)) 
        in
        let (_, _, subtyp_constraints) =
          List.fold_left
            (fun ctxs indentry ->
               let _, params = Typeops.infer_local_decls env params in
               let ctxs' = infer_inductive_subtyping_arity_constructor
                   ctxs dosubst indentry.Entries.mind_entry_arity true params
               in
               List.fold_left
                 (fun ctxs cons ->
                    infer_inductive_subtyping_arity_constructor
                      ctxs dosubst cons false params
                 )
                 ctxs' indentry.Entries.mind_entry_lc
            ) (env, evd, Univ.Constraint.empty) entries
        in 
        Entries.Cumulative_ind_entry
          (Univ.CumulativityInfo.make 
             (Univ.CumulativityInfo.univ_context cumi,
              Univ.UContext.make
                (Univ.UContext.instance (Univ.CumulativityInfo.subtyp_context cumi),
                 subtyp_constraints)))
      end
  in {mind_ent with Entries.mind_entry_universes = uinfind;}
