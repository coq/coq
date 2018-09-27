(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
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
let dest_ind_family (mis,params) : inductive_family = (mis,params)

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

let projection_nparams_env _ p = Projection.npars p

let projection_nparams p = Projection.npars p

let has_dependent_elim mib =
  match mib.mind_record with
  | PrimRecord _ -> mib.mind_finite == BiFinite
  | NotRecord | FakeRecord -> true

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
  cs_args : Constr.rel_context;
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

let get_projections = Environ.get_projections

let make_case_or_project env sigma indf ci pred c branches =
  let open EConstr in
  let projs = get_projections env (fst (fst indf)) in
  match projs with
  | None -> (mkCase (ci, pred, c, branches))
  | Some ps ->
     assert(Array.length branches == 1);
     let na, ty, t = destLambda sigma pred in
     let () =
       let (ind, _), _ = dest_ind_family indf in
       let mib, _ = Inductive.lookup_mind_specif env ind in
       if (* dependent *) not (Vars.noccurn sigma 1 t) &&
          not (has_dependent_elim mib) then
       user_err ~hdr:"make_case_or_project"
                    Pp.(str"Dependent case analysis not allowed" ++
                     str" on inductive type " ++ Termops.Internal.print_constr_env env sigma (mkInd ind))
     in
     let branch = branches.(0) in
     let ctx, br = decompose_lam_n_assum sigma (Array.length ps) branch in
     let n, len, ctx =
       List.fold_right
         (fun decl (i, j, ctx) ->
          match decl with
          | LocalAssum (na, ty) ->
             let t = mkProj (Projection.make ps.(i) true, mkRel j) in
             (i + 1, j + 1, LocalDef (na, t, Vars.liftn 1 j ty) :: ctx)
          | LocalDef (na, b, ty) ->
             (i, j + 1, LocalDef (na, Vars.liftn 1 j b, Vars.liftn 1 j ty) :: ctx))
         ctx (0, 1, [])
     in
     mkLetIn (na, c, ty, it_mkLambda_or_LetIn (Vars.liftn 1 (Array.length ps + 1) br) ctx)

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

(** From a rel context describing the constructor arguments,
    build an expansion function.
    The term built is expecting to be substituted first by
    a substitution of the form [params, x : ind params] *)
let compute_projections env (kn, i as ind) =
  let open Term in
  let mib = Environ.lookup_mind kn env in
  let u = match mib.mind_universes with
  | Monomorphic_ind _ -> Instance.empty
  | Polymorphic_ind auctx -> make_abstract_instance auctx
  | Cumulative_ind acumi ->
    make_abstract_instance (ACumulativityInfo.univ_context acumi)
  in
  let x = match mib.mind_record with
  | NotRecord | FakeRecord ->
    anomaly Pp.(str "Trying to build primitive projections for a non-primitive record")
  | PrimRecord info-> Name (pi1 (info.(i)))
  in
  let pkt = mib.mind_packets.(i) in
  let { mind_nparams = nparamargs; mind_params_ctxt = params } = mib in
  let subst = List.init mib.mind_ntypes (fun i -> mkIndU ((kn, mib.mind_ntypes - i - 1), u)) in
  let rctx, _ = decompose_prod_assum (substl subst pkt.mind_nf_lc.(0)) in
  let ctx, paramslet = List.chop pkt.mind_consnrealdecls.(0) rctx in
  (** We build a substitution smashing the lets in the record parameters so
      that typechecking projections requires just a substitution and not
      matching with a parameter context. *)
  let indty =
    (* [ty] = [Ind inst] is typed in context [params] *)
    let inst = Context.Rel.to_extended_vect mkRel 0 paramslet in
    let indu = mkIndU (ind, u) in
    let ty = mkApp (indu, inst) in
    (* [Ind inst] is typed in context [params-wo-let] *)
    ty
  in
  let ci =
    let print_info =
      { ind_tags = []; cstr_tags = [|Context.Rel.to_tags ctx|]; style = LetStyle } in
      { ci_ind     = ind;
        ci_npar    = nparamargs;
        ci_cstr_ndecls = pkt.mind_consnrealdecls;
        ci_cstr_nargs = pkt.mind_consnrealargs;
        ci_pp_info = print_info }
  in
  let len = List.length ctx in
  let compat_body ccl i =
    (* [ccl] is defined in context [params;x:indty] *)
    (* [ccl'] is defined in context [params;x:indty;x:indty] *)
    let ccl' = liftn 1 2 ccl in
    let p = mkLambda (x, lift 1 indty, ccl') in
    let branch = it_mkLambda_or_LetIn (mkRel (len - i)) ctx in
    let body = mkCase (ci, p, mkRel 1, [|lift 1 branch|]) in
      it_mkLambda_or_LetIn (mkLambda (x,indty,body)) params
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
      match na with
      | Name id ->
        let lab = Label.of_id id in
        let kn = Projection.Repr.make ind ~proj_npars:mib.mind_nparams ~proj_arg lab in
        (* from [params, field1,..,fieldj |- t(params,field1,..,fieldj)]
           to [params, x:I, field1,..,fieldj |- t(params,field1,..,fieldj] *)
        let t = liftn 1 j t in
        (* from [params, x:I, field1,..,fieldj |- t(params,field1,..,fieldj)]
           to [params-wo-let, x:I |- t(params,proj1 x,..,projj x)] *)
        (* from [params, x:I, field1,..,fieldj |- t(field1,..,fieldj)]
           to [params, x:I |- t(proj1 x,..,projj x)] *)
        let ty = substl subst t in
        let term = mkProj (Projection.make kn true, mkRel 1) in
        let fterm = mkProj (Projection.make kn false, mkRel 1) in
        let compat = compat_body ty (j - 1) in
        let etab = it_mkLambda_or_LetIn (mkLambda (x, indty, term)) params in
        let etat = it_mkProd_or_LetIn (mkProd (x, indty, ty)) params in
        let body = (etab, etat, compat) in
        (proj_arg + 1, j + 1, body :: pbs, fterm :: subst)
      | Anonymous ->
        anomaly Pp.(str "Trying to build primitive projections for a non-primitive record")
  in
  let (_, _, pbs, subst) =
    List.fold_right projections ctx (0, 1, [], [])
  in
  Array.rev_of_list pbs

let legacy_match_projection env ind =
  Array.map pi3 (compute_projections env ind)

let compute_projections ind mib =
  let ans = compute_projections ind mib in
  Array.map (fun (prj, ty, _) -> (prj, ty)) ans

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
        when (fst (Inductive.lookup_mind_specif env (fst ind))).mind_finite <> CoFinite ->
        let l = List.map EConstr.Unsafe.to_constr l in
        (ind, l)
    | _ -> raise Not_found

let find_coinductive env sigma c =
  let open EConstr in
  let (t, l) = decompose_app sigma (whd_all env sigma c) in
  match EConstr.kind sigma t with
    | Ind ind
        when (fst (Inductive.lookup_mind_specif env (fst ind))).mind_finite == CoFinite ->
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

          From Coq > 8.2, using or not the effective dependency of
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

let type_of_projection_constant env (p,u) =
  let pty = lookup_projection p env in
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
  let check_fix_cofix e c =
    match kind (EConstr.to_constr sigma c) with
    | CoFix (_,(_,_,_) as cofix) ->
      Inductive.check_cofix e cofix
    | Fix (_,(_,_,_) as fix) ->
      Inductive.check_fix e fix
    | _ -> ()
  in
  let rec iter env c =
    check_fix_cofix env c;
    iter_constr_with_full_binders sigma EConstr.push_rel iter env c
  in
  iter env c
