(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Util
open Names
open Univ
open Term
open Termops
open Sign
open Declarations
open Environ
open Reductionops

(* [inductive_family] = [inductive_instance] applied to global parameters *)
type inductive_family = inductive * constr list

let make_ind_family (mis, params) = (mis,params)
let dest_ind_family (mis,params) = (mis,params)

let map_ind_family f (mis,params) = (mis, List.map f params)

let liftn_inductive_family n d = map_ind_family (liftn n d)
let lift_inductive_family n = liftn_inductive_family n 1

let substnl_ind_family l n = map_ind_family (substnl l n)


type inductive_type = IndType of inductive_family * constr list

let make_ind_type (indf, realargs) = IndType (indf,realargs)
let dest_ind_type (IndType (indf,realargs)) = (indf,realargs)

let map_inductive_type f (IndType (indf, realargs)) =
  IndType (map_ind_family f indf, List.map f realargs)

let liftn_inductive_type n d = map_inductive_type (liftn n d)
let lift_inductive_type n = liftn_inductive_type n 1

let substnl_ind_type l n = map_inductive_type (substnl l n)

let mkAppliedInd (IndType ((ind,params), realargs)) =
  applist (mkInd ind,params@realargs)


(* Does not consider imbricated or mutually recursive types *) 
let mis_is_recursive_subset listind rarg = 
  let rec one_is_rec rvec = 
    List.exists
      (fun ra ->
        match dest_recarg ra with
	  | Mrec i -> List.mem i listind 
          | _ -> false) rvec
  in 
  array_exists one_is_rec (dest_subterms rarg)

let mis_is_recursive (ind,mib,mip) =
  mis_is_recursive_subset (interval 0 (mib.mind_ntypes-1))
    mip.mind_recargs

let mis_nf_constructor_type (ind,mib,mip) j =
  let specif = mip.mind_nf_lc
  and ntypes = mib.mind_ntypes
  and nconstr = Array.length mip.mind_consnames in
  let make_Ik k = mkInd ((fst ind),ntypes-k-1) in 
  if j > nconstr then error "Not enough constructors in the type";
  substl (list_tabulate make_Ik ntypes) specif.(j-1)

(* Arity of constructors excluding parameters and local defs *)
let mis_constr_nargs indsp =
  let (mib,mip) = Global.lookup_inductive indsp in
  let recargs = dest_subterms mip.mind_recargs in
  Array.map List.length recargs

let mis_constr_nargs_env env (kn,i) = 
  let mib = Environ.lookup_mind kn env in
  let mip = mib.mind_packets.(i) in 
  let recargs = dest_subterms mip.mind_recargs in
  Array.map List.length recargs

let mis_constructor_nargs_env env ((kn,i),j) =
  let mib = Environ.lookup_mind kn env in
  let mip = mib.mind_packets.(i) in 
  recarg_length mip.mind_recargs j + mip.mind_nparams

(* Annotation for cases *)
let make_case_info env ind style pats_source =
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
  let print_info =
    { ind_nargs = mip.mind_nrealargs;
      style     = style;
      source    = pats_source } in
  { ci_ind     = ind;
    ci_npar    = mip.mind_nparams;
    ci_pp_info = print_info }

let make_default_case_info env style ind =
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
  make_case_info env ind style
    (Array.map (fun _ -> RegularPat) mip.mind_consnames)

(*s Useful functions *)

type constructor_summary = {
  cs_cstr : constructor;
  cs_params : constr list;
  cs_nargs : int;
  cs_args : rel_context;
  cs_concl_realargs : constr array
}

let lift_constructor n cs = {
  cs_cstr = cs.cs_cstr;
  cs_params = List.map (lift n) cs.cs_params;
  cs_nargs = cs.cs_nargs;
  cs_args = lift_rel_context n cs.cs_args;
  cs_concl_realargs = Array.map (liftn n (cs.cs_nargs+1)) cs.cs_concl_realargs
}

let instantiate_params t args sign =
  let rec inst s t = function
    | ((_,None,_)::ctxt,a::args) ->
	(match kind_of_term t with
	   | Prod(_,_,t) -> inst (a::s) t (ctxt,args)
	   | _ -> anomaly"instantiate_params: type, ctxt and args mismatch")
    | ((_,(Some b),_)::ctxt,args) -> 
	(match kind_of_term t with
	   | LetIn(_,_,_,t) -> inst ((substl s b)::s) t (ctxt,args)
	   | _ -> anomaly"instantiate_params: type, ctxt and args mismatch")
    | [], [] -> substl s t
    | _ -> anomaly"instantiate_params: type, ctxt and args mismatch"
  in inst [] t (List.rev sign,args)

let get_constructor (ind,mib,mip,params) j =
  assert (j <= Array.length mip.mind_consnames);
  let typi = mis_nf_constructor_type (ind,mib,mip) j in
  let typi = instantiate_params typi params mip.mind_params_ctxt in
  let (args,ccl) = decompose_prod_assum typi in
  let (_,allargs) = decompose_app ccl in
  let vargs = list_skipn mip.mind_nparams allargs in
  { cs_cstr = ith_constructor_of_inductive ind j;
    cs_params = params;
    cs_nargs = rel_context_length args;
    cs_args = args;
    cs_concl_realargs = Array.of_list vargs }

let get_constructors env (ind,params) =
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
  Array.init (Array.length mip.mind_consnames)
    (fun j -> get_constructor (ind,mib,mip,params) (j+1))

let rec instantiate args c = match kind_of_term c, args with
  | Prod (_,_,c), a::args -> instantiate args (subst1 a c)
  | LetIn (_,b,_,c), args -> instantiate args (subst1 b c)
  | _, [] -> c
  | _ -> anomaly "too short arity"

let get_arity env (ind,params) =
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
  let arity = mip.mind_nf_arity in
  destArity (instantiate params arity)

(* Functions to build standard types related to inductive *)
let build_dependent_constructor cs =
  applist
    (mkConstruct cs.cs_cstr,
     (List.map (lift cs.cs_nargs) cs.cs_params)
      @(extended_rel_list 0 cs.cs_args))

let build_dependent_inductive env ((ind, params) as indf) =
  let arsign,_ = get_arity env indf in
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
  let nrealargs = mip.mind_nrealargs in
  applist 
    (mkInd ind,
     (List.map (lift nrealargs) params)@(extended_rel_list 0 arsign))

(* builds the arity of an elimination predicate in sort [s] *)

let make_arity_signature env dep indf =
  let (arsign,_) = get_arity env indf in
  if dep then
    (* We need names everywhere *)
    name_context env
      ((Anonymous,None,build_dependent_inductive env indf)::arsign)
      (* Costly: would be better to name one for all at definition time *)
  else
    (* No need to enforce names *)
    arsign

let make_arity env dep indf s = mkArity (make_arity_signature env dep indf, s)

(* [p] is the predicate and [cs] a constructor summary *)
let build_branch_type env dep p cs =
  let base = appvect (lift cs.cs_nargs p, cs.cs_concl_realargs) in
  if dep then
    it_mkProd_or_LetIn_name env
      (applist (base,[build_dependent_constructor cs]))
      cs.cs_args
  else
    it_mkProd_or_LetIn base cs.cs_args

(**************************************************)

let extract_mrectype t =
  let (t, l) = decompose_app t in
  match kind_of_term t with
    | Ind ind -> (ind, l)
    | _ -> raise Not_found

let find_mrectype env sigma c =
  let (t, l) = decompose_app (whd_betadeltaiota env sigma c) in
  match kind_of_term t with
    | Ind ind -> (ind, l)
    | _ -> raise Not_found

let find_rectype env sigma c =
  let (t, l) = decompose_app (whd_betadeltaiota env sigma c) in
  match kind_of_term t with
    | Ind ind ->
        let (mib,mip) = Inductive.lookup_mind_specif env ind in
        let (par,rargs) = list_chop mip.mind_nparams l in
        IndType((ind, par),rargs)
    | _ -> raise Not_found

let find_inductive env sigma c =
  let (t, l) = decompose_app (whd_betadeltaiota env sigma c) in
  match kind_of_term t with
    | Ind ind
        when (fst (Inductive.lookup_mind_specif env ind)).mind_finite ->
        (ind, l)
    | _ -> raise Not_found

let find_coinductive env sigma c =
  let (t, l) = decompose_app (whd_betadeltaiota env sigma c) in
  match kind_of_term t with
    | Ind ind
        when not (fst (Inductive.lookup_mind_specif env ind)).mind_finite ->
        (ind, l)
    | _ -> raise Not_found


(***********************************************)
(* find appropriate names for pattern variables. Useful in the
   Case tactic. *)

let is_dep_predicate env kelim pred nodep_ar = 
  let rec srec env pval pt nodep_ar =
    let pt' = whd_betadeltaiota env Evd.empty pt in
    let pv' = whd_betadeltaiota env Evd.empty pval in
    match kind_of_term pv', kind_of_term pt', kind_of_term nodep_ar with
      | Lambda (na,t,b), Prod (_,_,a), Prod (_,_,a') ->
	  srec (push_rel_assum (na,t) env) b a a'
      | _,              Prod (na,t,a), Prod (_,_,a') ->
	  srec (push_rel_assum (na,t) env) (lift 1 pv') a a'
      | Lambda (_,_,b), Prod (_,_,_), _ -> (*dependent (mkRel 1) b*) true
      | _, Prod (_,_,_), _ -> true
      | _ -> false in 
  srec env pred.uj_val pred.uj_type nodep_ar

let is_dependent_elimination_predicate env pred indf =
  let (ind,params) = indf in
  let (_,mip) = Inductive.lookup_mind_specif env ind in
  let kelim = mip.mind_kelim in
  let arsign,s = get_arity env indf in
  let glob_t = it_mkProd_or_LetIn (mkSort s) arsign in
  is_dep_predicate env kelim pred glob_t

let is_dep_arity env kelim predty nodep_ar = 
  let rec srec pt nodep_ar =
    let pt' = whd_betadeltaiota env Evd.empty pt in
    match kind_of_term pt', kind_of_term nodep_ar with
      | Prod (_,a1,a2), Prod (_,a1',a2') -> srec a2 a2'
      | Prod (_,a1,a2), _ -> true
      | _ -> false in 
  srec predty nodep_ar

let is_dependent_elimination env predty indf =
  let (ind,params) = indf in
  let (_,mip) = Inductive.lookup_mind_specif env ind in
  let kelim = mip.mind_kelim in
  let arsign,s = get_arity env indf in
  let glob_t = it_mkProd_or_LetIn (mkSort s) arsign in
  is_dep_arity env kelim predty glob_t

let set_names env n brty =
  let (ctxt,cl) = decompose_prod_n_assum n brty in
  it_mkProd_or_LetIn_name env cl ctxt

let set_pattern_names env ind brv =
  let (_,mip) = Inductive.lookup_mind_specif env ind in
  let arities =
    Array.map
      (fun c ->
        rel_context_length (fst (decompose_prod_assum c)) -
        mip.mind_nparams)
      mip.mind_nf_lc in
  array_map2 (set_names env) arities brv


let type_case_branches_with_names env indspec pj c =
  let (ind,args) = indspec in
  let (lbrty,conclty,_) = Inductive.type_case_branches env indspec pj c in
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
  let params = list_firstn mip.mind_nparams args in
  if is_dependent_elimination_predicate env pj (ind,params) then
    (set_pattern_names env ind lbrty, conclty)
  else (lbrty, conclty)

(* Type of Case predicates *)
let arity_of_case_predicate env (ind,params) dep k =
  let arsign,_ = get_arity env (ind,params) in
  let mind = build_dependent_inductive env (ind,params) in
  let concl = if dep then mkArrow mind (mkSort k) else mkSort k in
  it_mkProd_or_LetIn concl arsign

(***********************************************)
(* Guard condition *)

(* A function which checks that a term well typed verifies both
   syntactic conditions *)

let control_only_guard env = 
  let rec control_rec c = match kind_of_term c with
    | Rel _ | Var _    -> ()
    | Sort _ | Meta _ -> ()
    | Ind _       -> ()
    | Construct _ -> ()
    | Const _        -> ()
    | CoFix (_,(_,tys,bds) as cofix) ->
	Inductive.check_cofix env cofix;
	Array.iter control_rec tys;
	Array.iter control_rec bds;
    | Fix (_,(_,tys,bds) as fix) ->
	Inductive.check_fix env fix; 
	Array.iter control_rec tys;
	Array.iter control_rec bds;
    | Case(_,p,c,b) -> control_rec p;control_rec c;Array.iter control_rec b
    | Evar (_,cl)         -> Array.iter control_rec cl
    | App (c,cl)         -> control_rec c; Array.iter control_rec cl
    | Cast (c1,c2)       -> control_rec c1; control_rec c2
    | Prod (_,c1,c2)     -> control_rec c1; control_rec c2
    | Lambda (_,c1,c2)   -> control_rec c1; control_rec c2
    | LetIn (_,c1,c2,c3) -> control_rec c1; control_rec c2; control_rec c3
  in 
  control_rec 
