(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

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

let liftn_inductive_family n d (mis,params) =
  (mis, List.map (liftn n d) params)
let lift_inductive_family n = liftn_inductive_family n 1

let substnl_ind_family l n (mis,params) =
  (mis, List.map (substnl l n) params)


type inductive_type = IndType of inductive_family * constr list

let make_ind_type (indf, realargs) = IndType (indf,realargs)
let dest_ind_type (IndType (indf,realargs)) = (indf,realargs)

let liftn_inductive_type n d (IndType (indf, realargs)) =
  IndType (liftn_inductive_family n d indf, List.map (liftn n d) realargs)
let lift_inductive_type n = liftn_inductive_type n 1

let substnl_ind_type l n (IndType (indf,realargs)) =
  IndType (substnl_ind_family l n indf, List.map (substnl l n) realargs)

let mkAppliedInd (IndType ((ind,params), realargs)) =
  applist (mkInd ind,params@realargs)


let mis_is_recursive_subset listind mip = 
  let rec one_is_rec rvec = 
    List.exists
      (function
	 | Mrec i       -> List.mem i listind 
         | Imbr(_,lvec) -> one_is_rec lvec
         | Norec        -> false
         | Param _      -> false) rvec
  in 
  array_exists one_is_rec mip.mind_listrec

let mis_is_recursive (mib,mip) =
  mis_is_recursive_subset (interval 0 (mib.mind_ntypes-1)) mip

let mis_nf_constructor_type (ind,mib,mip) j =
  let specif = mip.mind_nf_lc
  and ntypes = mib.mind_ntypes
  and nconstr = Array.length mip.mind_consnames in
  let make_Ik k = mkInd ((fst ind),ntypes-k-1) in 
  if j > nconstr then error "Not enough constructors in the type";
  substl (list_tabulate make_Ik ntypes) specif.(j-1)

(* Annotation for cases *)
let make_case_info env ind style pats_source =
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
  let print_info =
    { cnames    = mip.mind_consnames;
      ind_nargs = mip.mind_nrealargs;
      style     = style;
      source    =pats_source } in
  { ci_ind     = ind;
    ci_npar    = mip.mind_nparams;
    ci_pp_info = print_info }

let make_default_case_info env ind =
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
  make_case_info env ind None
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
  let (_,vargs) = list_chop mip.mind_nparams allargs in
  { cs_cstr = ith_constructor_of_inductive ind j;
    cs_params = params;
    cs_nargs = rel_context_length args;
    cs_args = args;
    cs_concl_realargs = Array.of_list vargs }

let get_constructors env (ind,params) =
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
  Array.init (Array.length mip.mind_consnames)
    (fun j -> get_constructor (ind,mib,mip,params) (j+1))

let get_arity env (ind,params) =
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
  let arity = body_of_type mip.mind_nf_arity in
  destArity (prod_applist arity params)

(* Functions to build standard types related to inductive *)
let local_rels =
  let rec relrec acc n = function (* more recent arg in front *)
    | [] -> acc
    | (_,None,_)::l -> relrec (mkRel n :: acc) (n+1) l
    | (_,Some _,_)::l -> relrec acc (n+1) l
  in relrec [] 1

let build_dependent_constructor cs =
  applist
    (mkConstruct cs.cs_cstr,
     (List.map (lift cs.cs_nargs) cs.cs_params)@(local_rels cs.cs_args))

let build_dependent_inductive env ((ind, params) as indf) =
  let arsign,_ = get_arity env indf in
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
  let nrealargs = mip.mind_nrealargs in
  applist 
    (mkInd ind,
     (List.map (lift nrealargs) params)@(local_rels arsign))

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
  let params = fst (list_chop mip.mind_nparams args) in
  if is_dependent_elimination env pj.uj_type (ind,params) then
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
    | Case(_,p,c,b) ->control_rec p;control_rec c;Array.iter control_rec b
    | Evar (_,cl)         -> Array.iter control_rec cl
    | App (_,cl)         -> Array.iter control_rec cl
    | Cast (c1,c2)       -> control_rec c1; control_rec c2
    | Prod (_,c1,c2)     -> control_rec c1; control_rec c2
    | Lambda (_,c1,c2)   -> control_rec c1; control_rec c2
    | LetIn (_,c1,c2,c3) -> control_rec c1; control_rec c2; control_rec c3
  in 
  control_rec 
