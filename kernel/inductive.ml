
(* $Id$ *)

open Util
open Names
open Univ
open Generic
open Term
open Sign
open Constant
open Environ
open Reduction

type mind_specif = {
  mis_sp : section_path;
  mis_mib : mutual_inductive_body;
  mis_tyi : int;
  mis_args : constr array;
  mis_mip : mutual_inductive_packet }

let mis_ntypes mis = mis.mis_mib.mind_ntypes
let mis_index mis = mis.mis_tyi
let mis_nconstr mis = Array.length (mis.mis_mip.mind_consnames)
let mis_nparams mis = mis.mis_mib.mind_nparams
let mis_nrealargs mis = mis.mis_mip.mind_nrealargs
let mis_kelim mis = mis.mis_mip.mind_kelim
let mis_recargs mis =
  Array.map (fun mip -> mip.mind_listrec) mis.mis_mib.mind_packets
let mis_recarg mis = mis.mis_mip.mind_listrec
let mis_typename mis = mis.mis_mip.mind_typename
let mis_typepath mis =
  make_path (dirpath mis.mis_sp) mis.mis_mip.mind_typename CCI
let mis_consnames mis = mis.mis_mip.mind_consnames
let mis_inductive mis = ((mis.mis_sp,mis.mis_tyi),mis.mis_args)

let mis_lc mis =
  Instantiate.instantiate_constr
    (ids_of_sign mis.mis_mib.mind_hyps) mis.mis_mip.mind_lc
    (Array.to_list mis.mis_args)

let mis_lc_without_abstractions mis = 
  let rec strip_DLAM = function
    | (DLAM (n,c1)) -> strip_DLAM c1 
    | (DLAMV (n,v)) -> v
    | _ -> assert false
  in 
  strip_DLAM (mis_lc mis)

let mis_type_mconstructs mispec =
  let specif = mis_lc mispec
  and ntypes = mis_ntypes mispec
  and nconstr = mis_nconstr mispec in
  let make_Ik k = mkMutInd ((mispec.mis_sp,k),mispec.mis_args) 
  and make_Ck k = mkMutConstruct (((mispec.mis_sp,mispec.mis_tyi),k+1),
		       mispec.mis_args) in
  (Array.init nconstr make_Ck, 
   sAPPVList specif (list_tabulate make_Ik ntypes))

let mis_typed_arity mis =
  let idhyps = ids_of_sign mis.mis_mib.mind_hyps 
  and largs = Array.to_list mis.mis_args in
  Instantiate.instantiate_type idhyps mis.mis_mip.mind_arity largs

let mis_arity mispec = incast_type (mis_typed_arity mispec)

let mis_params_ctxt mispec =
  let paramsign,_ =
    decompose_prod_n mispec.mis_mib.mind_nparams
      (body_of_type (mis_typed_arity mispec))
  in paramsign

let mis_sort mispec = mispec.mis_mip.mind_sort

let liftn_inductive_instance n depth mis = {
  mis_sp = mis.mis_sp;
  mis_mib = mis.mis_mib;
  mis_tyi = mis.mis_tyi;
  mis_args = Array.map (liftn n depth) mis.mis_args;
  mis_mip = mis.mis_mip
}

let lift_inductive_instance n = liftn_inductive_instance n 1


type constructor_summary = {
  cs_cstr : constructor;
  cs_params : constr list;
  cs_nargs : int;
  cs_args : (name * constr) list;
  cs_concl_realargs : constr array
}

let lift_constructor n cs = {
  cs_cstr = (let (csp,ctxt) = cs.cs_cstr in (csp,Array.map (lift n) ctxt));
  cs_params = List.map (lift n) cs.cs_params;
  cs_nargs = cs.cs_nargs;
  cs_args = lift_context n cs.cs_args;
  cs_concl_realargs = Array.map (liftn n (cs.cs_nargs+1)) cs.cs_concl_realargs
}

(* [inductive_family] = [inductive_instance] applied to global parameters *)
type inductive_family = IndFamily of mind_specif * constr list
(* = {
  mind : inductive;
  params : constr list;
  nparams : int;
  nrealargs : int;
  nconstr : int;
  ind_kelim : sorts list;
} *)

type inductive_type = IndType of inductive_family * constr list

let liftn_inductive_family n d (IndFamily (mis, params)) =
  IndFamily (liftn_inductive_instance n d mis, List.map (liftn n d) params)
let lift_inductive_family n = liftn_inductive_family n 1

let liftn_inductive_type n d (IndType (indf, realargs)) =
  IndType (liftn_inductive_family n d indf, List.map (liftn n d) realargs)
let lift_inductive_type n = liftn_inductive_type n 1

let make_ind_family (mis, params) = IndFamily (mis,params)
let dest_ind_family (IndFamily (mis,params)) = (mis,params)

let make_ind_type (indf, realargs) = IndType (indf,realargs)
let dest_ind_type (IndType (indf,realargs)) = (indf,realargs)

let mkAppliedInd (IndType (IndFamily (mis,params), realargs)) =
  applist (mkMutInd (mis_inductive mis),params@realargs)

let mis_is_recursive_subset listind mis = 
  let rec one_is_rec rvec = 
    List.exists
      (function
	 | Mrec i       -> List.mem i listind 
         | Imbr(_,lvec) -> one_is_rec lvec
         | Norec        -> false
         | Param _      -> false) rvec
  in 
  array_exists one_is_rec (mis_recarg mis)

let mis_is_recursive mis =
  mis_is_recursive_subset (interval 0 ((mis_ntypes mis)-1)) mis


(* Annotation for cases *)
let make_case_info mis style pats_source =
  let constr_lengths = Array.map List.length (mis_recarg mis) in
  let indsp = (mis.mis_sp,mis.mis_tyi) in
  let print_info =
    (indsp,mis_consnames mis,mis.mis_mip.mind_nrealargs,style,pats_source) in
  (constr_lengths,print_info)

let make_default_case_info mis =
  make_case_info mis None (Array.init (mis_nconstr mis) (fun _ -> RegularPat))

(*s Useful functions *)

let inductive_path_of_constructor_path (ind_sp,i) = ind_sp
let ith_constructor_path_of_inductive_path ind_sp i = (ind_sp,i)

let inductive_of_constructor ((ind_sp,i),args) = (ind_sp,args)
let ith_constructor_of_inductive (ind_sp,args) i = ((ind_sp,i),args)

let build_dependent_constructor cs =
  applist
    (mkMutConstruct cs.cs_cstr,
     (List.map (lift cs.cs_nargs) cs.cs_params)@(rel_list 0 cs.cs_nargs))

let build_dependent_inductive (IndFamily (mis, params)) =
  let nrealargs = mis_nrealargs mis in
  applist 
    (mkMutInd (mis_inductive mis),
     (List.map (lift nrealargs) params)@(rel_list 0 nrealargs))

exception Induc

let find_mrectype env sigma c =
  let (t,l) = whd_betadeltaiota_stack env sigma c [] in
  match t with
    | DOPN(MutInd ind_sp,args) ->  ((ind_sp,args),l)
    | _ -> raise Induc

let find_minductype env sigma c =
  let (t,l) = whd_betadeltaiota_stack env sigma c [] in
  match t with
    | DOPN(MutInd (sp,i),_)
        when mind_type_finite (lookup_mind sp env) i -> (destMutInd t,l)
    | _ -> raise Induc

let find_mcoinductype env sigma c =
  let (t,l) = whd_betadeltaiota_stack env sigma c [] in
  match t with
    | DOPN(MutInd (sp,i),_)
        when not (mind_type_finite (lookup_mind sp env) i) -> (destMutInd t,l)
    | _ -> raise Induc

(* raise Induc if not an inductive type *)
let lookup_mind_specif ((sp,tyi),args) env =
  let mib = lookup_mind sp env in
  { mis_sp = sp; mis_mib = mib; mis_tyi = tyi; mis_args = args;
    mis_mip = mind_nth_type_packet mib tyi }

let find_inductive env sigma ty =
  let (mind,largs) = find_minductype env sigma ty in
  let mispec = lookup_mind_specif mind env in 
  let nparams = mis_nparams mispec in
  let (params,realargs) = list_chop nparams largs in
  make_ind_type (make_ind_family (mispec,params),realargs)

let get_constructors (IndFamily (mispec,params)) =
  let specif = mis_lc mispec in
  let make_ik i = DOPN (MutInd (mispec.mis_sp,i), mispec.mis_args) in
  let types = sAPPVList specif (list_tabulate make_ik (mis_ntypes mispec)) in
  let make_ck j =
    let (args,ccl) = decompose_prod (prod_applist types.(j) params) in
    let (_,vargs) = array_chop (mis_nparams mispec + 1) (destAppL (ensure_appl ccl)) in
    { cs_cstr = ith_constructor_of_inductive (mis_inductive mispec) (j+1);
      cs_params = params;
      cs_nargs = List.length args;
      cs_args = args;
      cs_concl_realargs = vargs } in
  Array.init (mis_nconstr mispec) make_ck

let get_arity env sigma (IndFamily (mispec,params)) =
  let arity = mis_arity mispec in
  splay_arity env sigma (prod_applist arity params)

(* builds the arity of an elimination predicate in sort [s] *)
let make_arity env sigma dep indf s =
  let (arsign,_) = get_arity env sigma indf in
  if dep then
    (* We need names everywhere *)
    it_prod_name env
      (mkArrow (build_dependent_inductive indf) (mkSort s)) arsign
  else
    (* No need to enforce names *)
    prod_it (mkSort s) arsign

(* [p] is the predicate and [cs] a constructor summary *)
let build_branch_type env dep p cs =
  let base = appvect (lift cs.cs_nargs p, cs.cs_concl_realargs) in
  if dep then
    it_prod_name env
      (applist (base,[build_dependent_constructor cs]))
      cs.cs_args
  else
    prod_it base cs.cs_args
