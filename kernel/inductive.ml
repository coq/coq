(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Util
open Identifier
open Names
open Univ
open Term
open Sign
open Declarations
open Environ
open Reduction

type inductive_instance = {
  mis_ln : long_name;
  mis_mib : mutual_inductive_body;
  mis_tyi : int;
  mis_args : constr array;
  mis_mip : one_inductive_body }


let build_mis ((ln,tyi),args) mib =
  { mis_ln = ln; mis_mib = mib; mis_tyi = tyi; mis_args = args;
    mis_mip = mind_nth_type_packet mib tyi }

let mis_ntypes mis = mis.mis_mib.mind_ntypes
let mis_nparams mis = mis.mis_mip.mind_nparams

let mis_index mis = mis.mis_tyi

let mis_nconstr mis = Array.length (mis.mis_mip.mind_consnames)
let mis_nrealargs mis = mis.mis_mip.mind_nrealargs
let mis_kelim mis = mis.mis_mip.mind_kelim
let mis_recargs mis =
  Array.map (fun mip -> mip.mind_listrec) mis.mis_mib.mind_packets
let mis_recarg mis = mis.mis_mip.mind_listrec
let mis_typename mis = ident_of_label mis.mis_mip.mind_typename
let mis_typepath mis =
  (mis.mis_ln,mis.mis_tyi)
let mis_consnames mis = Array.map ident_of_label mis.mis_mip.mind_consnames
let mis_conspaths mis =
  let ind_p = mis_typepath mis in 
  Array.init (mis_nconstr mis) (fun i -> (ind_p,i+1)) 
let mis_inductive mis = ((mis.mis_ln,mis.mis_tyi),mis.mis_args)
let mis_finite mis = mis.mis_mip.mind_finite

let mis_typed_nf_lc mis =
  let sign = mis.mis_mib.mind_hyps in
(*  let args = Array.to_list mis.mis_args in *)
  Array.map (fun t -> (* Instantiate.instantiate_type sign*) t (*args*))
    mis.mis_mip.mind_nf_lc

let mis_nf_lc mis = Array.map body_of_type (mis_typed_nf_lc mis)

let mis_user_lc mis = 
  let sign = mis.mis_mib.mind_hyps in
(*i
  let at = mind_user_lc mis.mis_mip in 
  if Array.length mis.mis_args = 0 then at
  else 
  let args = Array.to_list mis.mis_args in
  Array.map (fun t -> Instantiate.instantiate_constr sign t args) at
i*)
  Array.map (fun t -> (*Instantiate.instantiate_type sign*) t (*args*))
    (mind_user_lc mis.mis_mip)

(* gives the vector of constructors and of 
   types of constructors of an inductive definition 
   correctly instanciated *)

let mis_type_mconstructs mispec =
  let specif = Array.map body_of_type (mis_user_lc mispec)
  and ntypes = mis_ntypes mispec
  and nconstr = mis_nconstr mispec in
  let make_Ik k = mkMutInd ((mispec.mis_ln,ntypes-k-1),mispec.mis_args) 
  and make_Ck k = mkMutConstruct
		    (((mispec.mis_ln,mispec.mis_tyi),k+1),
		       mispec.mis_args) in
  (Array.init nconstr make_Ck, 
   Array.map (substl (list_tabulate make_Ik ntypes)) specif)

let mis_nf_constructor_type i mispec =
  let specif = mis_nf_lc mispec
  and ntypes = mis_ntypes mispec
  and nconstr = mis_nconstr mispec in
  let make_Ik k = mkMutInd ((mispec.mis_ln,ntypes-k-1),mispec.mis_args) in 
  if i > nconstr then error "Not enough constructors in the type";
  substl (list_tabulate make_Ik ntypes) specif.(i-1)

let mis_constructor_type i mispec = 
  let specif = mis_user_lc mispec
  and ntypes = mis_ntypes mispec
  and nconstr = mis_nconstr mispec in
  let make_Ik k = mkMutInd ((mispec.mis_ln,ntypes-k-1),mispec.mis_args) in 
  if i > nconstr then error "Not enough constructors in the type";
  substl (list_tabulate make_Ik ntypes) specif.(i-1)

let mis_arity mis =
  let hyps = mis.mis_mib.mind_hyps 
  in let ar = mind_user_arity mis.mis_mip
  in if Array.length mis.mis_args = 0 then ar
    else let largs = Array.to_list mis.mis_args in
      Instantiate.instantiate_type hyps ar largs

let mis_nf_arity mis =
  let hyps = mis.mis_mib.mind_hyps 
  in if Array.length mis.mis_args = 0 then mis.mis_mip.mind_nf_arity
    else let largs = Array.to_list mis.mis_args in
  Instantiate.instantiate_type hyps mis.mis_mip.mind_nf_arity largs

let mis_params_ctxt mis = mis.mis_mip.mind_params_ctxt
(*
  let paramsign,_ =
    decompose_prod_n_assum mis.mis_mip.mind_nparams
      (body_of_type (mis_nf_arity mis))
  in paramsign
*)

let mis_sort mispec = mispec.mis_mip.mind_sort

let liftn_inductive_instance n depth mis = {
  mis_ln = mis.mis_ln;
  mis_mib = mis.mis_mib;
  mis_tyi = mis.mis_tyi;
  mis_args = Array.map (liftn n depth) mis.mis_args;
  mis_mip = mis.mis_mip
}

let lift_inductive_instance n = liftn_inductive_instance n 1

let substnl_ind_instance l n mis = {
  mis_ln = mis.mis_ln;
  mis_mib = mis.mis_mib;
  mis_tyi = mis.mis_tyi;
  mis_args = Array.map (substnl l n) mis.mis_args;
  mis_mip = mis.mis_mip
}

(* [inductive_family] = [inductive_instance] applied to global parameters *)
type inductive_family = IndFamily of inductive_instance * constr list

type inductive_type = IndType of inductive_family * constr list

let liftn_inductive_family n d (IndFamily (mis, params)) =
  IndFamily (liftn_inductive_instance n d mis, List.map (liftn n d) params)
let lift_inductive_family n = liftn_inductive_family n 1

let liftn_inductive_type n d (IndType (indf, realargs)) =
  IndType (liftn_inductive_family n d indf, List.map (liftn n d) realargs)
let lift_inductive_type n = liftn_inductive_type n 1

let substnl_ind_family l n (IndFamily (mis,params)) =
  IndFamily (substnl_ind_instance l n mis, List.map (substnl l n) params)

let substnl_ind_type l n (IndType (indf,realargs)) =
  IndType (substnl_ind_family l n indf, List.map (substnl l n) realargs)

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
  let indln = (mis.mis_ln,mis.mis_tyi) in
  let print_info =
    (indln,mis_consnames mis,mis.mis_mip.mind_nrealargs,style,pats_source) in
  (mis_nparams mis,print_info)

let make_default_case_info mis =
  make_case_info mis None (Array.init (mis_nconstr mis) (fun _ -> RegularPat))

(*s Useful functions *)

let inductive_path_of_constructor_path (ind_ln,i) = ind_ln
let ith_constructor_path_of_inductive_path ind_ln i = (ind_ln,i)

let inductive_of_constructor ((ind_ln,i),args) = (ind_ln,args)
let index_of_constructor ((ind_ln,i),args) = i
let ith_constructor_of_inductive (ind_ln,args) i = ((ind_ln,i),args)

exception Induc

let extract_mrectype t =
  let (t, l) = whd_stack t in
  match kind_of_term t with
    | IsMutInd ind -> (ind, l)
    | _ -> raise Induc

let find_mrectype env sigma c =
  let (t, l) = whd_betadeltaiota_stack env sigma c in
  match kind_of_term t with
    | IsMutInd ind -> (ind, l)
    | _ -> raise Induc

let find_inductive env sigma c =
  let (t, l) = whd_betadeltaiota_stack env sigma c in
  match kind_of_term t with
    | IsMutInd ((ln,i),_ as ind)
        when mind_type_finite (lookup_mind ln env) i -> (ind, l)
    | _ -> raise Induc

let find_coinductive env sigma c =
  let (t, l) = whd_betadeltaiota_stack env sigma c in
  match kind_of_term t with
    | IsMutInd ((ln,i),_ as ind)
        when not (mind_type_finite (lookup_mind ln env) i) -> (ind, l)
    | _ -> raise Induc

(* raise Induc if not an inductive type *)
let lookup_mind_specif ((ln,tyi),args as ind) env =
  build_mis ind (lookup_mind ln env)

let find_rectype env sigma ty =
  let (mind,largs) = find_mrectype env sigma ty in
  let mispec = lookup_mind_specif mind env in 
  let nparams = mis_nparams mispec in
  let (params,realargs) = list_chop nparams largs in
  make_ind_type (make_ind_family (mispec,params),realargs)

type constructor_summary = {
  cs_cstr : constructor;
  cs_params : constr list;
  cs_nargs : int;
  cs_args : rel_context;
  cs_concl_realargs : constr array
}

let lift_constructor n cs = {
  cs_cstr = (let (csp,ctxt) = cs.cs_cstr in (csp,Array.map (lift n) ctxt));
  cs_params = List.map (lift n) cs.cs_params;
  cs_nargs = cs.cs_nargs;
  cs_args = lift_rel_context n cs.cs_args;
  cs_concl_realargs = Array.map (liftn n (cs.cs_nargs+1)) cs.cs_concl_realargs
}

let instantiate_params t args sign =
  let rec inst s t = function
    | ((_,None,_)::ctxt,a::args) ->
	(match kind_of_term t with
	   | IsProd(_,_,t) -> inst (a::s) t (ctxt,args)
	   | _ -> anomaly"instantiate_params: type, ctxt and args mismatch")
    | ((_,(Some b),_)::ctxt,args) -> 
	(match kind_of_term t with
	   | IsLetIn(_,_,_,t) -> inst ((substl s b)::s) t (ctxt,args)
	   | _ -> anomaly"instantiate_params: type, ctxt and args mismatch")
    | [], [] -> substl s t
    | _ -> anomaly"instantiate_params: type, ctxt and args mismatch"
  in inst [] t (List.rev sign,args)

let get_constructor_type (IndFamily (mispec,params)) j =
  assert (j <= mis_nconstr mispec);
  let typi = mis_constructor_type j mispec in
  instantiate_params typi params (mis_params_ctxt mispec)

let get_constructors_types (IndFamily (mispec,params) as indf) =
  Array.init (mis_nconstr mispec) (fun j -> get_constructor_type indf (j+1))

let get_constructor (IndFamily (mispec,params) as indf) j =
  assert (j <= mis_nconstr mispec);
  let typi = mis_nf_constructor_type j mispec in
  let typi = instantiate_params typi params (mis_params_ctxt mispec) in
  let (args,ccl) = decompose_prod_assum typi in
  let (_,allargs) = whd_stack ccl in
  let (_,vargs) = list_chop (mis_nparams mispec) allargs in
  { cs_cstr = ith_constructor_of_inductive (mis_inductive mispec) j;
    cs_params = params;
    cs_nargs = rel_context_length args;
    cs_args = args;
    cs_concl_realargs = Array.of_list vargs }

let get_constructors (IndFamily (mispec,params) as indf) =
  Array.init (mis_nconstr mispec) (fun j -> get_constructor indf (j+1))

let get_arity_type (IndFamily (mispec,params)) =
  let arity = body_of_type (mis_arity mispec) in
(*  instantiate_params arity params (mis_params_ctxt mispec) *)
  prod_applist arity params

let get_arity (IndFamily (mispec,params)) =
  let arity = body_of_type (mis_nf_arity mispec) in
(*  instantiate_params arity params (mis_params_ctxt mispec) *)
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
    (mkMutConstruct cs.cs_cstr,
     (List.map (lift cs.cs_nargs) cs.cs_params)@(local_rels cs.cs_args))

let build_dependent_inductive (IndFamily (mis, params) as indf) =
  let arsign,_ = get_arity indf in
  let nrealargs = mis_nrealargs mis in
  applist 
    (mkMutInd (mis_inductive mis),
     (List.map (lift nrealargs) params)@(local_rels arsign))

(* builds the arity of an elimination predicate in sort [s] *)
let make_arity env dep indf s =
  let (arsign,_) = get_arity indf in
  if dep then
    (* We need names everywhere *)
    it_mkProd_or_LetIn_name env
      (mkArrow (build_dependent_inductive indf) (mkSort s)) arsign
  else
    (* No need to enforce names *)
    it_mkProd_or_LetIn (mkSort s) arsign

(* [p] is the predicate and [cs] a constructor summary *)
let build_branch_type env dep p cs =
  let base = appvect (lift cs.cs_nargs p, cs.cs_concl_realargs) in
  if dep then
    it_mkProd_or_LetIn_name env
      (applist (base,[build_dependent_constructor cs]))
      cs.cs_args
  else
    it_mkProd_or_LetIn base cs.cs_args


