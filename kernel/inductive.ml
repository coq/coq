
(* $Id$ *)

open Util
open Names
open Univ
open Generic
open Term
open Sign

type recarg = 
  | Param of int 
  | Norec 
  | Mrec of int 
  | Imbr of inductive_path * recarg list

type mutual_inductive_packet = {
  mind_consnames : identifier array;
  mind_typename : identifier;
  mind_lc : constr;
  mind_arity : typed_type;
  mind_nrealargs : int;
  mind_kelim : sorts list;
  mind_listrec : (recarg list) array;
  mind_finite : bool }

type mutual_inductive_body = {
  mind_kind : path_kind;
  mind_ntypes : int;
  mind_hyps : typed_type signature;
  mind_packets : mutual_inductive_packet array;
  mind_constraints : constraints;
  mind_singl : constr option;
  mind_nparams : int }

let mind_type_finite mib i = mib.mind_packets.(i).mind_finite

type mind_specif = {
  mis_sp : section_path;
  mis_mib : mutual_inductive_body;
  mis_tyi : int;
  mis_args : constr array;
  mis_mip : mutual_inductive_packet }

let mis_ntypes mis = mis.mis_mib.mind_ntypes
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

type constructor_summary = {
  cs_cstr : constructor;
  cs_params : constr list;
  cs_nargs : int;
  cs_args : (name * constr) list;
  cs_concl_realargs : constr array
}

(* A light version of mind_specif_of_mind with pre-splitted args *)
(* and a receipt to build a summary of constructors *)
type inductive_summary = {
  mind : inductive;
  params : constr list;
  realargs : constr list;
  nparams : int;
  nrealargs : int;
  nconstr : int;
}

let is_recursive listind = 
  let rec one_is_rec rvec = 
    List.exists (function
		   | Mrec(i)        -> List.mem i listind 
                   | Imbr(_,lvec) -> one_is_rec lvec
                   | Norec          -> false
                   | Param(_)       -> false) rvec
  in 
  array_exists one_is_rec

let mis_is_recursive mis =
  is_recursive (interval 0 ((mis_ntypes mis)-1)) (mis_recarg mis)

let mind_nth_type_packet mib n = mib.mind_packets.(n)

(* Annotation for cases *)
let make_case_info mis style pats_source =
  let constr_lengths = Array.map List.length (mis_recarg mis) in
  let indsp = (mis.mis_sp,mis.mis_tyi) in
  let print_info =
    (indsp,mis_consnames mis,mis.mis_mip.mind_nrealargs,style,pats_source) in
  (constr_lengths,print_info)

let make_default_case_info mis =
  make_case_info mis None (Array.init (mis_nconstr mis) (fun _ -> RegularPat))

(*s Declaration. *)

type mutual_inductive_entry = {
  mind_entry_nparams : int;
  mind_entry_finite : bool;
  mind_entry_inds : (identifier * constr * identifier list * constr) list }

let inductive_path_of_constructor_path (ind_sp,i) = ind_sp
let ith_constructor_path_of_inductive_path ind_sp i = (ind_sp,i)

let inductive_of_constructor ((ind_sp,i),args) = (ind_sp,args)
let ith_constructor_of_inductive (ind_sp,args) i = ((ind_sp,i),args)

let build_dependent_constructor cs =
  applist
    (mkMutConstruct cs.cs_cstr,
     (List.map (lift cs.cs_nargs) cs.cs_params)@(rel_list 0 cs.cs_nargs))

let build_dependent_inductive is =
  applist 
    (mkMutInd is.mind,
     (List.map (lift is.nparams) is.params)@(rel_list 0 is.nrealargs))
