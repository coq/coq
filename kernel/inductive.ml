
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
  fullmind : constr;
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

type inductive_error =
  | NonPos of name list * constr * constr
  | NotEnoughArgs of name list * constr * constr
  | NotConstructor of name list * constr * constr
  | NonPar of name list * constr * int * constr * constr
  | SameNamesTypes of identifier
  | SameNamesConstructors of identifier * identifier
  | NotAnArity of identifier
  | BadEntry

exception InductiveError of inductive_error

(* [check_constructors_names id s cl] checks that all the constructors names
   appearing in [l] are not present in the set [s], and returns the new set
   of names. The name [id] is the name of the current inductive type, used
   when reporting the error. *)

let check_constructors_names id =
  let rec check idset = function
    | [] -> idset
    | c::cl -> 
	if Idset.mem c idset then 
	  raise (InductiveError (SameNamesConstructors (id,c)))
	else
	  check (Idset.add c idset) cl
  in
  check

(* [mind_check_names mie] checks the names of an inductive types declaration,
   and raises the corresponding exceptions when two types or two constructors
   have the same name. *)

let mind_check_names mie =
  let rec check indset cstset = function
    | [] -> ()
    | (id,_,cl,_)::inds -> 
	if Idset.mem id indset then
	  raise (InductiveError (SameNamesTypes id))
	else
	  let cstset' = check_constructors_names id cstset cl in
	  check (Idset.add id indset) cstset' inds
  in
  check Idset.empty Idset.empty mie.mind_entry_inds

(* [mind_extract_params mie] extracts the params from an inductive types
   declaration, and checks that they are all present (and all the same)
   for all the given types. *)

let mind_extract_params n c = 
  let (l,c') = decompose_prod_n n c in (List.rev l,c')
  
let extract nparams c =
  try mind_extract_params nparams c 
  with UserError _ -> raise (InductiveError BadEntry)

let check_params nparams params c = 
  let eparams = fst (extract nparams c) in
  try
    List.iter2 
      (fun (n1,t1) (n2,t2) ->
	 if n1 <> n2 || strip_all_casts t1 <> strip_all_casts t2 then
	   raise (InductiveError BadEntry))
      eparams params
  with Invalid_argument _ ->
    raise (InductiveError BadEntry)

let mind_extract_and_check_params mie =
  let nparams = mie.mind_entry_nparams in
  match mie.mind_entry_inds with
    | [] -> anomaly "empty inductive types declaration"
    | (_,ar,_,_)::l -> 
	let (params,_) = extract nparams ar in
	List.iter (fun (_,c,_,_) -> check_params nparams params c) l;
	params

let mind_check_lc params mie =
  let ntypes = List.length mie.mind_entry_inds in
  let nparams = List.length params in
  let check_lc (_,_,_,lc) =
    let (lna,c) = decomp_all_DLAMV_name lc in
    Array.iter (check_params nparams params) c;
    if not (List.length lna = ntypes) then raise (InductiveError BadEntry)
  in
  List.iter check_lc mie.mind_entry_inds

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
