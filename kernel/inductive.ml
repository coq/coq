
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
  | Imbr of section_path * int * (recarg list)

type mutual_inductive_packet = {
  mind_consnames : identifier array;
  mind_typename : identifier;
  mind_lc : constr;
  mind_arity : typed_type;
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
let mis_kelim mis = mis.mis_mip.mind_kelim
let mis_recargs mis =
  Array.map (fun mip -> mip.mind_listrec) mis.mis_mib.mind_packets
let mis_recarg mis = mis.mis_mip.mind_listrec
let mis_typename mis = mis.mis_mip.mind_typename

let mind_nth_type_packet mib n = mib.mind_packets.(n)

(*s Declaration. *)

type mutual_inductive_entry = {
  mind_entry_nparams : int;
  mind_entry_finite : bool;
  mind_entry_inds : (identifier * constr * identifier list * constr) list }

type inductive_error =
  | NonPos of int   
  | NotEnoughArgs of int
  | NotConstructor  
  | NonPar of int * int
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

let mind_extract_params = decompose_prod_n
  
let extract nparams c =
  try mind_extract_params nparams c 
  with UserError _ -> raise (InductiveError (NotEnoughArgs nparams))

let check_params nparams params c = 
  if not (fst (extract nparams c) = params) then 
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
    if not (List.length lna = ntypes) then
      raise (InductiveError BadEntry)
  in
  List.iter check_lc mie.mind_entry_inds

