(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Pp
open Util
open Identifier
(*i*)

(* This file implements long names *)


type dir_path = identifier list

let make_dirpath x = x
let repr_dirpath x = x

let dirpath_prefix = function 
  | [] -> anomaly "dirpath_prefix: empty dirpath"
  | l -> snd (list_sep_last l)

let split_dirpath d = let (b,d) = list_sep_last d in (d,b)

let parse_sp s =
  let len = String.length s in
  let rec decoupe_dirs n =
    try
      let pos = String.index_from s n '.' in
      let dir = String.sub s n (pos-n) in
      let dirs,n' = decoupe_dirs (succ pos) in
      (id_of_string dir)::dirs,n'
    with
      | Not_found -> [],n
  in
  if len = 0 then invalid_arg "parse_section_path";
  let dirs,n = decoupe_dirs 0 in
  let id = String.sub s n (len-n) in
  dirs, (id_of_string id)

let dirpath_of_string s =
  try
    let sl,s = parse_sp s in
    sl @ [s]
  with
    | Invalid_argument _ -> invalid_arg "dirpath_of_string"

let string_of_dirpath sl = String.concat "." (List.map string_of_id sl)

let pr_dirpath sl = str (string_of_dirpath sl)

let is_dirpath_prefix_of = list_prefix_of



type mod_str_id=uniq_ident
let msid_of_string = unique

type mod_bound_id=uniq_ident
let mbid_of_string = unique
let mbid_of_ident id = unique (string_of_id id)
let string_of_mbid = string_of_uid

type module_path =
  | MPcomp of dir_path
  | MPbid of mod_bound_id
  | MPsid of mod_str_id 
  | MPdot of module_path * label
(*i  | MPapply of module_path * module_path    in the future (maybe) i*)

(* debugging *)
let rec string_of_modpath = function
  | MPcomp sl -> string_of_dirpath sl
  | MPbid uid -> string_of_uid uid
  | MPsid uid -> string_of_uid uid
  | MPdot (mp,l) -> string_of_modpath mp ^ "." ^ string_of_label l

let rec pr_modpath = function
  | MPcomp sl -> pr_dirpath sl
  | MPbid uid -> pr_uid uid
  | MPsid uid -> str "[" ++ pr_uid uid ++ str "]" 
  | MPdot (mp,l) -> pr_modpath mp ++ str "." ++ pr_label l 


(* this is correct under the condition that bound and struct
   identifiers can never be identical (i.e. get the same stamp)! *) 

type substitution = module_path Umap.t

let empty_subst = Umap.empty

let add_msid = Umap.add 
let add_mbid = Umap.add

let map_msid msid mp = add_msid msid mp empty_subst
let map_mbid mbid mp = add_msid mbid mp empty_subst

let join subst = 
  Umap.fold Umap.add subst

let list_contents sub = 
  let one_pair uid mp l =
    (debug_string_of_uid uid, string_of_modpath mp)::l
  in
    Umap.fold one_pair sub []

let debug_string_of_subst sub = 
  let l = List.map (fun (s1,s2) -> s1^"|->"^s2) (list_contents sub) in
    "{" ^ String.concat "; " l ^ "}"

let debug_pr_subst sub = 
  let l = list_contents sub in
  let f (s1,s2) = hov 2 (str s1 ++ spc () ++ str "|-> " ++ str s2) 
  in
    str "{" ++ hov 2 (prlist_with_sep pr_coma f l) ++ str "}" 

let rec subst_modpath sub mp = (* 's like subst *)
  match mp with
    | MPsid sid -> 
	(try Umap.find sid sub with Not_found -> mp)
    | MPbid bid ->
	(try Umap.find bid sub with Not_found -> mp)
    | MPdot (mp1,l) -> 
	let mp1' = subst_modpath sub mp1 in
	  if mp1==mp1' then 
	    mp
	  else
	    MPdot (mp1',l)
    | _ -> mp


let rec occur_in_path uid = function
  | MPsid sid -> sid = uid
  | MPbid bid -> bid = uid
  | MPdot (mp1,_) -> occur_in_path uid mp1
  | _ -> false
    
let occur_uid uid sub = 
  let check_one uid' mp =
    if uid = uid' || occur_in_path uid mp then raise Exit
  in
    try 
      Umap.iter check_one sub;
      false
    with Exit -> true

let occur_msid = occur_uid
let occur_mbid = occur_uid

(* we compare labels first if two MPdot's *)
let rec mp_ord mp1 mp2 = match (mp1,mp2) with
    MPdot(mp1,l1), MPdot(mp2,l2) -> let c=compare l1 l2 in
      if c=0 then
	mp_ord mp1 mp2
      else
	c
  |  _,_ -> compare mp1 mp2

let top_msid = unique "ROOT"
let top_path = MPsid top_msid

module MPmap = Map.Make(struct 
			  type t=module_path 
			  let compare=mp_ord 
			end)

(* Long names of constants,... *)

type long_name = module_path * label

let make_ln mp l = (mp, l)

let modname = fst
let label = snd
let basename (_,l) = ident_of_label l


let subst_long_name sub ((mp1,l) as ln) = 
  let mp1'=subst_modpath sub mp1 in
    if mp1==mp1' then 
      ln
    else
      (mp1',l)
      

(* debugging *)
let string_of_long_name (mp,l) = string_of_modpath (MPdot(mp,l))
let pr_ln (mp,l) = pr_modpath (MPdot(mp,l))

let ln_ord (mp1,l1) (mp2,l2) = mp_ord (MPdot(mp1,l1)) (MPdot(mp2,l2))


module LNmap = Map.Make(struct 
			  type t=long_name 
			  let compare=ln_ord 
			end)

(*s Specific paths for declarations *)

type variable_path = identifier
type constant_path = long_name
type inductive_path = long_name * int
type constructor_path = inductive_path * int
type mutual_inductive_path = long_name

type global_reference =
  | VarRef of variable_path
  | ConstRef of constant_path
  | IndRef of inductive_path
  | ConstructRef of constructor_path
  | ModRef of module_path
  | ModTypeRef of long_name

let subst_global_reference subst ref = match ref with
  | VarRef _ -> ref
  | ConstRef ln ->  
      let ln' = subst_long_name subst ln in if ln==ln' then ref else
	  ConstRef ln'
  | IndRef (ln,i) -> 
      let ln' = subst_long_name subst ln in if ln==ln' then ref else
	  IndRef(ln',i)
  | ConstructRef ((ln,i),j) ->
      let ln' = subst_long_name subst ln in if ln==ln' then ref else
	  ConstructRef ((ln',i),j)
  | ModRef mp ->
      let mp' = subst_modpath subst mp in if mp==mp' then ref else
	  ModRef mp'
  | ModTypeRef ln ->
      let ln' = subst_long_name subst ln in if ln==ln' then ref else
	  ModTypeRef ln'
