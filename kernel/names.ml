(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Pp
open Util

(*s Identifiers *)

type identifier = string

let id_ord = Pervasives.compare

let id_of_string s = String.copy s

let map_ident id =
  if Options.do_translate() then
    match id with
        "fix" -> "Fix"
      | _ -> id
  else id
let string_of_id id = String.copy (map_ident id)

(* Hash-consing of identifier *)
module Hident = Hashcons.Make(
  struct 
    type t = string
    type u = string -> string
    let hash_sub hstr id = hstr id
    let equal id1 id2 = id1 == id2
    let hash = Hashtbl.hash
  end)

module IdOrdered = 
  struct
    type t = identifier
    let compare = id_ord
  end

module Idset = Set.Make(IdOrdered)
module Idmap = Map.Make(IdOrdered)
module Idpred = Predicate.Make(IdOrdered)

(* Names *)

type name = Name of identifier | Anonymous

(* Dirpaths are lists of module identifiers. The actual representation
   is reversed to optimise sharing: Coq.A.B is ["B";"A";"Coq"] *)
 
type module_ident = identifier
type dir_path = module_ident list

module ModIdOrdered = 
  struct
    type t = identifier
    let compare = Pervasives.compare
  end

module ModIdmap = Map.Make(ModIdOrdered)

let make_dirpath x = x
let repr_dirpath x = x

let empty_dirpath = []

let string_of_dirpath = function
  | [] -> "<empty>"
  | sl ->
      String.concat "." (List.map string_of_id (List.rev sl))


let u_number = ref 0 
type uniq_ident = int * string * dir_path
let make_uid dir s = incr u_number;(!u_number,String.copy s,dir)
let string_of_uid (i,s,p) = 
  "<"(*^string_of_dirpath p ^"#"^*) ^ s ^"#"^ string_of_int i^">"

module Umap = Map.Make(struct 
			 type t = uniq_ident 
			 let compare = Pervasives.compare
		       end)


type mod_self_id = uniq_ident
let make_msid = make_uid
let debug_string_of_msid = string_of_uid
let id_of_msid (_,s,_) = s

type mod_bound_id = uniq_ident
let make_mbid = make_uid
let debug_string_of_mbid = string_of_uid
let id_of_mbid (_,s,_) = s

type label = string
let mk_label l = l
let string_of_label l = l

let id_of_label l = l
let label_of_id id = id

module Labset = Idset
module Labmap = Idmap

type module_path =
  | MPfile of dir_path
  | MPbound of mod_bound_id
  | MPself of mod_self_id 
  | MPdot of module_path * label

let rec string_of_mp = function
  | MPfile sl -> string_of_dirpath sl
  | MPbound uid -> string_of_uid uid
  | MPself uid -> string_of_uid uid
  | MPdot (mp,l) -> string_of_mp mp ^ "." ^ string_of_label l

(* we compare labels first if both are MPdots *)
let rec mp_ord mp1 mp2 = match (mp1,mp2) with
    MPdot(mp1,l1), MPdot(mp2,l2) -> 
      let c = Pervasives.compare l1 l2 in
	if c<>0 then
	  c
	else
	  mp_ord mp1 mp2
  |  _,_ -> Pervasives.compare mp1 mp2

module MPord = struct
  type t = module_path
  let compare = mp_ord
end

module MPset = Set.Make(MPord)
module MPmap = Map.Make(MPord)


(* this is correct under the condition that bound and struct
   identifiers can never be identical (i.e. get the same stamp)! *) 

type substitution = module_path Umap.t

let empty_subst = Umap.empty

let add_msid = Umap.add 
let add_mbid = Umap.add

let map_msid msid mp = add_msid msid mp empty_subst
let map_mbid mbid mp = add_msid mbid mp empty_subst

let list_contents sub = 
  let one_pair uid mp l =
    (string_of_uid uid, string_of_mp mp)::l
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

let rec subst_mp sub mp = (* 's like subst *)
  match mp with
    | MPself sid -> 
	(try Umap.find sid sub with Not_found -> mp)
    | MPbound bid ->
	(try Umap.find bid sub with Not_found -> mp)
    | MPdot (mp1,l) -> 
	let mp1' = subst_mp sub mp1 in
	  if mp1==mp1' then 
	    mp
	  else
	    MPdot (mp1',l)
    | _ -> mp

let join subst1 subst2 = 
  let subst = Umap.map (subst_mp subst2) subst1 in
  Umap.fold Umap.add subst2 subst

let rec occur_in_path uid = function
  | MPself sid -> sid = uid
  | MPbound bid -> bid = uid
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



(* Kernel names *)

type kernel_name = module_path * dir_path * label

let make_kn mp dir l = (mp,dir,l)
let repr_kn kn = kn

let modpath kn = 
  let mp,_,_ = repr_kn kn in mp

let label kn = 
  let _,_,l = repr_kn kn in l

let string_of_kn (mp,dir,l) = 
  string_of_mp mp ^ "#" ^ string_of_dirpath dir ^ "#" ^ string_of_label l

let pr_kn kn = str (string_of_kn kn)


let subst_kn sub (mp,dir,l as kn) = 
  let mp' = subst_mp sub mp in
    if mp==mp' then kn else (mp',dir,l)


let kn_ord kn1 kn2 = 
    let mp1,dir1,l1 = kn1 in
    let mp2,dir2,l2 = kn2 in
    let c = Pervasives.compare l1 l2 in
      if c <> 0 then
	c
      else 
	let c = Pervasives.compare dir1 dir2 in
	  if c<>0 then
	    c 
	  else
	    MPord.compare mp1 mp2


module KNord = struct
  type t = kernel_name
  let compare =kn_ord
end

module KNmap = Map.Make(KNord)
module KNpred = Predicate.Make(KNord)
module KNset = Set.Make(KNord)


let default_module_name = id_of_string "If you see this, it's a bug"

let initial_dir = make_dirpath [default_module_name]

let initial_msid = (make_msid initial_dir "If you see this, it's a bug")
let initial_path = MPself initial_msid

type variable = identifier
type constant = kernel_name
type mutual_inductive = kernel_name
type inductive = mutual_inductive * int
type constructor = inductive * int

let ith_mutual_inductive (kn,_) i = (kn,i)
let ith_constructor_of_inductive ind i = (ind,i)
let inductive_of_constructor (ind,i) = ind
let index_of_constructor (ind,i) = i

(* Better to have it here that in closure, since used in grammar.cma *)
type evaluable_global_reference =
  | EvalVarRef of identifier
  | EvalConstRef of constant

(* Hash-consing of name objects *)
module Hname = Hashcons.Make(
  struct 
    type t = name
    type u = identifier -> identifier
    let hash_sub hident = function
      | Name id -> Name (hident id)
      | n -> n
    let equal n1 n2 =
      match (n1,n2) with
	| (Name id1, Name id2) -> id1 == id2
        | (Anonymous,Anonymous) -> true
        | _ -> false
    let hash = Hashtbl.hash
  end)

module Hdir = Hashcons.Make(
  struct 
    type t = dir_path
    type u = identifier -> identifier
    let hash_sub hident d = List.map hident d
    let rec equal d1 d2 = match (d1,d2) with
      | [],[] -> true
      | id1::d1,id2::d2 -> id1 == id2 & equal d1 d2
      | _ -> false
    let hash = Hashtbl.hash
  end)

module Huniqid = Hashcons.Make(
  struct 
    type t = uniq_ident
    type u = (string -> string) * (dir_path -> dir_path)
    let hash_sub (hstr,hdir) (n,s,dir) = (n,hstr s,hdir dir)
    let equal (n1,s1,dir1) (n2,s2,dir2) = n1 = n2 & s1 = s2 & dir1 == dir2
    let hash = Hashtbl.hash
  end)

module Hmod = Hashcons.Make(
  struct 
    type t = module_path
    type u = (dir_path -> dir_path) * (uniq_ident -> uniq_ident) *
	(string -> string)
    let rec hash_sub (hdir,huniqid,hstr as hfuns) = function
      | MPfile dir -> MPfile (hdir dir)
      | MPbound m -> MPbound (huniqid m)
      | MPself m -> MPself (huniqid m)
      | MPdot (md,l) -> MPdot (hash_sub hfuns md, hstr l)
    let rec equal d1 d2 = match (d1,d2) with
      | MPfile dir1, MPfile dir2 -> dir1 == dir2
      | MPbound m1, MPbound m2 -> m1 == m2
      | MPself m1, MPself m2 -> m1 == m2
      | MPdot (mod1,l1), MPdot (mod2,l2) -> equal mod1 mod2 & l1 = l2
      | _ -> false
    let hash = Hashtbl.hash
  end)

module Hkn = Hashcons.Make(
  struct 
    type t = kernel_name
    type u = (module_path -> module_path)
	* (dir_path -> dir_path) * (string -> string)
    let hash_sub (hmod,hdir,hstr) (md,dir,l) = (hmod md, hdir dir, hstr l)
    let equal (mod1,dir1,l1) (mod2,dir2,l2) =
      mod1 == mod2 && dir1 == dir2 && l1 == l2
    let hash = Hashtbl.hash
  end)

let hcons_names () =
  let hstring = Hashcons.simple_hcons Hashcons.Hstring.f () in
  let hident = Hashcons.simple_hcons Hident.f hstring in
  let hname = Hashcons.simple_hcons Hname.f hident in
  let hdir = Hashcons.simple_hcons Hdir.f hident in
  let huniqid = Hashcons.simple_hcons Huniqid.f (hstring,hdir) in
  let hmod = Hashcons.simple_hcons Hmod.f (hdir,huniqid,hstring) in
  let hkn = Hashcons.simple_hcons Hkn.f (hmod,hdir,hstring) in
  (hkn,hdir,hname,hident,hstring)
