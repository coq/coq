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

let id_of_string s = check_ident_soft s; String.copy s

let string_of_id id = String.copy id

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

module ModIdmap = Idmap

let make_dirpath x = x
let repr_dirpath x = x

let empty_dirpath = []

let string_of_dirpath = function
  | [] -> "<>"
  | sl -> String.concat "." (List.map string_of_id (List.rev sl))


let u_number = ref 0 
type uniq_ident = int * string * dir_path
let make_uid dir s = incr u_number;(!u_number,String.copy s,dir)
 let debug_string_of_uid (i,s,p) =
 "<"(*^string_of_dirpath p ^"#"^*) ^ s ^"#"^ string_of_int i^">"
let string_of_uid (i,s,p) = 
  string_of_dirpath p ^"."^s

module Umap = Map.Make(struct 
			 type t = uniq_ident 
			 let compare = Pervasives.compare
		       end)

type label = string

type mod_self_id = uniq_ident
let make_msid = make_uid
let repr_msid (n, id, dp) = (n, id, dp)
let debug_string_of_msid = debug_string_of_uid
let refresh_msid (_,s,dir) = make_uid dir s
let string_of_msid = string_of_uid
let id_of_msid (_,s,_) = s
let label_of_msid (_,s,_) = s

type mod_bound_id = uniq_ident
let make_mbid = make_uid
let repr_mbid (n, id, dp) = (n, id, dp)
let debug_string_of_mbid = debug_string_of_uid
let string_of_mbid = string_of_uid
let id_of_mbid (_,s,_) = s
let label_of_mbid (_,s,_) = s


let mk_label l = l
let string_of_label = string_of_id

let id_of_label l = l
let label_of_id id = id

module Labset = Idset
module Labmap = Idmap

type module_path =
  | MPfile of dir_path
  | MPbound of mod_bound_id
  | MPself of mod_self_id 
  | MPdot of module_path * label

let rec check_bound_mp = function
  | MPbound _ -> true
  | MPdot(mp,_) ->check_bound_mp mp
  | _ -> false

let rec string_of_mp = function
  | MPfile sl -> "MPfile (" ^ string_of_dirpath sl ^ ")"
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
module Cmap = KNmap
module Cpred = KNpred
module Cset = KNset

let default_module_name = "If you see this, it's a bug"

let initial_dir = make_dirpath [default_module_name]

let initial_msid = (make_msid initial_dir "If you see this, it's a bug")
let initial_path = MPself initial_msid

type variable = identifier
type constant = kernel_name
type mutual_inductive = kernel_name
type inductive = mutual_inductive * int
type constructor = inductive * int

let constant_of_kn kn = kn
let make_con mp dir l = (mp,dir,l)
let repr_con con = con
let string_of_con = string_of_kn
let con_label = label
let pr_con = pr_kn
let con_modpath = modpath

let mind_modpath = modpath
let ind_modpath ind = mind_modpath (fst ind)
let constr_modpath c = ind_modpath (fst c)

let ith_mutual_inductive (kn,_) i = (kn,i)
let ith_constructor_of_inductive ind i = (ind,i)
let inductive_of_constructor (ind,i) = ind
let index_of_constructor (ind,i) = i

module InductiveOrdered = struct
  type t = inductive
  let compare (spx,ix) (spy,iy) = 
    let c = ix - iy in if c = 0 then KNord.compare spx spy else c
end

module Indmap = Map.Make(InductiveOrdered)

module ConstructorOrdered = struct
  type t = constructor
  let compare (indx,ix) (indy,iy) = 
    let c = ix - iy in if c = 0 then InductiveOrdered.compare indx indy else c
end

module Constrmap = Map.Make(ConstructorOrdered)

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
  (hkn,hkn,hdir,hname,hident,hstring)


(*******)

type transparent_state = Idpred.t * Cpred.t

let empty_transparent_state = (Idpred.empty, Cpred.empty)
let full_transparent_state = (Idpred.full, Cpred.full)
let var_full_transparent_state = (Idpred.full, Cpred.empty)
let cst_full_transparent_state = (Idpred.empty, Cpred.full)

type 'a tableKey =
  | ConstKey of constant
  | VarKey of identifier
  | RelKey of 'a 


type inv_rel_key = int (* index in the [rel_context] part of environment
			  starting by the end, {\em inverse} 
			  of de Bruijn indice *)

type id_key = inv_rel_key tableKey

