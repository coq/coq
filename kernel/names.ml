(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Pp
open Util

(*s Identifiers *)

type identifier = string

let id_ord = Pervasives.compare

let string_of_id id = String.copy id
let id_of_string s = String.copy s

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

let string_of_dirpath = function
  | [] -> "<empty>"
  | sl ->
      String.concat "." (List.map string_of_id (List.rev sl))


let u_number = ref 0 
type uniq_ident = int * string * dir_path
let string_of_uid (i,s,p) = "<"^string_of_dirpath p ^ s ^ string_of_int i^">"

type mod_self_id = uniq_ident
let make_msid dir s = incr u_number;(!u_number,s,dir)
let string_of_msid = string_of_uid

type mod_bound_id = uniq_ident
let make_mbid dir s = incr u_number;(!u_number,s,dir)
let string_of_mbid = string_of_uid

type label = string
let mk_label l = l
let string_of_label l = l

let id_of_label l = l
let label_of_id id = id

module Labset = Idset

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

(* we compare labels first if two MPdot's *)
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

module MPmap = Map.Make(MPord)


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


(* TODO: revise this!!! *)
let initial_path = MPself (make_msid [] "INIT")

type variable = identifier
type constant = kernel_name
type mutual_inductive = kernel_name
type inductive = mutual_inductive * int
type constructor = inductive * int

let ith_mutual_inductive (kn,_) i = (kn,i)
let ith_constructor_of_inductive ind i = (ind,i)
let inductive_of_constructor (ind,i) = ind
let index_of_constructor (ind,i) = i

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
    let equal d1 d2 = List.for_all2 (==) d1 d2
    let hash = Hashtbl.hash
  end)

module Hkn = Hashcons.Make(
  struct 
    type t = kernel_name
    type u = identifier -> identifier
    let hash_sub hident kn = Util.todo "hash_cons"; kn
    let equal kn1 kn2 = kn1==kn2
    let hash = Hashtbl.hash
  end)

let hcons_names () =
  let hstring = Hashcons.simple_hcons Hashcons.Hstring.f () in
  let hident = Hashcons.simple_hcons Hident.f hstring in
  let hname = Hashcons.simple_hcons Hname.f hident in
  let hdir = Hashcons.simple_hcons Hdir.f hident in
  let hkn = Hashcons.simple_hcons Hkn.f hident in
  (hkn,hdir,hname,hident,hstring)
