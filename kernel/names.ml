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

(*s Section paths are absolute names *)

type section_path = {
  dirpath : dir_path ;
  basename : identifier }

let make_path pa id = { dirpath = pa; basename = id }
let repr_path { dirpath = pa; basename = id } = (pa,id)

(* parsing and printing of section paths *)
let string_of_path sp =
  let (sl,id) = repr_path sp in
  if sl = [] then string_of_id id
  else (string_of_dirpath sl) ^ "." ^ (string_of_id id)

let sp_ord sp1 sp2 =
  let (p1,id1) = repr_path sp1
  and (p2,id2) = repr_path sp2 in
  let p_bit = compare p1 p2 in
  if p_bit = 0 then id_ord id1 id2 else p_bit

module SpOrdered =
  struct
    type t = section_path
    let compare = sp_ord
  end

module Spset = Set.Make(SpOrdered)
module Sppred = Predicate.Make(SpOrdered)
module Spmap = Map.Make(SpOrdered)

(*s********************************************************************)
(* type of global reference *)

type variable = identifier
type constant = section_path
type inductive = section_path * int
type constructor = inductive * int
type mutual_inductive = section_path

let ith_mutual_inductive (sp,_) i = (sp,i)
let ith_constructor_of_inductive ind_sp i = (ind_sp,i)
let inductive_of_constructor (ind_sp,i) = ind_sp
let index_of_constructor (ind_sp,i) = i

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
    let equal = list_for_all2eq (==)
    let hash = Hashtbl.hash
  end)

module Hsp = Hashcons.Make(
  struct 
    type t = section_path
    type u = (dir_path -> dir_path) * (identifier -> identifier)
    let hash_sub (hdir,hident) sp =
      { dirpath = hdir sp.dirpath;
        basename = hident sp.basename }
    let equal sp1 sp2 =
      (sp1.dirpath == sp2.dirpath) && (sp1.basename == sp2.basename)
    let hash = Hashtbl.hash
  end)

let hcons_names () =
  let hstring = Hashcons.simple_hcons Hashcons.Hstring.f () in
  let hident = Hashcons.simple_hcons Hident.f hstring in
  let hname = Hashcons.simple_hcons Hname.f hident in
  let hdir = Hashcons.simple_hcons Hdir.f hident in
  let hspcci = Hashcons.simple_hcons Hsp.f (hdir,hident) in
  (hspcci,hdir,hname,hident,hstring)
