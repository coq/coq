(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

open Pp
open Util
(*open Identifier*)
open Names
(*open Nameops*)

type global_reference =
  | VarRef of variable
  | ConstRef of constant
  | IndRef of inductive
  | ConstructRef of constructor

(* subst_global_ref : substitution -> global_reference -> global_reference *)

(**********************************************)

let pr_dirpath sl = (str (string_of_dirpath sl))

(* Operations on dirpaths *)
let empty_dirpath = make_dirpath []


(* Pop the last n module idents *)
let extract_dirpath_prefix n dir =
  let (_,dir') = list_chop n (repr_dirpath dir) in
  make_dirpath dir'

let dirpath_prefix p = match repr_dirpath p with
  | [] -> anomaly "dirpath_prefix: empty dirpath"
  | _::l -> make_dirpath l

let is_dirpath_prefix_of d1 d2 =
  list_prefix_of (List.rev (repr_dirpath d1)) (List.rev (repr_dirpath d2))

(* To know how qualified a name should be to be understood in the current env*)
let add_dirpath_prefix id d = make_dirpath (repr_dirpath d @ [id])

let split_dirpath d =
  let l = repr_dirpath d in (make_dirpath (List.tl l), List.hd l)

let extend_dirpath p id = make_dirpath (id :: repr_dirpath p)


(*
let path_of_constructor env ((sp,tyi),ind) =
   let mib = Environ.lookup_mind sp env in
   let mip = mib.mind_packets.(tyi) in 
   let (pa,_) = repr_path sp in 
   Names.make_path pa (mip.mind_consnames.(ind-1))

let path_of_inductive env (sp,tyi) =
  if tyi = 0 then sp
  else
    let mib = Environ.lookup_mind sp env in
    let mip = mib.mind_packets.(tyi) in 
    let (pa,_) = repr_path sp in 
    Names.make_path pa (mip.mind_typename) 
*)
(* parsing *)
let parse_dir s =
  let len = String.length s in
  let rec decoupe_dirs dirs n =
    if n>=len then dirs else
    let pos =
      try
	String.index_from s n '.' 
      with Not_found -> len
    in
    let dir = String.sub s n (pos-n) in
      decoupe_dirs ((id_of_string dir)::dirs) (pos+1)	  
  in
    decoupe_dirs [] 0

let dirpath_of_string s = 
  match parse_dir s with
      [] -> invalid_arg "dirpath_of_string"
    | dir -> make_dirpath dir


(*s Section paths are absolute names *)

type section_path = {
  dirpath : dir_path ;
  basename : identifier }

let make_path pa id = { dirpath = pa; basename = id }
let repr_path { dirpath = pa; basename = id } = (pa,id)

(* parsing and printing of section paths *)
let string_of_path sp =
  let (sl,id) = repr_path sp in
  if repr_dirpath sl = [] then string_of_id id
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

let dirpath sp = let (p,_) = repr_path sp in p
let basename sp = let (_,id) = repr_path sp in id

let path_of_string s =
  try
    let dir, id = split_dirpath (dirpath_of_string s) in
    make_path dir id
  with
    | Invalid_argument _ -> invalid_arg "path_of_string"

let pr_sp sp = str (string_of_path sp) 

let restrict_path n sp =
  let dir, s = repr_path sp in
  let (dir',_) = list_chop n (repr_dirpath dir) in
  make_path (make_dirpath dir') s

let encode_kn dir id = make_kn (MPfile dir) (make_dirpath []) (label_of_id id)

let decode_kn kn = 
  let mp,dir,l = repr_kn kn in
    match mp with
	MPfile dir -> (dir,id_of_label l)
      | _ -> anomaly "MPfile expected!"


(*s qualified names *)
type qualid = section_path

let make_qualid = make_path
let repr_qualid = repr_path

let string_of_qualid = string_of_path
let pr_qualid = pr_sp

let qualid_of_sp sp = sp
let make_short_qualid id = make_qualid empty_dirpath id
let qualid_of_dirpath dir = 
  let (l,a) = split_dirpath dir in
  make_qualid l a
