(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Errors
open Util
open Names

(**********************************************)

let pr_dirpath sl = (str (string_of_dirpath sl))

(*s Operations on dirpaths *)

(* Pop the last n module idents *)
let pop_dirpath_n n dir =
  make_dirpath (List.skipn n (repr_dirpath dir))

let pop_dirpath p = match repr_dirpath p with
  | [] -> anomaly "dirpath_prefix: empty dirpath"
  | _::l -> make_dirpath l

let is_dirpath_prefix_of d1 d2 =
  List.prefix_of (List.rev (repr_dirpath d1)) (List.rev (repr_dirpath d2))

let chop_dirpath n d =
  let d1,d2 = List.chop n (List.rev (repr_dirpath d)) in
    make_dirpath (List.rev d1), make_dirpath (List.rev d2)

let drop_dirpath_prefix d1 d2 =
  let d = Util.List.drop_prefix (List.rev (repr_dirpath d1)) (List.rev (repr_dirpath d2)) in
    make_dirpath (List.rev d)

let append_dirpath d1 d2 = make_dirpath (repr_dirpath d2 @ repr_dirpath d1)

(* To know how qualified a name should be to be understood in the current env*)
let add_dirpath_prefix id d = make_dirpath (repr_dirpath d @ [id])

let split_dirpath d =
  let l = repr_dirpath d in (make_dirpath (List.tl l), List.hd l)

let add_dirpath_suffix p id = make_dirpath (id :: repr_dirpath p)

(* parsing *)
let parse_dir s =
  let len = String.length s in
  let rec decoupe_dirs dirs n =
    if Int.equal n len && n > 0 then error (s ^ " is an invalid path.");
    if n >= len then dirs else
    let pos =
      try
	String.index_from s n '.'
      with Not_found -> len
    in
    if Int.equal pos n then error (s ^ " is an invalid path.");
    let dir = String.sub s n (pos-n) in
    decoupe_dirs ((id_of_string dir)::dirs) (pos+1)
  in
    decoupe_dirs [] 0

let dirpath_of_string s =
  let path = match s with
  | "" -> []
  | _ -> parse_dir s
  in
  make_dirpath path

let string_of_dirpath = Names.string_of_dirpath


module Dirset = Set.Make(struct type t = dir_path let compare = dir_path_ord end)
module Dirmap = Map.Make(struct type t = dir_path let compare = dir_path_ord end)

(*s Section paths are absolute names *)

type full_path = {
  dirpath : dir_path ;
  basename : identifier }

let make_path pa id = { dirpath = pa; basename = id }

let repr_path { dirpath = pa; basename = id } = (pa,id)

(* parsing and printing of section paths *)
let string_of_path sp =
  let (sl,id) = repr_path sp in
  match repr_dirpath sl with
  | [] -> string_of_id id
  | _ -> (string_of_dirpath sl) ^ "." ^ (string_of_id id)

let sp_ord sp1 sp2 =
  let (p1,id1) = repr_path sp1
  and (p2,id2) = repr_path sp2 in
  let p_bit = compare p1 p2 in
  if Int.equal p_bit 0 then id_ord id1 id2 else p_bit

module SpOrdered =
  struct
    type t = full_path
    let compare = sp_ord
  end

module Spmap = Map.Make(SpOrdered)

let dirpath sp = let (p,_) = repr_path sp in p
let basename sp = let (_,id) = repr_path sp in id

let path_of_string s =
  try
    let dir, id = split_dirpath (dirpath_of_string s) in
    make_path dir id
  with
    | Invalid_argument _ -> invalid_arg "path_of_string"

let pr_path sp = str (string_of_path sp)

let restrict_path n sp =
  let dir, s = repr_path sp in
  let dir' = List.firstn n (repr_dirpath dir) in
  make_path (make_dirpath dir') s

(*s qualified names *)
type qualid = full_path

let make_qualid = make_path
let repr_qualid = repr_path

let string_of_qualid = string_of_path
let pr_qualid = pr_path

let qualid_of_string = path_of_string

let qualid_of_path sp = sp
let qualid_of_ident id = make_qualid empty_dirpath id
let qualid_of_dirpath dir =
  let (l,a) = split_dirpath dir in
  make_qualid l a

type object_name = full_path * kernel_name

type object_prefix = dir_path * (module_path * dir_path)

let make_oname (dirpath,(mp,dir)) id =
  make_path dirpath id, make_kn mp dir (label_of_id id)

(* to this type are mapped dir_path's in the nametab *)
type global_dir_reference =
  | DirOpenModule of object_prefix
  | DirOpenModtype of object_prefix
  | DirOpenSection of object_prefix
  | DirModule of object_prefix
  | DirClosedSection of dir_path
      (* this won't last long I hope! *)

type reference =
  | Qualid of qualid Loc.located
  | Ident of identifier Loc.located

let qualid_of_reference = function
  | Qualid (loc,qid) -> loc, qid
  | Ident (loc,id) -> loc, qualid_of_ident id

let string_of_reference = function
  | Qualid (loc,qid) -> string_of_qualid qid
  | Ident (loc,id) -> string_of_id id

let pr_reference = function
  | Qualid (_,qid) -> pr_qualid qid
  | Ident (_,id) -> str (string_of_id id)

let loc_of_reference = function
  | Qualid (loc,qid) -> loc
  | Ident (loc,id) -> loc

(* Deprecated synonyms *)

let make_short_qualid = qualid_of_ident
let qualid_of_sp = qualid_of_path
