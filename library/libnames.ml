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
open Identifier
open Names

type path_kind = CCI | FW | OBJ

let string_of_kind = function
  | CCI -> "cci" 
  | FW -> "fw" 
  | OBJ -> "obj"

let kind_of_string = function
  | "cci" -> CCI 
  | "fw" -> FW 
  | "obj" -> OBJ
  | _ -> invalid_arg "kind_of_string"

(*s Section paths are absolute names *)

type section_path = {
  dirpath : dir_path ;
  basename : identifier ;
  kind : path_kind }

let make_path pa id k = { dirpath = pa; basename = id; kind = k }
let repr_path { dirpath = pa; basename = id; kind = k} = (pa,id,k)

let kind_of_path sp = sp.kind
let basename sp = sp.basename
let dirpath sp = sp.dirpath

(* parsing and printing of section paths *)
let string_of_dirpath sl = String.concat "." sl

let string_of_path sp =
  let (sl,id,k) = repr_path sp in
  String.concat ""
    (List.flatten (List.map (fun s -> [string_of_id s;"."]) sl)
     @ [ string_of_id id ])

let parse_sp s =
  let len = String.length s in
  let rec decoupe_dirs n =
    try
      let pos = String.index_from s n '.' in
      let dir = String.sub s n (pos-n) in
      let dirs,n' = decoupe_dirs (succ pos) in
      dir::dirs,n'
    with
      | Not_found -> [],n
  in
  if len = 0 then invalid_arg "parse_section_path";
  let dirs,n = decoupe_dirs 0 in
  let id = String.sub s n (len-n) in
  dirs,id

let path_of_string s =
  try
    let sl,s = parse_sp s in
    make_path (List.map id_of_string sl) (id_of_string s) CCI
  with
    | Invalid_argument _ -> invalid_arg "path_of_string"

let dirpath_of_string s =
  try
    let sl,s = parse_sp s in
    List.map id_of_string (sl @ [s])
  with
    | Invalid_argument _ -> invalid_arg "dirpath_of_string"

let pr_sp sp = [< 'sTR (string_of_path sp) >]

let sp_of_wd = function
  | [] -> invalid_arg "Names.sp_of_wd"
  | l -> let (bn,dp) = list_sep_last l in 
      make_path dp bn OBJ

let wd_of_sp sp = 
  let (dp,id,_) = repr_path sp in 
    dp @ [id]

let sp_ord sp1 sp2 =
  let (p1,id1,k) = repr_path sp1
  and (p2,id2,k') = repr_path sp2 in
  let ck = compare k k' in
  if ck = 0 then
    let p_bit = compare p1 p2 in
    if p_bit = 0 then compare id1 id2 else p_bit
  else
    ck

let dirpath_prefix_of = list_prefix_of

module SpOrdered =
  struct
    type t = section_path
    let compare = sp_ord
  end

module Spset = Set.Make(SpOrdered)

module Spmap = Map.Make(SpOrdered)

(*s module ident *)

type module_ident = identifier

module ModIdmap = Idmap


(*s qualified names *)
type qualid = dir_path * identifier

let make_qualid p id = (p,id)
let repr_qualid q = q

let string_of_qualid (l,id) = 
  String.concat "." (List.map string_of_id (l@[id]))
let pr_qualid (l,id) =
  prlist_with_sep (fun () -> pr_str ".") pr_str 
    (List.map string_of_id (l@[id]))

let qualid_of_sp sp = make_qualid (dirpath sp) (basename sp)

let qualid_of_dirpath dir =
  let a,l = list_sep_last (repr_qualid dir) in
  make_qualid l a
