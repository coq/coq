(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open CErrors
open Util
open Names

(**********************************************)

let pr_dirpath sl = DirPath.print sl

(*s Operations on dirpaths *)

let split_dirpath d = match DirPath.repr d with
  | id :: l -> DirPath.make l, id
  | _ -> failwith "split_dirpath"

let pop_dirpath p = match DirPath.repr p with
  | _::l -> DirPath.make l
  | [] -> failwith "pop_dirpath"

(* Pop the last n module idents *)
let pop_dirpath_n n dir = DirPath.make (List.skipn n (DirPath.repr dir))

let is_dirpath_prefix_of d1 d2 =
  List.prefix_of Id.equal
    (List.rev (DirPath.repr d1)) (List.rev (DirPath.repr d2))

let is_dirpath_suffix_of dir1 dir2 =
  let dir1 = DirPath.repr dir1 in
  let dir2 = DirPath.repr dir2 in
  List.prefix_of Id.equal dir1 dir2

let chop_dirpath n d =
  let d1,d2 = List.chop n (List.rev (DirPath.repr d)) in
  DirPath.make (List.rev d1), DirPath.make (List.rev d2)

let drop_dirpath_prefix d1 d2 =
  let d =
    List.drop_prefix Id.equal
      (List.rev (DirPath.repr d1)) (List.rev (DirPath.repr d2))
  in
  DirPath.make (List.rev d)

let append_dirpath d1 d2 = DirPath.make (DirPath.repr d2 @ DirPath.repr d1)

let add_dirpath_prefix id d = DirPath.make (DirPath.repr d @ [id])

let add_dirpath_suffix p id = DirPath.make (id :: DirPath.repr p)

(* parsing *)
let parse_dir s =
  let len = String.length s in
  let rec decoupe_dirs dirs n =
    if Int.equal n len && n > 0 then user_err Pp.(str @@ s ^ " is an invalid path.");
    if n >= len then dirs else
    let pos =
      try
	String.index_from s n '.'
      with Not_found -> len
    in
    if Int.equal pos n then user_err Pp.(str @@ s ^ " is an invalid path.");
    let dir = String.sub s n (pos-n) in
    decoupe_dirs ((Id.of_string dir)::dirs) (pos+1)
  in
    decoupe_dirs [] 0

let dirpath_of_string s =
  let path = match s with
  | "" -> []
  | _ -> parse_dir s
  in
  DirPath.make path

let string_of_dirpath = Names.DirPath.to_string

module Dirset = Set.Make(DirPath)
module Dirmap = Map.Make(DirPath)

(*s Section paths are absolute names *)

type full_path = {
  dirpath : DirPath.t ;
  basename : Id.t }

let dirpath sp = sp.dirpath
let basename sp = sp.basename

let make_path pa id = { dirpath = pa; basename = id }

let repr_path { dirpath = pa; basename = id } = (pa,id)

let eq_full_path p1 p2 =
  Id.equal p1.basename p2.basename &&
  DirPath.equal p1.dirpath p2.dirpath

(* parsing and printing of section paths *)
let string_of_path sp =
  let (sl,id) = repr_path sp in
  match DirPath.repr sl with
  | [] -> Id.to_string id
  | _ -> (DirPath.to_string sl) ^ "." ^ (Id.to_string id)

let sp_ord sp1 sp2 =
  let (p1,id1) = repr_path sp1
  and (p2,id2) = repr_path sp2 in
  let p_bit = DirPath.compare p1 p2 in
  if Int.equal p_bit 0 then Id.compare id1 id2 else p_bit

module SpOrdered =
  struct
    type t = full_path
    let compare = sp_ord
  end

module Spmap = Map.Make(SpOrdered)

let path_of_string s =
  try
    let dir, id = split_dirpath (dirpath_of_string s) in
    make_path dir id
  with
    | Invalid_argument _ -> invalid_arg "path_of_string"

let pr_path sp = str (string_of_path sp)

let restrict_path n sp =
  let dir, s = repr_path sp in
  let dir' = List.firstn n (DirPath.repr dir) in
  make_path (DirPath.make dir') s

(*s qualified names *)
type qualid = full_path

let make_qualid = make_path
let repr_qualid = repr_path

let qualid_eq = eq_full_path

let string_of_qualid = string_of_path
let pr_qualid = pr_path

let qualid_of_string = path_of_string

let qualid_of_path sp = sp
let qualid_of_ident id = make_qualid DirPath.empty id
let qualid_of_dirpath dir =
  let (l,a) = split_dirpath dir in
  make_qualid l a

type object_name = full_path * KerName.t

type object_prefix = {
  obj_dir : DirPath.t;
  obj_mp  : ModPath.t;
  obj_sec : DirPath.t;
}

(* let make_oname (dirpath,(mp,dir)) id = *)
let make_oname { obj_dir; obj_mp; obj_sec } id =
  make_path obj_dir id, KerName.make obj_mp obj_sec (Label.of_id id)

(* to this type are mapped DirPath.t's in the nametab *)
type global_dir_reference =
  | DirOpenModule of object_prefix
  | DirOpenModtype of object_prefix
  | DirOpenSection of object_prefix
  | DirModule of object_prefix
  | DirClosedSection of DirPath.t
      (* this won't last long I hope! *)

let eq_op op1 op2 =
  DirPath.equal op1.obj_dir op2.obj_dir &&
  DirPath.equal op1.obj_sec op2.obj_sec &&
  ModPath.equal op1.obj_mp  op2.obj_mp

let eq_global_dir_reference r1 r2 = match r1, r2 with
| DirOpenModule op1, DirOpenModule op2 -> eq_op op1 op2
| DirOpenModtype op1, DirOpenModtype op2 -> eq_op op1 op2
| DirOpenSection op1, DirOpenSection op2 -> eq_op op1 op2
| DirModule op1, DirModule op2 -> eq_op op1 op2
| DirClosedSection dp1, DirClosedSection dp2 -> DirPath.equal dp1 dp2
| _ -> false

type reference_r =
  | Qualid of qualid
  | Ident of Id.t
type reference = reference_r CAst.t

let qualid_of_reference = CAst.map (function
  | Qualid qid -> qid
  | Ident id -> qualid_of_ident id)

let string_of_reference = CAst.with_val (function
  | Qualid qid -> string_of_qualid qid
  | Ident id -> Id.to_string id)

let pr_reference = CAst.with_val (function
  | Qualid qid -> pr_qualid qid
  | Ident id -> Id.print id)

let eq_reference {CAst.v=r1} {CAst.v=r2} = match r1, r2 with
| Qualid q1, Qualid q2 -> qualid_eq q1 q2
| Ident id1, Ident id2 -> Id.equal id1 id2
| _ -> false

let join_reference {CAst.loc=l1;v=ns} {CAst.loc=l2;v=r} =
  CAst.make ?loc:(Loc.merge_opt l1 l2) (
  match ns , r with
    Qualid q1, Qualid q2 ->
      let (dp1,id1) = repr_qualid q1 in
      let (dp2,id2) = repr_qualid q2 in
      Qualid (make_qualid
		(append_dirpath (append_dirpath dp1 (dirpath_of_string (Names.Id.to_string id1))) dp2)
		id2)
  | Qualid q1, Ident id2 ->
    let (dp1,id1) = repr_qualid q1 in
    Qualid (make_qualid
	      (append_dirpath dp1 (dirpath_of_string (Names.Id.to_string id1)))
	      id2)
  | Ident id1, Qualid q2 ->
    let (dp2,id2) = repr_qualid q2 in
    Qualid (make_qualid
      (append_dirpath (dirpath_of_string (Names.Id.to_string id1)) dp2)
      id2)
  | Ident id1, Ident id2 ->
    Qualid (make_qualid
      (dirpath_of_string (Names.Id.to_string id1)) id2)
  )

(* Default paths *)
let default_library = Names.DirPath.initial (* = ["Top"] *)

(*s Roots of the space of absolute names *)
let coq_string = "Coq"
let coq_root = Id.of_string coq_string
let default_root_prefix = DirPath.empty

(* Deprecated synonyms *)

let make_short_qualid = qualid_of_ident
let qualid_of_sp = qualid_of_path
