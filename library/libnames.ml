(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names

(**********************************************)

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

let drop_dirpath_prefix d1 d2 =
  let d =
    List.drop_prefix Id.equal
      (List.rev (DirPath.repr d1)) (List.rev (DirPath.repr d2))
  in
  DirPath.make (List.rev d)

let append_dirpath d1 d2 = DirPath.make (DirPath.repr d2 @ DirPath.repr d1)

let add_dirpath_suffix p id = DirPath.make (id :: DirPath.repr p)

(* parsing *)
let parse_dir s =
  let len = String.length s in
  let rec decoupe_dirs dirs n =
    if Int.equal n len && n > 0 then
      CErrors.user_err Pp.(str @@ s ^ " is an invalid path.");
    if n >= len then dirs else
    let pos =
      try
        String.index_from s n '.'
      with Not_found -> len
    in
    if Int.equal pos n then
      CErrors.user_err Pp.(str @@ s ^ " is an invalid path.");
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

(** Absolute paths *)

type full_path = {
  dirpath : DirPath.t;
  basename : Id.t;
}

let dirpath sp = sp.dirpath
let basename sp = sp.basename

let dirpath_of_path { dirpath; basename } =
  add_dirpath_suffix dirpath basename

let is_path_prefix_of p dp = is_dirpath_prefix_of (dirpath_of_path p) dp

let make_path pa id = { dirpath = pa; basename = id }

let make_path0 dp =
  let dp, id = split_dirpath dp in
  make_path dp id

let dummy_full_path = make_path0 DirPath.dummy

let add_path_suffix { dirpath = pa0; basename = id0 } id =
  { dirpath = add_dirpath_suffix pa0 id0; basename = id }

let append_path ({ dirpath = dp; basename = id0 } as p) dp' =
  if DirPath.is_empty dp' then p
  else
    let dp', id = split_dirpath dp' in
    { dirpath = append_dirpath (add_dirpath_suffix dp id0) dp'; basename = id }

let path_pop_n_suffixes n ({ dirpath = dp; } as path) =
  if n = 0 then path
  else
    let dp = pop_dirpath_n (n-1) dp in
    make_path0 dp

let path_pop_suffix p = path_pop_n_suffixes 1 p

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

let compare_full_path sp1 sp2 =
  let (p1,id1) = repr_path sp1
  and (p2,id2) = repr_path sp2 in
  let p_bit = DirPath.compare p1 p2 in
  if Int.equal p_bit 0 then Id.compare id1 id2 else p_bit

module SpOrdered =
  struct
    type t = full_path
    let compare = compare_full_path
  end

module Spmap = Map.Make(SpOrdered)

let path_of_string s =
  try
    let dir, id = split_dirpath (dirpath_of_string s) in
    make_path dir id
  with
    | Invalid_argument _ -> invalid_arg "path_of_string"

let pr_path sp = Pp.str (string_of_path sp)

(*s qualified names *)
type qualid_r = full_path
type qualid = qualid_r CAst.t

let make_qualid ?loc pa id = CAst.make ?loc (make_path pa id)
let repr_qualid {CAst.v=qid} = repr_path qid

let qualid_eq qid1 qid2 = eq_full_path qid1.CAst.v qid2.CAst.v

let is_qualid_suffix_of_full_path
    CAst.{v={dirpath=dirpath1;basename=basename1}} {dirpath=dirpath2;basename=basename2} =
  let dir1 = DirPath.repr dirpath1 in
  let dir2 = DirPath.repr dirpath2 in
  Id.equal basename1 basename2 && List.prefix_of Id.equal dir1 dir2

let string_of_qualid qid = string_of_path qid.CAst.v
let pr_qualid qid = pr_path qid.CAst.v

let qualid_of_string ?loc s = CAst.make ?loc @@ path_of_string s

let qualid_of_path ?loc sp = CAst.make ?loc sp
let qualid_of_ident ?loc id = make_qualid ?loc DirPath.empty id
let qualid_of_dirpath ?loc dir =
  let (l,a) = split_dirpath dir in
  make_qualid ?loc l a

let qualid_of_lident lid = qualid_of_ident ?loc:lid.CAst.loc lid.CAst.v

let qualid_is_ident qid = DirPath.is_empty (dirpath qid.CAst.v)

let qualid_basename qid =
  qid.CAst.v.basename

let qualid_path qid =
  qid.CAst.v.dirpath

let idset_mem_qualid qid s =
  qualid_is_ident qid && Id.Set.mem (qualid_basename qid) s

(* Default paths *)

(*s Roots of the space of absolute names *)
let rocq_init_string = "Corelib"
let rocq_init_root = Id.of_string rocq_init_string
let default_root_prefix = DirPath.empty
