(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Vmemitcodes

exception Faulty of string

(* TODO: share with Library *)

module Delayed :
sig

type 'a t
val make : file:string -> ObjFile.in_handle -> segment:'a ObjFile.id -> 'a t
val return : 'a -> 'a t
val eval : 'a t -> 'a

end =
struct

type 'a delayed = {
  del_file : string;
  del_off : int64;
  del_digest : Digest.t;
}

type 'a node = ToFetch of 'a delayed | Fetched of 'a

type 'a t = 'a node ref

let in_delayed f ch ~segment =
  let seg = ObjFile.get_segment ch ~segment in
  let digest = seg.ObjFile.hash in
  { del_file = f; del_digest = digest; del_off = seg.ObjFile.pos; }

let make ~file ch ~segment =
  let del = in_delayed file ch ~segment in
  ref (ToFetch del)

(** Fetching a table of opaque terms at position [pos] in file [f],
    expecting to find first a copy of [digest]. *)

let fetch_delayed del =
  let { del_digest = digest; del_file = f; del_off = pos; } = del in
  let ch = open_in_bin f in
  let obj, digest' =
    try
      let () = LargeFile.seek_in ch pos in
      let obj = System.marshal_in f ch in
      let digest' = Digest.input ch in
      obj, digest'
    with e -> close_in ch; raise e
  in
  close_in ch;
  if not (String.equal digest digest') then raise (Faulty f);
  obj

let eval r = match !r with
| Fetched v -> v
| ToFetch del ->
  let v = fetch_delayed del in
  let () = r := Fetched v in
  v

let return v = ref (Fetched v)

end

module VmTable =
struct

type t = {
  table_len : int;
  table_dir : DirPath.t;
  table_val : to_patch Int.Map.t;
}

type index = DirPath.t * int

let empty = {
  table_len = 0;
  table_dir = DirPath.dummy;
  table_val = Int.Map.empty;
}

let set_path dp tab =
  let () = assert (DirPath.equal tab.table_dir DirPath.dummy) in
  { tab with table_dir = dp }

let create code tab =
  let id = tab.table_len in
  let dp = tab.table_dir in
  let () = assert (not @@ DirPath.equal dp DirPath.dummy) in
  let table_val = Int.Map.add id code tab.table_val in
  let ntab = { table_dir = dp; table_len = id + 1; table_val } in
  ntab, (dp, id)

end

type compiled_library = {
  lib_dp : DirPath.t;
  lib_data : to_patch array;
}

type on_disk = DirPath.t * compiled_library Delayed.t

let inject lib =
  (lib.lib_dp, Delayed.return lib)

type t = {
  local : VmTable.t;
  foreign : compiled_library Delayed.t DPmap.t;
}

type index = VmTable.index

type indirect_code = VmTable.index pbody_code

let empty = {
  local = VmTable.empty;
  foreign = DPmap.empty;
}

let set_path dp lib =
  let local = VmTable.set_path dp lib.local in
  { lib with local }

let add code lib =
  let tab, idx = VmTable.create code lib.local in
  let lib = { lib with local = tab } in
  lib, idx

let vm_segment : compiled_library ObjFile.id = ObjFile.make_id "vmlibrary"

let load dp ~file ch =
  (dp, Delayed.make ~file ~segment:vm_segment ch : on_disk)

let link (dp, m) libs =
  let () = assert (not @@ DPmap.mem dp libs.foreign) in
  { libs with foreign = DPmap.add dp m libs.foreign }

let missing_index dp i =
  CErrors.anomaly Pp.(str "Missing VM index " ++ int i ++
    str " in library " ++ DirPath.print dp)

let resolve (dp, i) libs =
  if DirPath.equal dp libs.local.VmTable.table_dir then
    match Int.Map.find i libs.local.VmTable.table_val with
    | v -> v
    | exception Not_found -> missing_index dp i
  else match DPmap.find dp libs.foreign with
  | tab ->
    let tab = Delayed.eval tab in
    tab.lib_data.(i)
  | exception Not_found ->
    CErrors.anomaly Pp.(str "Missing VM table for library " ++
      DirPath.print dp)

let export lib =
  let local = lib.local in
  let init i = Int.Map.find i local.VmTable.table_val in
  let data = Array.init local.VmTable.table_len init in
  { lib_dp = local.VmTable.table_dir; lib_data = data }
