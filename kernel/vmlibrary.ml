(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Vmemitcodes

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

type t = {
  local : VmTable.t;
  foreign : VmTable.t DPmap.t;
}

type index = VmTable.index

type indirect_code = VmTable.index pbody_code

type on_disk = VmTable.t

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

let link m libs =
  let dp = m.VmTable.table_dir in
  let () = assert (not @@ DPmap.mem dp libs.foreign) in
  { libs with foreign = DPmap.add dp m libs.foreign }

let resolve (dp, i) libs =
  let tab =
    if DirPath.equal dp libs.local.VmTable.table_dir then
      libs.local
    else match DPmap.find dp libs.foreign with
    | tab -> tab
    | exception Not_found ->
      CErrors.anomaly Pp.(str "Missing VM table for library " ++
        DirPath.print dp)
  in
  match Int.Map.find i tab.VmTable.table_val with
  | v -> v
  | exception Not_found ->
    CErrors.anomaly Pp.(str "Missing VM index " ++ int i ++
      str " in library " ++ DirPath.print dp)

let export lib =
  lib.local
