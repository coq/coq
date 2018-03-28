(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* The file format is a header
 *     ("COQAUX%d %s %s\n" version hex_hash path)
 * followed by an arbitrary number of entries
 *     ("%d %d %s %S\n" loc_begin loc_end key value)  *)

open Filename

let version = 1

let oc = ref None

let aux_file_name_for vfile =
  dirname vfile ^ "/." ^ chop_extension(basename vfile) ^ ".aux"

let mk_absolute vfile =
  let vfile = CUnix.remove_path_dot vfile in
  if Filename.is_relative vfile then CUnix.correct_path vfile (Sys.getcwd ())
  else vfile

let start_aux_file ~aux_file:output_file ~v_file =
  let vfile = mk_absolute v_file in
  oc := Some (open_out output_file);
  Printf.fprintf (Option.get !oc) "COQAUX%d %s %s\n"
    version (Digest.to_hex (Digest.file vfile)) vfile

let stop_aux_file () =
  close_out (Option.get !oc);
  oc := None

let recording () = not (Option.is_empty !oc)

module H = Map.Make(struct type t = int * int let compare = compare end)
module M = Map.Make(String)
type data = string M.t
type aux_file = data H.t

let contents x = x

let empty_aux_file = H.empty

let get ?loc aux key = M.find key (H.find (Option.cata Loc.unloc (0,0) loc) aux)

let record_in_aux_at ?loc key v =
  Option.iter (fun oc ->
      match loc with
      | Some loc -> let i, j = Loc.unloc loc in
                    Printf.fprintf oc "%d %d %s %S\n" i j key v
      | None     -> Printf.fprintf oc "0 0 %s %S\n" key v
    ) !oc

let current_loc : Loc.t option ref = ref None

let record_in_aux_set_at ?loc () = current_loc := loc

let record_in_aux key v = record_in_aux_at ?loc:!current_loc key v

let set h loc k v =
  let m = try H.find loc h with Not_found -> M.empty in
  H.add loc (M.add k v m) h

let load_aux_file_for vfile =
  let vfile = mk_absolute vfile in
  let ret3 x y z = x, y, z in
  let ret4 x y z t = x, y, z, t in
  let h = ref empty_aux_file in
  let add loc k v = h := set !h loc k v in
  let aux_fname = aux_file_name_for vfile in
  try
    let ib = Scanf.Scanning.from_channel (open_in aux_fname) in
    let ver, hash, fname =
      Scanf.bscanf ib "COQAUX%d %s %s\n" ret3 in
    if ver <> version then raise (Failure "aux file version mismatch");
    if fname <> vfile then
      raise (Failure "aux file name mismatch");
    let only_dummyloc = Digest.to_hex (Digest.file vfile) <> hash in
    while true do
      let i, j, k, v = Scanf.bscanf ib "%d %d %s %S\n" ret4 in
      if not only_dummyloc || (i = 0 && j = 0) then add (i,j) k v;
    done;
    raise End_of_file
  with
  | End_of_file -> !h
  | Sys_error s | Scanf.Scan_failure s
  | Failure s | Invalid_argument s ->
    Flags.if_verbose Feedback.msg_info Pp.(str"Loading file "++str aux_fname++str": "++str s);
     empty_aux_file

let set ?loc h k v = set h (Option.cata Loc.unloc (0,0) loc) k v
