(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let die fmt = Printf.kfprintf (fun _ -> exit 1) stderr fmt

let usage () = die "Usage: rocq timelog2html VFILE DATAFILES\n\n%a\n%s\n"
    (fun fmt len -> Printf.fprintf fmt "(1 to %d data files are supported.)" len)
    Htmloutput.max_data_count
    "Data files may JSON profile files (as produced by rocq c -profile) with extension .json,\
\nor timing files (as produced by rocq c -time-file)"

let parse_args = function
  | [] | [_] -> usage ()
  | vfile :: data_files ->
    let data_files = Array.of_list data_files in
    let () = if Array.length data_files > Htmloutput.max_data_count
      then usage ()
    in
    vfile, data_files

let file_data data_file =
  match Filename.extension data_file with
  | ".json" ->
    let data = Profparser.parse ~file:data_file in
    data_file, CArray.of_list data
  | _ ->
    let data = Timelogparser.parse ~file:data_file in
    data_file, CArray.of_list data

let main args =
  let vfile, data_files = parse_args args in

  let source = BenchUtil.read_whole_file vfile in

  let all_data = Array.map file_data data_files in

  let all_data = BenchUtil.combine_related_data all_data in

  let dummy = Array.make (Array.length data_files) BenchUtil.dummy_measure in

  let all_data = Array.of_list (Sourcehandler.join_to_source ~dummy ~source (Array.to_list all_data)) in

  let vname = Filename.basename vfile in

  let () = Htmloutput.output stdout ~vname ~data_files all_data in
  ()
