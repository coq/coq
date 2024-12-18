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

let usage ~prog () = die "Usage: %s VFILE TIMEFILES\n\n%a\n" prog
    (fun fmt len -> Printf.fprintf fmt "(1 to %d time files are supported.)" len)
    Htmloutput.max_data_count

let parse_args ~prog = function
  | [] | [_] -> usage ~prog ()
  | vfile :: data_files ->
    let data_files = Array.of_list data_files in
    let () = if Array.length data_files > Htmloutput.max_data_count
      then usage ~prog ()
    in
    vfile, data_files

let file_data data_file =
  let data = Timelogparser.parse ~file:data_file in
  data_file, CArray.of_list data

let main ~prog args =
  let vfile, data_files = parse_args ~prog args in

  let source = BenchUtil.read_whole_file vfile in

  let all_data = Array.map file_data data_files in

  let all_data = BenchUtil.combine_related_data all_data in

  let dummy = Array.make (Array.length data_files) BenchUtil.dummy_measure in

  let all_data = Array.of_list (Sourcehandler.join_to_source ~dummy ~source (Array.to_list all_data)) in

  let vname = Filename.basename vfile in

  let () = Htmloutput.output stdout ~vname ~data_files all_data in
  ()
