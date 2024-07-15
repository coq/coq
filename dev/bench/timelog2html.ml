(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Benchlib

let die fmt = Printf.kfprintf (fun _ -> exit 1) stderr fmt

let usage () = die "Usage: %s VFILE TIMEFILES\n\n%a\n" Sys.argv.(0)
    (fun fmt len -> Printf.fprintf fmt "(1 to %d time files are supported.)" len)
    Htmloutput.max_data_count

let () = if Array.length Sys.argv < 3 ||
            Array.length Sys.argv > 2 + Htmloutput.max_data_count
  then  usage ()

let vfile = Sys.argv.(1)
let data_files = Array.sub Sys.argv 2 (Array.length Sys.argv - 2)

let source = BenchUtil.read_whole_file vfile

let file_data data_file =
  let data = Timelogparser.parse ~file:data_file in
  data_file, CArray.of_list data

let all_data = Array.map file_data data_files

let all_data = BenchUtil.combine_related_data all_data

let dummy = Array.make (Array.length data_files) BenchUtil.dummy_measure

let all_data = Array.of_list (Sourcehandler.join_to_source ~dummy ~source (Array.to_list all_data))

let vname = Filename.basename vfile

let () = Htmloutput.output stdout ~vname ~data_files all_data
