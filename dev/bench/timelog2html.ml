(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let die fmt = Printf.kfprintf (fun _ -> exit 1) stderr (fmt^^"\n%!")

let usage () = die "Usage: rocq timelog2html [options] VFILE DATAFILES\n\n%a\n%s"
    (fun fmt len -> Printf.fprintf fmt "1 to %d data files are supported." len)
    Htmloutput.max_data_count
    "Data files may be .json or .json.gz profile files (as produced by rocq c -profile),\
     \nor timing files (as produced by rocq c -time-file).\
     \n\
     \nOptions:\
     \n  -o FILE: output to FILE (default is - meaning stdout)\
     \n  -raw-time-o FILE: output machine readable timing data to FILE\
     \n                    (default off, - means stdout)\
     \n                    (only supported with 2 data files; cannot be combined with\
     \n                     -raw-instr-o)\
     \n  -raw-instr-o FILE: output machine readable instruction data to FILE\
     \n                     (default off, - means stdout)\
     \n                     (only supported with 2 data files; cannot be combined with\
     \n                      -raw-time-o)\
     \n  -min-diff DIFF: in -raw-o, only output lines with time diff greater than DIFF\
     \n                  (DIFF in OCaml float format, default 1e-4)"

let parse_files = function
  | [] | [_] -> usage ()
  | vfile :: data_files ->
    let data_files = Array.of_list data_files in
    let () = if Array.length data_files > Htmloutput.max_data_count
      then usage ()
    in
    vfile, data_files

type output = Stdout | File of string

type opts = {
  output : output;
  raw_time_output : output option;
  raw_instr_output : output option;
  min_diff : Q.t;
}

let defaults = {
  output = Stdout;
  raw_time_output = None;
  raw_instr_output = None;
  min_diff = Q.(one / of_int 10_000);
}

let with_output f out =
  match out with
  | Stdout -> f stdout
  | File fname ->
    let ch = open_out fname in
    Fun.protect ~finally:(fun () -> close_out ch) (fun () -> f ch)

let parse_output = function
  | "-" -> Stdout
  | f -> File f

let parse_min_diff d =
  try Q.of_float @@ float_of_string d
  with Failure _ -> usage ()

let rec parse_args opts = function
  | "-o" :: f :: args -> parse_args { opts with output = parse_output f } args
  | ("-raw-time-o" :: f :: args
     | "-raw-instr-o" :: f :: args) when opts.raw_time_output != None ->
    die "Cannot use -raw-time-o and -raw-instr-o together"
  | "-raw-time-o" :: f :: args -> parse_args { opts with raw_time_output = Some (parse_output f) } args
  | "-raw-instr-o" :: f :: args -> parse_args { opts with raw_instr_output = Some (parse_output f) } args
  | "-min-diff" :: d :: args -> parse_args { opts with min_diff = parse_min_diff d } args
  | ["-o"|"-raw-o"|"-min-diff"] -> usage()
  | args -> opts, parse_files args

let file_data data_file =
  if List.exists (fun suf -> CString.is_suffix suf data_file) [".json"; ".json.gz"] then
    let data = Profparser.parse ~file:data_file in
    data_file, CArray.of_list data
  else
    let data = Timelogparser.parse ~file:data_file in
    data_file, data |> CArray.map_of_list (fun (loc, time) -> loc, { BenchUtil.dummy_data with time; })

let main args =
  let opts, (vfile, data_files) = parse_args defaults args in

  let source = BenchUtil.read_whole_file vfile in

  let all_data = Array.map file_data data_files in

  let all_data = BenchUtil.combine_related_data all_data in

  let dummy = Array.make (Array.length data_files) BenchUtil.dummy_data in

  let all_data = Array.of_list (Sourcehandler.join_to_source ~dummy ~source (Array.to_list all_data)) in

  let vname = Filename.basename vfile in

  let () = opts.raw_time_output |> Option.iter @@ with_output @@ fun ch ->
    let selection = Htmloutput.(Time {min_diff=opts.min_diff}) in
    Htmloutput.raw_output ch ~selection all_data
  in
  let () = opts.raw_instr_output |> Option.iter @@ with_output @@ fun ch ->
    (* we roughly convert the specified minimal time to a minimal instruction count *)
    let min_diff =  Q.(to_int (opts.min_diff * of_int 6_000_000_000)) in
    let selection = Htmloutput.(Instr {min_diff}) in
    Htmloutput.raw_output ch ~selection all_data
  in
  let () =  opts.output |> with_output @@ fun ch ->
    Htmloutput.output ch ~vname ~data_files all_data
  in
  ()
