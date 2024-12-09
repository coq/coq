(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let fatal_error fmt = Printf.kfprintf (fun _ -> exit 1) stderr (fmt^^"\n")

let error_usage () =
  fatal_error "Usage: rocq [-debug-shim] {-v|--version|NAME} [ARGUMENTS...]"

let with_worker opts kind args =
  Rocqshim.init opts args;
  let prog = Rocqshim.get_worker_path { package = "rocq-runtime"; basename = "coqworker" } in
  let () = if opts.debug_shim then Printf.eprintf "Using %s\n%!" prog in
  let argv = Array.of_list (prog :: ("--kind="^kind) :: args) in
  Rocqshim.exec_or_create_process prog argv

let () =
  if Array.length Sys.argv < 2 then error_usage ();

  let args = List.tl (Array.to_list Sys.argv) in
  let opts, args = Rocqshim.parse_opts args in
  match args with
  | "-v" :: _ | "--version" :: _ -> Boot.Usage.version ()
  | ("c" | "compile") :: args -> with_worker opts "compile" args
  | ("top"|"repl") :: args -> with_worker opts "repl" args
  | ("preprocess-mlg"|"pp-mlg") :: args -> Coqpp_main.main args
  | "dep" :: args -> Coqdeplib.Rocqdep_main.main args
  | "doc" :: args -> Coqdoclib.Rocqdoc_main.main ~prog:(Sys.argv.(0) ^ " doc") args

  | prog :: _ ->
    fatal_error "Unknown argument %s" prog
  | [] -> error_usage ()
