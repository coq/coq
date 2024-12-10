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

let with_worker_gen opts basename args =
  Rocqshim.init opts args;
  let prog = Rocqshim.get_worker_path { package = "rocq-runtime"; basename } in
  let () = if opts.debug_shim then Printf.eprintf "Using %s\n%!" prog in
  let argv = Array.of_list (prog :: args) in
  Rocqshim.exec_or_create_process prog argv

let with_worker opts kind args =
  with_worker_gen opts "coqworker" (("--kind="^kind) :: args)

let () =
  if Array.length Sys.argv < 2 then error_usage ();

  let args = List.tl (Array.to_list Sys.argv) in
  let opts, args = Rocqshim.parse_opts args in
  match args with
  (* help prints *)
  | "-v" :: _ | "--version" :: _ -> Boot.Usage.version ()

  (* workers *)
  | ("c" | "compile") :: args -> with_worker opts "compile" args
  | ("top"|"repl") :: args -> with_worker opts "repl" args
  | ("top-with-drop"|"repl-with-drop") :: args -> with_worker_gen opts "coqworker_with_drop" args
  | "native-precompile" :: args -> with_worker_gen opts "rocqnative" args

  (* statically linked subcommands *)
  | ("preprocess-mlg"|"pp-mlg") :: args -> Coqpp_main.main args
  | "dep" :: args -> Coqdeplib.Rocqdep_main.main args
  | "doc" :: args -> Coqdoclib.Rocqdoc_main.main ~prog:(Sys.argv.(0) ^ " doc") args
  | "wc" :: args -> Rocqwc.main args
  | "workmgr" :: args -> Rocqworkmgr.main ~prog:(Sys.argv.(0) ^ " workmgr") args
  | "tex" :: args -> Rocqtex.main ~prog:(Sys.argv.(0) ^ " tex") args
  | "makefile" :: args -> Rocqmakefile.main ~prog:[Sys.argv.(0); "makefile"] args
  | "timelog2html" :: args -> Benchlib.Timelog2html.main ~prog:(Sys.argv.(0) ^ " timelog2html") args

  | prog :: _ ->
    fatal_error "Unknown argument %s" prog
  | [] -> error_usage ()
