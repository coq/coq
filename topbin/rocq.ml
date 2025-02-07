(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let fatal_error fmt = Printf.kfprintf (fun _ -> exit 1) stderr (fmt^^"%!")

let with_worker_gen opts ?(package="rocq-runtime") basename args =
  Rocqshim.init opts args;
  let prog = Rocqshim.get_worker_path { package; basename } in
  let () = if opts.debug_shim then Printf.eprintf "Using %s\n%!" prog in
  let argv = Array.of_list (prog :: args) in
  Rocqshim.exec_or_create_process prog argv

let with_worker opts kind args =
  with_worker_gen opts "rocqworker" (("--kind="^kind) :: args)

let with_sibling_exe opts prog args =
  let prog = System.get_toplevel_path prog in
  let () = if opts.Rocqshim.debug_shim then Printf.eprintf "Using %s\n%!" prog in
  let argv = Array.of_list (prog :: args) in
  Rocqshim.exec_or_create_process prog argv

type subcommand =
  | Compile
  | Repl
  | ReplWithDrop
  | NativePrecompile
  | Check
  | Votour
  | PpMlg
  | Dep
  | Doc
  | Wc
  | Workmgr
  | Tex
  | Makefile
  | Timelog2Html

let subcommands = [
  ("compile", "Compile a Rocq source file", Compile);
  ("c", "Alias for compile", Compile);
  ("repl", "Interactive read-eval-print loop", Repl);
  ("top", "Alias for repl", Repl);
  ("repl-with-drop", "repl with Drop command", ReplWithDrop);
  ("top-with-drop", "Alias for repl-with-drop", ReplWithDrop);
  ("native-precompile", "Preprocess a compiled Rocq file for use by native_compute", NativePrecompile);
  ("check", "Check a compiled Rocq file (alias for command rocqchk)", Check);
  ("votour", "Low level debugging of compiled files", Votour);
  ("preprocess-mlg", "Preprocess Rocq grammar files (.mlg) to produce OCaml sources", PpMlg);
  ("pp-mlg", "Alias for preprocess-mlg", PpMlg);
  ("dep", "Print dependencies for compiling Rocq files", Dep);
  ("doc", "Generate documentation from a Rocq source file", Doc);
  ("wc", "Count lines of code in a Rocq source file", Wc);
  ("workmgr", "Control the number of parallel workers used by Rocq", Workmgr);
  ("tex", "Process Rocq code in a Latex document", Tex);
  ("makefile", "Generate a Makefile to compile a Rocq project", Makefile);
  ("timelog2html", "Combine timing information and a Rocq source file", Timelog2Html);
]

let print_usage fmt () =
  let longest_subcmd =
    List.fold_left (fun acc (cmd,_,_) -> max acc (String.length cmd)) 0 subcommands
  in
  let subcommands =
    List.map (fun (cmd,doc,_) ->
        let separator = String.make (3 + longest_subcmd - String.length cmd) ' ' in
        "    "^cmd^separator^doc)
      subcommands
  in
  Printf.fprintf fmt "Usage: rocq [-debug-shim] {-v|--version|--print-version|--help|SUBCOMMAND} [ARGUMENTS...]\n\
\n  -v, --version: print human readable version info\
\n  --print-version: print machine readable version info\
\n\n\
Supported subcommands:\n\n\
%s\n\
\n\
Use \"rocq subcommand --help\" to get more information about a given subcommand.\n" (String.concat "\n" subcommands)

let error_usage () =
  fatal_error "%a" print_usage ()

let run_subcommand opts args = function
  | Compile -> with_worker opts "compile" args
  | Repl -> with_worker opts "repl" args
  | ReplWithDrop -> with_worker_gen opts "rocqworker_with_drop" args
  | NativePrecompile -> with_worker_gen opts "rocqnative" args
  | Check -> with_sibling_exe opts "rocqchk" args
  | Votour -> with_sibling_exe opts "votour" args
  | PpMlg -> Coqpp_main.main args
  | Dep -> Coqdeplib.Rocqdep_main.main args
  | Doc -> Coqdoclib.Rocqdoc_main.main ~prog:(Sys.argv.(0) ^ " doc") args
  | Wc -> Rocqwc.main args
  | Workmgr -> Rocqworkmgr.main ~prog:(Sys.argv.(0) ^ " workmgr") args
  | Tex -> Rocqtex.main ~prog:(Sys.argv.(0) ^ " tex") args
  | Makefile -> Rocqmakefile.main ~prog:[Sys.argv.(0); "makefile"] args
  | Timelog2Html -> with_worker_gen opts ~package:"rocq-devtools" "timelog2html" args

let () =
  if Array.length Sys.argv < 2 then error_usage ();

  let args = List.tl (Array.to_list Sys.argv) in
  let opts, args = Rocqshim.parse_opts args in
  match args with
  (* help prints *)
  | ("-h" | "-H" | "-help" | "--help") :: _ ->
    Printf.printf "%a%!" print_usage ();
    exit 0

  | cmd :: args ->
    begin match List.find_opt (fun (cmd',_,_) -> String.equal cmd cmd') subcommands with
    | Some (_,_,cmd) -> run_subcommand opts args cmd
    | None ->
      if Rocqshim.try_run_queries opts (cmd::args) then ()
      else fatal_error "Unknown subcommand %s\n%a%!" cmd print_usage ()
    end

  | [] -> error_usage ()
