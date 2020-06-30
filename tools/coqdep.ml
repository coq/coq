(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Format
open Minisys
open Coqdep_common

(** The basic parts of coqdep (i.e. the parts used by [coqdep -boot])
    are now in [Coqdep_common]. The code that remains here concerns
    the other options. Calling this complete coqdep with the [-boot]
    option should be equivalent to calling [coqdep_boot].

    As of today, this module depends on the following Coq modules:

    - Envars
    - CoqProject_file

    All of it for `coqlib` handling. Ideally we would like to clean
    coqlib handling up so this can be bootstrapped earlier.
*)

let option_sort = ref false

let usage () =
  eprintf " usage: coqdep [options] <filename>+\n";
  eprintf " options:\n";
  eprintf "  -boot : For coq developers, prints dependencies over coq library files (omitted by default).\n";
  eprintf "  -sort : output the given file name ordered by dependencies\n";
  eprintf "  -noglob | -no-glob : \n";
  eprintf "  -f file : read -I, -Q, -R and filenames from _CoqProject-formatted FILE.";
  eprintf "  -I dir : add (non recursively) dir to ocaml path\n";
  eprintf "  -R dir logname : add and import dir recursively to coq load path under logical name logname\n";
  eprintf "  -Q dir logname : add (recursively) and open (non recursively) dir to coq load path under logical name logname\n";
  eprintf "  -vos : also output dependencies about .vos files\n";
  eprintf "  -exclude-dir dir : skip subdirectories named 'dir' during -R/-Q search\n";
  eprintf "  -coqlib dir : set the coq standard library directory\n";
  eprintf "  -dyndep (opt|byte|both|no|var) : set how dependencies over ML modules are printed\n";
  exit 1

let split_period = Str.split (Str.regexp (Str.quote "."))

let add_q_include path l = add_rec_dir_no_import add_known path (split_period l)
let add_r_include path l = add_rec_dir_import add_known path (split_period l)

let treat_coqproject f =
  let open CoqProject_file in
  let iter_sourced f = List.iter (fun {thing} -> f thing) in
  let warning_fn x = coqdep_warning "%s" x in
  let project = read_project_file ~warning_fn f in
  iter_sourced (fun { path } -> add_caml_dir path) project.ml_includes;
  iter_sourced (fun ({ path }, l) -> add_q_include path l) project.q_includes;
  iter_sourced (fun ({ path }, l) -> add_r_include path l) project.r_includes;
  iter_sourced (fun f -> treat_file None f) (all_files project)

let rec parse = function
  | "-boot" :: ll -> option_boot := true; parse ll
  | "-sort" :: ll -> option_sort := true; parse ll
  | "-vos" :: ll -> write_vos := true; parse ll
  | ("-noglob" | "-no-glob") :: ll -> option_noglob := true; parse ll
  | "-f" :: f :: ll -> treat_coqproject f; parse ll
  | "-I" :: r :: ll -> add_caml_dir r; parse ll
  | "-I" :: [] -> usage ()
  | "-R" :: r :: ln :: ll -> add_r_include r ln; parse ll
  | "-Q" :: r :: ln :: ll -> add_q_include r ln; parse ll
  | "-R" :: ([] | [_]) -> usage ()
  | "-exclude-dir" :: r :: ll -> System.exclude_directory r; parse ll
  | "-exclude-dir" :: [] -> usage ()
  | "-coqlib" :: r :: ll -> Envars.set_user_coqlib r; parse ll
  | "-coqlib" :: [] -> usage ()
  | "-dyndep" :: "no" :: ll -> option_dynlink := No; parse ll
  | "-dyndep" :: "opt" :: ll -> option_dynlink := Opt; parse ll
  | "-dyndep" :: "byte" :: ll -> option_dynlink := Byte; parse ll
  | "-dyndep" :: "both" :: ll -> option_dynlink := Both; parse ll
  | "-dyndep" :: "var" :: ll -> option_dynlink := Variable; parse ll
  | ("-h"|"--help"|"-help") :: _ -> usage ()
  | f :: ll -> treat_file None f; parse ll
  | [] -> ()

(* Exception to be raised by Envars *)
exception CoqlibError of string

let coqdep () =
  if Array.length Sys.argv < 2 then usage ();
  if not Coq_config.has_natdynlink then option_dynlink := No;
  parse (List.tl (Array.to_list Sys.argv));
  (* Add current dir with empty logical path if not set by options above. *)
  (try ignore (Coqdep_common.find_dir_logpath (Sys.getcwd()))
   with Not_found -> add_norec_dir_import add_known "." []);
  (* We don't setup any loadpath if the -boot is passed *)
  if not !option_boot then begin
    Envars.set_coqlib ~fail:(fun msg -> raise (CoqlibError msg));
    let coqlib = Envars.coqlib () in
    add_rec_dir_import add_coqlib_known (coqlib//"theories") ["Coq"];
    add_rec_dir_import add_coqlib_known (coqlib//"plugins") ["Coq"];
    let user = coqlib//"user-contrib" in
    if Sys.file_exists user then add_rec_dir_no_import add_coqlib_known user [];
    List.iter (fun s -> add_rec_dir_no_import add_coqlib_known s [])
      (Envars.xdg_dirs ~warn:(fun x -> coqdep_warning "%s" x));
    List.iter (fun s -> add_rec_dir_no_import add_coqlib_known s []) Envars.coqpath;
  end;
  if !option_sort then begin sort (); exit 0 end;
  coq_dependencies ();
  ()

let _ =
  try
    coqdep ()
  with CoqlibError msg ->
    eprintf "*** Error: %s@\n%!" msg;
    exit 1
