(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

exception Parsing_error of string

type project = {
  project_file  : string option;
  makefile : string option;
  install_kind  : install option;
  use_ocamlopt : bool;

  v_files : string list;
  mli_files : string list;
  ml4_files : string list;
  ml_files : string list;
  mllib_files : string list;
  mlpack_files : string list;

  ml_includes : path list;
  r_includes  : (path * logic_path) list;
  q_includes  : (path * logic_path) list;
  extra_args : string list;
  defs : (string * string) list;

  (* deprecated in favor of a Makefile.local using :: rules *)
  extra_targets : extra_target list;
  subdirs : string list;

}
and extra_target = {
  target : string;
  dependencies : string;
  phony : bool;
  command : string;
}
and logic_path = string
and path = { path : string; canonical_path : string }
and install =
  | NoInstall
  | TraditionalInstall
  | UserInstall

val cmdline_args_to_project : curdir:string -> string list -> project
val read_project_file : string -> project
val coqtop_args_from_project : project -> string list
val find_project_file : from:string -> projfile_name:string -> string option

