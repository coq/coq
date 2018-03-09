(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

exception Parsing_error of string

type arg_source = CmdLine | ProjectFile

type 'a sourced = { thing : 'a; source : arg_source }

type project = {
  project_file  : string option;
  makefile : string option;
  install_kind  : install option;
  use_ocamlopt : bool;

  v_files : string sourced list;
  mli_files : string sourced list;
  ml4_files : string sourced list;
  ml_files : string sourced list;
  mllib_files : string sourced list;
  mlpack_files : string sourced list;

  ml_includes : path sourced list;
  r_includes  : (path * logic_path) sourced list;
  q_includes  : (path * logic_path) sourced list;
  extra_args : string sourced list;
  defs : (string * string) sourced list;

  (* deprecated in favor of a Makefile.local using :: rules *)
  extra_targets : extra_target sourced list;
  subdirs : string sourced list;
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

val all_files : project -> string sourced list

val map_sourced_list : ('a -> 'b) -> 'a sourced list -> 'b list

(** Only uses the elements with source=CmdLine *)
val map_cmdline : ('a -> 'b) -> 'a sourced list -> 'b list

(** Only uses the elements with source=CmdLine *)
val filter_cmdline : 'a sourced list -> 'a list

val forget_source : 'a sourced -> 'a
