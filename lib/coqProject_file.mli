(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

exception Parsing_error of string

type arg_source = CmdLine | ProjectFile

type 'a sourced = { thing : 'a; source : arg_source }

type meta_file = Absent | Present of string | Generate of string

type project = {
  project_file  : string option;
  makefile : string option;
  native_compiler : native_compiler option;
  (* the installation path for installing project documentation (relative to
   * the user-contrib folder) *)
  docroot : string option;

  v_files : string sourced list;
  mli_files : string sourced list;
  mlg_files : string sourced list;
  ml_files : string sourced list;
  mllib_files : string sourced list;
  mlpack_files : string sourced list;
  meta_file : meta_file;

  ml_includes : path sourced list;
  r_includes  : (path * logic_path) sourced list;
  q_includes  : (path * logic_path) sourced list;
  extra_args : string sourced list;
  defs : (string * string) sourced list;
}
and logic_path = string
and path = { path : string; canonical_path : string }
and native_compiler =
| NativeYes
| NativeNo
| NativeOndemand

val cmdline_args_to_project : warning_fn:(string -> unit) -> curdir:string -> string list -> project

exception UnableToOpenProjectFile of string

val read_project_file : warning_fn:(string -> unit) -> string -> project
(** [read_project_file warning_fn file] parses [file] as a Coq project;
    use [warning_fn] for deprecate options;
    raise [Parsing_error] on illegal options or arguments;
    raise [UnableToOpenProjectFile msg] if the file could not be opened;
    fails on some illegal non-project-file options *)

val coqtop_args_from_project : project -> string list
val find_project_file : from:string -> projfile_name:string -> string option

val all_files : project -> string sourced list

val map_sourced_list : ('a -> 'b) -> 'a sourced list -> 'b list

(** Only uses the elements with source=CmdLine *)
val map_cmdline : ('a -> 'b) -> 'a sourced list -> 'b list

(** Only uses the elements with source=CmdLine *)
val filter_cmdline : 'a sourced list -> 'a list

val forget_source : 'a sourced -> 'a
