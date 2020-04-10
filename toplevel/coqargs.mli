(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type color = [`ON | `AUTO | `EMACS | `OFF]

val default_toplevel : Names.DirPath.t

type native_compiler = NativeOff | NativeOn of { ondemand : bool }

type coqargs_logic_config = {
  impredicative_set : Declarations.set_predicativity;
  indices_matter    : bool;
  toplevel_name     : Stm.interactive_top;
}

type coqargs_config = {
  logic       : coqargs_logic_config;
  rcfile      : string option;
  coqlib      : string option;
  color       : color;
  enable_VM   : bool;
  native_compiler : native_compiler;
  native_output_dir : CUnix.physical_path;
  native_include_dirs : CUnix.physical_path list;
  stm_flags   : Stm.AsyncOpts.stm_opt;
  debug       : bool;
  time        : bool;
  print_emacs : bool;
}

type coqargs_pre = {
  boot        : bool;
  load_init   : bool;
  load_rcfile : bool;

  ml_includes : CUnix.physical_path list;
  vo_includes : Loadpath.vo_path list;

  load_vernacular_list : (string * bool) list;
  injections  : Stm.injection_command list;

  inputstate  : string option;
}

type coqargs_query =
  | PrintTags | PrintWhere | PrintConfig
  | PrintVersion | PrintMachineReadableVersion
  | PrintHelp of Usage.specific_usage

type coqargs_main =
  | Queries of coqargs_query list
  | Run

type coqargs_post = {
  memory_stat : bool;
  output_context : bool;
}

type t = {
  config : coqargs_config;
  pre : coqargs_pre;
  main : coqargs_main;
  post : coqargs_post;
}

(* Default options *)
val default : t

val parse_args : help:Usage.specific_usage -> init:t -> string list -> t * string list
val error_wrong_arg : string -> unit

val injection_commands : t -> Stm.injection_command list
val build_load_path : t -> CUnix.physical_path list * Loadpath.vo_path list
