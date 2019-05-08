(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type color = [`ON | `AUTO | `EMACS | `OFF]

val default_toplevel : Names.DirPath.t

type native_compiler = NativeOff | NativeOn of { ondemand : bool }

type option_command = OptionSet of string option | OptionUnset

type coqargs_logic_config = {
  impredicative_set : Declarations.set_predicativity;
  indices_matter    : bool;
  toplevel_name     : Stm.interactive_top;
  allow_sprop       : bool;
  cumulative_sprop  : bool;
}

type coqargs_config = {
  logic       : coqargs_logic_config;
  rcfile      : string option;
  coqlib      : string option;
  color       : color;
  enable_VM   : bool;
  native_compiler : native_compiler;
  stm_flags   : Stm.AsyncOpts.stm_opt;
  debug       : bool;
  diffs_set   : bool;
  time        : bool;
  glob_opt    : bool;
  print_emacs : bool;
  set_options : (Goptions.option_name * option_command) list;
}

type coqargs_pre = {
  load_init   : bool;
  load_rcfile : bool;

  ml_includes : Loadpath.coq_path list;
  vo_includes : Loadpath.coq_path list;
  vo_requires : (string * string option * bool option) list;
  (* None = No Import; Some false = Import; Some true = Export *)

  load_vernacular_list : (string * bool) list;
  inputstate  : string option;
}

type coqargs_base_query =
  | PrintTags | PrintWhere | PrintConfig
  | PrintVersion | PrintMachineReadableVersion
  | PrintHelp of (unit -> unit)

type coqargs_queries = {
  queries : coqargs_base_query list;
  filteropts : string list option;
}

type coqargs_main =
  | Queries of coqargs_queries
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

val parse_args : help:(unit -> unit) -> init:t -> string list -> t * string list
val error_wrong_arg : string -> unit

val require_libs : t -> (string * string option * bool option) list
val build_load_path : t -> Loadpath.coq_path list
