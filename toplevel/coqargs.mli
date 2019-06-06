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

type t = {

  load_init   : bool;
  load_rcfile : bool;
  rcfile      : string option;

  ml_includes : Loadpath.coq_path list;
  vo_includes : Loadpath.coq_path list;
  vo_requires : (string * string option * bool option) list;

  toplevel_name : Stm.interactive_top;

  load_vernacular_list : (string * bool) list;
  batch : bool;

  color : color;

  impredicative_set : Declarations.set_predicativity;
  indices_matter : bool;
  enable_VM : bool;
  native_compiler : native_compiler;
  allow_sprop : bool;
  cumulative_sprop : bool;

  set_options : (Goptions.option_name * option_command) list;

  stm_flags   : Stm.AsyncOpts.stm_opt;
  debug       : bool;
  diffs_set   : bool;
  time        : bool;

  filter_opts : bool;

  glob_opt    : bool;

  memory_stat : bool;
  print_tags  : bool;
  print_where : bool;
  print_config: bool;
  output_context : bool;

  print_emacs : bool;

  inputstate  : string option;
}

(* Default options *)
val default : t

val parse_args : help:(unit -> unit) -> init:t -> string list -> t * string list
val exitcode : t -> int

val require_libs : t -> (string * string option * bool option) list
val build_load_path : t -> Loadpath.coq_path list
