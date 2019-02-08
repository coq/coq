(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type color = [`ON | `AUTO | `OFF]

val default_toplevel : Names.DirPath.t

type t = {

  boot : bool;

  load_init   : bool;
  load_rcfile : bool;
  rcfile      : string option;

  ml_includes : Mltop.coq_path list;
  vo_includes : Mltop.coq_path list;
  vo_requires : (string * string option * bool option) list;

  toplevel_name : Stm.interactive_top;

  load_vernacular_list : (string * bool) list;
  batch : bool;

  color : color;

  impredicative_set : Declarations.set_predicativity;
  indices_matter : bool;
  enable_VM : bool;
  enable_native_compiler : bool;
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
val build_load_path : t -> Mltop.coq_path list
