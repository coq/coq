(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type compilation_mode = BuildVo
type color = [`ON | `AUTO | `OFF]

val default_toplevel : Names.DirPath.t

type coq_cmdopts = {

  load_init   : bool;
  load_rcfile : bool;
  rcfile      : string option;

  ml_includes : Mltop.coq_path list;
  vo_includes : Mltop.coq_path list;
  vo_requires : (string * string option * bool option) list;

  (* Fuse these two? Currently, [batch_mode] is only used to
     distinguish coqc / coqtop in help display. *)
  batch_mode : bool;
  compilation_mode : compilation_mode;

  toplevel_name : Stm.interactive_top;

  compile_list: (string * bool) list;  (* bool is verbosity  *)
  compilation_output_name : string option;

  load_vernacular_list : (string * bool) list;

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

  (* Quiet / verbosity options should be here *)

  inputstate  : string option;
  outputstate : string option;

}

(* Default options *)
val default_opts : coq_cmdopts

val parse_args : coq_cmdopts -> string list -> coq_cmdopts * string list
val exitcode : coq_cmdopts -> int

val require_libs : coq_cmdopts -> (string * string option * bool option) list
val build_load_path : coq_cmdopts -> Mltop.coq_path list
