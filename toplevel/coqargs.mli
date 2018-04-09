(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type compilation_mode = BuildVo | BuildVio | Vio2Vo
type color = [`ON | `AUTO | `OFF]

type coq_cmdopts = {

  load_init   : bool;
  load_rcfile : bool;
  rcfile      : string option;

  ml_includes : string list;
  vo_includes : (string * Names.DirPath.t * bool) list;
  vo_requires : (string * string option * bool option) list;

  (* Fuse these two? Currently, [batch_mode] is only used to
     distinguish coqc / coqtop in help display. *)
  batch_mode : bool;
  compilation_mode : compilation_mode;

  toplevel_name : Names.DirPath.t;

  compile_list: (string * bool) list;  (* bool is verbosity  *)
  compilation_output_name : string option;

  load_vernacular_list : (string * bool) list;

  vio_checking: bool;
  vio_tasks   : (int list * string) list;
  vio_files   : string list;
  vio_files_j : int;

  color : color;

  impredicative_set : Declarations.set_predicativity;
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
  outputstate : string option;

}

val parse_args : string list -> coq_cmdopts * string list
val exitcode : coq_cmdopts -> int
