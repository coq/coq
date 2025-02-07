(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type native_compiler = Coq_config.native_compiler =
  NativeOff | NativeOn of { ondemand : bool }

type top = TopLogical of string | TopPhysical of string

type option_command =
  | OptionSet of string option
  | OptionUnset

type export_flag = Export | Import

type require_injection = { lib: string; prefix: string option; export: export_flag option; allow_failure: bool }
(** Parameters follow [Library], that is to say, [lib,prefix,export]
    means require library [lib] from optional [prefix] and import or
    export if [export] is [Some Lib.Import]/[Some Lib.Export]. *)

type injection_command =
  | OptionInjection of (string list * option_command)
  (** Set flags or options before the initial state is ready. *)
  | RequireInjection of require_injection
  (** Require libraries before the initial state is
      ready. *)
  | WarnNoNative of string
  (** Used so that "-w -native-compiler-disabled -native-compiler yes"
     does not cause a warning. The native option must be processed
     before injections (because it affects require), so the
     instruction to emit a message is separated. *)
  | WarnNativeDeprecated
  (** Used so that "-w -native-compiler-deprecated-option -native-compiler FLAG"
      does not cause a warning, similarly to above. *)

type coqargs_logic_config = {
  impredicative_set : bool;
  indices_matter    : bool;
  type_in_type      : bool;
  rewrite_rules     : bool;
  toplevel_name     : top;
}

type time_config = ToFeedback | ToFile of string

type coqargs_config = {
  logic       : coqargs_logic_config;
  rcfile      : string option;
  coqlib      : string option;
  enable_VM   : bool;
  native_compiler : native_compiler;
  native_output_dir : CUnix.physical_path;
  native_include_dirs : CUnix.physical_path list;
  output_directory : CUnix.physical_path option;
  exclude_dirs : CUnix.physical_path list;
  beautify : bool;
  quiet : bool;
  time : time_config option;
  test_mode : bool;
  profile : string option;
  print_emacs : bool;
}

type vo_path = {
  implicit : bool; (** true if -R, otherwise -Q *)
  unix_path : string;
  rocq_path : string;
}

type coqargs_pre = {
  boot        : bool;
  load_init   : bool;
  load_rcfile : bool;

  ml_includes : CUnix.physical_path list;
  vo_includes : vo_path list;

  load_vernacular_list : (string * bool) list;
  injections  : injection_command list;
}

type coqargs_main =
  | Queries of Boot.Usage.query list
  | Run

type coqargs_post = {
  memory_stat : bool;
}

type t = {
  config : coqargs_config;
  pre : coqargs_pre;
  main : coqargs_main;
  post : coqargs_post;
}

(* Default options *)
val default : t

val parse_args : init:t -> string list -> t * string list

val injection_commands : t -> injection_command list

(* Common utilities *)

val get_int : opt:string -> string -> int
val get_int_opt : opt:string -> string -> int option
val get_bool : opt:string -> string -> bool
val get_float : opt:string -> string -> float
val error_missing_arg : string -> 'a
val error_wrong_arg : string -> 'a
