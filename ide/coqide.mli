(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* The CoqIde main module. The following function [start] will parse the
   command line, initialize the load path, load the input
   state, load the files given on the command line, load the ressource file,
   produce the output state if any, and finally will launch the interface. *)

(** The arguments that will be passed to coqtop. No quoting here, since
    no /bin/sh when using create_process instead of open_process. *)
val sup_args : string list ref

(** Filter the argv from the option -coqtop, and set
    Minilib.coqtop_path accordingly *)
val set_coqtop_path : string list -> string list

(** Ask coqtop the remaining options it doesn't recognize *)
val process_argv : string list -> string list

val do_load : string -> unit

val crash_save : int -> unit
val ignore_break : unit -> unit
val check_for_geoproof_input : unit -> unit
val main : string list -> unit
