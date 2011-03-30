(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** * The CoqIde main module *)

(** The arguments that will be passed to coqtop. No quoting here, since
    no /bin/sh when using create_process instead of open_process. *)
val sup_args : string list ref

(** Filter the argv from the option -coqtop, and set
    Minilib.coqtop_path accordingly *)
val set_coqtop_path : string list -> string list

(** Ask coqtop the remaining options it doesn't recognize *)
val process_argv : string list -> string list

(** Prepare the widgets, load the given files in tabs *)
val main : string list -> unit

(** The function doing the actual loading of a file. *)
val do_load : string -> unit

(** Set coqide to ignore Ctrl-C, while launching [crash_save] and
    exiting for others received signals *)
val ignore_break : unit -> unit

(** Emergency saving of opened files as "foo.v.crashcoqide",
    and exit (if the integer isn't 127). *)
val crash_save : int -> unit

val check_for_geoproof_input : unit -> unit
