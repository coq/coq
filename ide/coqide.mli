(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** * The CoqIde main module *)

(** The arguments that will be passed to coqtop. No quoting here, since
    no /bin/sh when using create_process instead of open_process. *)
val sup_args : string list ref

(** In debug mode under win32, messages are written to a log file *)
val logfile : string option ref

(** Filter the argv from coqide specific options, and set
    Minilib.coqtop_path accordingly *)
val read_coqide_args : string list -> string list

(** Prepare the widgets, load the given files in tabs *)
val main : string list -> unit

(** Function to save anything and kill all coqtops
    @return [false] if you're allowed to quit. *)
val forbid_quit : unit -> bool

(** Terminate coqide after closing all coqtops and waiting
    for their death *)
val close_and_quit : unit -> unit

(** Function to load of a file. *)
val do_load : string -> unit

(** Set coqide to perform a clean quit at Ctrl-C, while launching
    [crash_save] and exiting for others received signals *)
val set_signal_handlers : unit -> unit

(** Emergency saving of opened files as "foo.v.crashcoqide",
    and exit (if the integer isn't 127). *)
val crash_save : int -> unit

val check_for_geoproof_input : unit -> unit
