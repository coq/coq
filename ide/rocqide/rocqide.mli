(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * The RocqIDE main module *)

(** The arguments that will be passed to rocqtop. No quoting here, since
    no /bin/sh when using create_process instead of open_process. *)
val sup_args : string list ref

(** In debug mode under win32, messages are written to a log file *)
val logfile : string option ref

(** Filter the argv from rocqide specific options, and set
    Minilib.rocqtop_path accordingly *)
val read_rocqide_args : string list -> string list

(** Prepare the widgets, load the given files in tabs *)
val main : string list -> GWindow.window

(** Terminate rocqide after closing all rocqtops and waiting
    for their death *)
val close_and_quit : unit -> unit

(** Function to load of a file. *)
val do_load : string -> unit

(** Set rocqide to perform a clean quit at Ctrl-C, while launching
    [crash_save] and exiting for others received signals *)
val set_signal_handlers : ?parent:GWindow.window -> unit -> unit

(** Emergency saving of opened files as "foo.v.crashrocqide",
    and exit (if the integer isn't 127). *)
val crash_save : int -> unit
