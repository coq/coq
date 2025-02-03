(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type worker = {
  package : string;
  basename : string;
}

(** Find the executable for the given worker. [init] must have been called.
    [byte] defaults to whether the current executable is byte compiled. *)
val get_worker_path : worker -> string

type opts = { debug_shim : bool }

val parse_opts : string list -> opts * string list

(** Initialize environment and search paths. *)
val init : opts -> string list -> unit

(** Returns whether there are queries in the argument list, and if there are print their output.
    Does not handle PrintHelp queries. *)
val try_run_queries : opts -> string list -> bool

(** On windows [Unix.execv] creates a new process and exits this one.
    This confuses dune into thinking we are done,
    so instead we create_process and wait for it. *)
val exec_or_create_process : string -> string array -> 'a
