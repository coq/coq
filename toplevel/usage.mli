(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** {6 Prints the version number on the standard output and exits (with 0). } *)

val version : int -> 'a
val machine_readable_version : int -> 'a

(** {6 Prints the usage on the error output, preceeded by a user-provided message. } *)
val print_usage : string -> unit

(** {6 Enable toploop plugins to insert some text in the usage message. } *)
val add_to_usage : string -> string -> unit

(** {6 Prints the usage on the error output. } *)
val print_usage_coqtop : unit -> unit
val print_usage_coqc : unit -> unit

