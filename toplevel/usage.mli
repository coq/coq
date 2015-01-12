(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** {6 Prints the version number on the standard output and exits (with 0). } *)

val version : int -> 'a

(** {6 Prints the usage on the error output, preceeded by a user-provided message. } *)
val print_usage : string -> unit

(** {6 Enable toploop plugins to insert some text in the usage message. } *)
val add_to_usage : string -> string -> unit

(** {6 Prints the usage on the error output. } *)
val print_usage_coqtop : unit -> unit
val print_usage_coqc : unit -> unit

(** {6 Prints the configuration information } *)
val print_config : unit -> unit
