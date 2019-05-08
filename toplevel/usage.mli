(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** {6 Prints the version number on the standard output. } *)

val version : unit -> unit
val machine_readable_version : unit -> unit

(** {6 [add_to_usage name extra_args extra_options] tell what extra
     arguments or options to print when asking usage for command [name]. } *)
val add_to_usage : string -> string -> string -> unit

(** {6 Prints the usage on the error output. } *)
val print_usage : string -> out_channel -> unit

