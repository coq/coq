(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** {6 Prints the version number on the standard output. } *)

val version : unit -> unit
val machine_readable_version : unit -> unit

(** {6 extra arguments or options to print when asking usage for a
     given executable. } *)

type specific_usage = {
  executable_name : string;
  extra_args : string;
  extra_options : string;
}

(** {6 Prints the generic part and specific part of usage for a
       given executable. } *)

val print_usage : out_channel -> specific_usage -> unit

type query =
  | PrintWhere | PrintConfig
  | PrintVersion | PrintMachineReadableVersion
  | PrintHelp
