(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val copy : string -> string -> unit

(** [files_from_file f] returns the list of file names contained in
   the file named [f]. These file names must be separated by spaces,
   tabulations or newlines. *)
val files_from_file : string -> string list

(** Version of [Sys.file_exists] but will exit on error *)
val check_if_file_exists : string -> unit
