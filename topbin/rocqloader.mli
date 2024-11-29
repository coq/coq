(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Initialize environment and search paths, returning the arguments
    not consumed to produce the [opts]. *)
val init : string list -> string list

(** Print a message to stderr if debugging the loader is on. *)
val ppdebug : ('a, out_channel, unit) format -> 'a

(** Load plugin given by the findlib name and run with given arguments. *)
val load_and_run : string -> string list -> unit
