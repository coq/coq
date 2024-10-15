(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type char_loc = {
  start_char : int;
  stop_char : int;
}

type source_loc = {
  chars : char_loc;
  line : int;
  text : string;
}

(** A measurement, with the original printed string and an exact rational representation *)
type measure = { str: string; q: Q.t; }

val dummy_measure : measure

val combine_related_data : (string * (char_loc * 'a) array) array -> (char_loc * 'a array) array
(** Combine data from multiple files about the same source, ensuring
    that the locations do not have inconsistencies. *)

val read_whole_file : string -> string
