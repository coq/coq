(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
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

val same_char_locs : char_loc -> char_loc -> bool

type source_loc = {
  chars : char_loc;
  line : int;
  text : string;
}

val same_source_locs : source_loc -> source_loc -> bool

val combine_related_data : (string * (source_loc * 'a) array) array -> (source_loc * 'a array) array
(** Combine data from multiple files about the same source, ensuring
    that the locations do not have inconsistencies. *)
