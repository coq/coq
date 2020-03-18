(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type t = {
  int : string;  (** \[0-9\]\[0-9_\]* *)
  frac : string;  (** empty or \[0-9_\]+ *)
  exp : string  (** empty or \[eE\]\[+-\]?\[0-9\]\[0-9_\]* *)
}

val equal : t -> t -> bool

(** [int s] amounts to [\{ int = s; frac = ""; exp = "" \}] *)
val int : string -> t

val to_string : t -> string

val of_string : string -> t option

(** Precondition: the first char on the stream is a digit (\[0-9\]).
    Precondition: at least two extra chars after the numeral to parse. *)
val parse : char Stream.t -> t
