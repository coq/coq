(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type t

val equal : t -> t -> bool
val compare : t -> t -> int

module Self : Map.OrderedType with type t = t
module Set : Set.S with type elt = t and type t = Set.Make(Self).t

val initial : t
val dummy : t
val fresh : unit -> t
val to_string : t -> string

val of_int : int -> t
val to_int : t -> int

val newer_than : t -> t -> bool

(* Attaches to an exception the concerned state id, plus an optional
 * state id that is a valid state id before the error.
 * Backtracking to the valid id is safe. *)
val add : Exninfo.info -> valid:t -> t -> Exninfo.info
val get : Exninfo.info -> (t * t) option

type ('a,'b) request = {
  exn_info : t * t;
  stop : t;
  document : 'b;
  loc : Loc.t option;
  uuid     : 'a;
  name     : string
}

