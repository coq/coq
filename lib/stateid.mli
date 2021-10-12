(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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
val print : t -> Pp.t

val of_int : int -> t
val to_int : t -> int

val newer_than : t -> t -> bool

(* Attaches to an exception the concerned state id, plus an optional
 * state id that is a valid state id before the error.
 * Backtracking to the valid id is safe. *)
val add : Exninfo.info -> valid:t -> t -> Exninfo.info
val get : Exninfo.info -> (t * t) option

type exn_info = { id : t; valid : t }

type ('a,'b) request = {
  exn_info : exn_info;
  stop : t;
  document : 'b;
  loc : Loc.t option;
  uuid     : 'a;
  name     : string
}

(* Asks the document manager if the given state is valid (or belongs to an
   old version of the document) *)
val is_valid : doc:int -> t -> bool

(* By default [is_valid] always answers true, but a document manager supporting
   undo operations like the STM can override this. *)
val set_is_valid : (doc:int -> t -> bool) -> unit
