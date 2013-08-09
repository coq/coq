(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Xml_datatype

type state_id
val initial_state_id : state_id
val dummy_state_id : state_id
val fresh_state_id : unit -> state_id
val string_of_state_id : state_id -> string
val state_id_of_int : int -> state_id
val int_of_state_id : state_id -> int
val newer_than : state_id -> state_id -> bool

(* XML marshalling *)
val of_state_id : state_id -> xml
val to_state_id : xml -> state_id

(* Attaches to an exception the concerned state id, plus an optional
 * state id that is a valid state id before the error.
 * Backtracking to the valid id is safe.
 * The initial_state_id is assumed to be safe. *)
val add_state_id : exn -> ?valid:state_id -> state_id -> exn
val get_state_id : exn -> (state_id * state_id) option

module StateidOrderedType : Map.OrderedType with type t = state_id
