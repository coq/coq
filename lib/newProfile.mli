(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module MiniJson : sig
  (** Subtype of Yojson.Safe.t *)
  type t = [
    | `Intlit of string
    | `String of string
    | `Assoc of (string * t) list
    | `List of t list
  ]
end

val profile : string -> ?args:(unit -> (string * MiniJson.t) list) -> (unit -> 'a) -> unit -> 'a

val is_profiling : unit -> bool

type settings =
  { output : Format.formatter
  }

val init : settings -> unit

val finish : unit -> unit
