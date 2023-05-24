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
  type t =
    | String of string
    | Int of string (* string not int so that we can have large ints *)
    | Record of (string * t) list
    | Array of t list
end

val profile : string -> ?args:(unit -> MiniJson.t) -> (unit -> 'a) -> unit -> 'a

val is_profiling : unit -> bool

type settings =
  { file : string
  }

val init : settings option -> unit
