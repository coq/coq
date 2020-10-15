(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val create : name:string -> ?verbosity:int -> (unit -> Pp.t) -> unit

val get_debug_level : string -> int
val set_debug_levels : (string * int) list -> unit

val get_flags : unit -> string
val parse_flags : string -> (string * int) list option
