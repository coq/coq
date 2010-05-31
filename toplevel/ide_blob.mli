(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)


type 'a menu = 'a * (string * string) list

type goals =
  | Message of string
  | Goals of ((string menu) list * string menu) list

val reinit : unit -> unit

val init_stdout : unit -> unit

type 'a call

type 'a value =
  | Good of 'a
  | Fail of exn

val eval_call : 'a call -> 'a value

val raw_interp : string -> unit call

val interp : bool -> string -> int call

val rewind : int -> int call

val is_in_loadpath : string -> bool call

val make_cases : string -> string list list call

val current_status : string call

val current_goals : goals call

val read_stdout : string call

