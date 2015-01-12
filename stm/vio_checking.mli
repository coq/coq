(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* [check_vio tasks file] checks the [tasks] stored in [file] *)
val check_vio : int list * string -> bool
val schedule_vio_checking : int -> string list -> unit

val schedule_vio_compilation : int -> string list -> unit
