(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* [check_vio tasks file] checks the [tasks] stored in [file] *)
val check_vio : int list * string -> bool
val schedule_vio_checking : int -> string list -> unit

val schedule_vio_compilation : int -> string list -> unit
