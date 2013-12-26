(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* [check_vi tasks file] checks the [tasks] stored in [file] *)
val check_vi : int list * string -> unit

(* [schedule_vi_checking j files] prints [j] command lines to
 * be executed in parallel to check all tasks in [files] *)
val schedule_vi_checking : int -> string list -> unit
