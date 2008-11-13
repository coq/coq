(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*s Prints the version number on the standard output and exits (with 0). *)

val version : unit -> 'a

(*s Prints the usage on the error output, preceeded by a user-provided message. *)
val print_usage : string -> unit

(*s Prints the usage on the error output. *)
val print_usage_coqtop : unit -> unit
val print_usage_coqc : unit -> unit

(*s Prints the configuration information *)
val print_config : unit -> unit
