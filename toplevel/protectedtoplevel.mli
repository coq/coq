(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Pp
(*i*)

(* A protected toplevel (used in Pcoq). *)

val break_happened : bool ref
val global_request_id : int ref
val output_results_nl : std_ppcmds -> unit
val rearm_break : unit -> unit
val check_break : unit -> unit
val set_acknowledge_command : (int -> int -> exn option -> std_ppcmds) -> unit
val set_start_marker : string -> unit
val set_end_marker : string -> unit
val parse_one_command_group : in_channel -> unit
val protected_loop : in_channel -> unit
