
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
val acknowledge_command : int -> std_ppcmds
val set_start_marker : string -> unit
val set_end_marker : string -> unit
val parse_one_command : in_channel -> unit
val protected_loop : in_channel -> unit
