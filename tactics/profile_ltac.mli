val do_profile : string -> ('a * Proof_type.ltac_call_kind) list -> 'b Proofview.tactic -> 'b Proofview.tactic

val set_profiling : bool -> unit

val get_profiling : unit -> bool

val set_display_profile_at_close : bool -> unit

val entered_call : unit -> unit

val print_results : unit -> unit

val print_results_tactic : string -> unit

val reset_profile : unit -> unit

val do_print_results_at_close : unit -> unit
