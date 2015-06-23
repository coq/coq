val do_profile : string -> ('a * Proof_type.ltac_call_kind) list -> 'b Proofview.tactic -> 'b Proofview.tactic

val set_profiling : bool -> unit

val entered_call : unit -> unit

val print_results : unit -> unit

val print_results_tactic : string -> unit

val reset_profile : unit -> unit
