open Util

val add_entry : Names.identifier -> Term.constr -> Term.types ->
  (Names.identifier * Term.types * Intset.t) array -> unit

val subtac_obligation : int * Names.identifier option -> unit

val solve_obligations : Names.identifier option -> Proof_type.tactic -> unit

val show_obligations : Names.identifier option -> unit
