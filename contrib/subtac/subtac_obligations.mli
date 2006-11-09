open Util

type obligation_info = (Names.identifier * Term.types * Intset.t) array

val add_definition : Names.identifier ->  Term.constr -> Term.types -> 
  obligation_info -> unit

val add_mutual_definitions : 
  (Names.identifier * Term.constr * Term.types * obligation_info) list -> unit

val subtac_obligation : int * Names.identifier option -> unit

val solve_obligations : Names.identifier option -> Proof_type.tactic -> unit

val show_obligations : Names.identifier option -> unit
