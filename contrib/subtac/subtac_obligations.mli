open Util

type obligation_info = (Names.identifier * Term.types * bool * Intset.t) array
    (* ident, type, opaque or transparent, dependencies *)

val set_default_tactic : Tacexpr.glob_tactic_expr -> unit

val add_definition : Names.identifier ->  Term.constr -> Term.types -> 
  obligation_info -> unit

val add_mutual_definitions : 
  (Names.identifier * Term.constr * Term.types * obligation_info) list -> int array -> unit

val subtac_obligation : int * Names.identifier option * Topconstr.constr_expr option -> unit

val next_obligation : Names.identifier option -> unit

val solve_obligations : Names.identifier option -> Proof_type.tactic -> unit

val show_obligations : Names.identifier option -> unit

val admit_obligations : Names.identifier option -> unit
