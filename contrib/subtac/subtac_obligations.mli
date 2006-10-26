val add_entry : Names.identifier -> (Term.constr list -> Term.constr) -> Term.types -> (Names.identifier * Term.types) list -> unit

val subtac_obligation : int * Names.identifier option -> unit
