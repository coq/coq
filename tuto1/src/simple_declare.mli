open Names
open EConstr

val packed_declare_definition :
    poly:bool -> Id.t -> constr Evd.in_evar_universe_context -> unit
