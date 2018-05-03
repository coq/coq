open Names
open EConstr

val packed_declare_definition :
    Id.t -> constr Evd.in_evar_universe_context -> unit