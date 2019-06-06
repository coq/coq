open Names

val declare_definition :
    poly:bool -> Id.t -> Evd.evar_map -> EConstr.t -> Names.GlobRef.t
