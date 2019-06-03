val simple_check1 :
  Environ.env -> Evd.evar_map -> EConstr.constr -> Evd.evar_map * EConstr.constr

val simple_check2 :
  Environ.env -> Evd.evar_map -> EConstr.constr -> EConstr.constr
