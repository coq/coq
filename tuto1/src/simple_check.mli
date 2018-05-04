val simple_check1 :
  EConstr.constr Evd.in_evar_universe_context -> EConstr.constr

val simple_check2 :
  EConstr.constr Evd.in_evar_universe_context -> Evd.evar_map * EConstr.constr

val simple_check3 :
  EConstr.constr Evd.in_evar_universe_context -> EConstr.constr