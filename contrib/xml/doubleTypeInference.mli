type types = { synthesized : Term.types; expected : Term.types option; } 

val cprop : Names.kernel_name

val whd_betadeltaiotacprop :
  Environ.env -> Evd.evar_map -> Term.constr -> Term.constr

val double_type_of :
  Environ.env -> Evd.evar_map -> Term.constr -> Term.constr option ->
   types Acic.CicHash.t -> unit
