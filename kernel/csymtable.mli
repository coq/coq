open Names
open Term
open Pre_env

val val_of_constr : env -> constr -> values

val set_opaque_const      : constant -> unit
val set_transparent_const : constant -> unit
