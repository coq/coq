open Names
open Term
open Environ

val val_of_constr : env -> constr -> values 

val set_opaque_const      : kernel_name -> unit
val set_transparent_const : kernel_name -> unit
