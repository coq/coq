
(* $Id$ *)

open Names
open Term
open Environ

val instantiate_constr : 
  identifier list -> constr -> constr list -> constr
val instantiate_type : 
  identifier list -> typed_type -> constr list -> typed_type

val constant_value : 'a unsafe_env -> constr -> constr
val constant_type : 'a unsafe_env -> constr -> typed_type

val const_or_ex_value : 'a unsafe_env -> constr -> constr
val const_or_ex_type : 'a unsafe_env -> constr -> constr

val const_abst_opt_value : 'a unsafe_env -> constr -> constr option
