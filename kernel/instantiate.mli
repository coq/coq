
(* $Id$ *)

(*i*)
open Names
open Term
open Inductive
open Evd
open Environ
(*i*)

(* Instantiation of constants and inductives on their real arguments. *)

val instantiate_constr : 
  identifier list -> constr -> constr list -> constr
val instantiate_type : 
  identifier list -> typed_type -> constr list -> typed_type

val constant_value : unsafe_env -> constr -> constr
val constant_type : unsafe_env -> constr -> typed_type

val existential_value : 'a evar_map -> constr -> constr
val existential_type : 'a evar_map -> constr -> constr

val const_abst_opt_value : unsafe_env -> constr -> constr option

val mis_lc : unsafe_env -> mind_specif -> constr

