
(* $Id$ *)
open Term
open Evd
open Environ

val get_type_of : env -> 'a evar_map -> constr -> constr
val get_sort_of : env -> 'a evar_map -> constr -> sorts

