
(* $Id$ *)
open Term
open Evd
open Environ

type metamap = (int * constr) list

val get_type_of : env -> 'a evar_map -> constr -> constr
val get_type_of_with_meta : env -> 'a evar_map -> metamap -> constr -> constr
val get_sort_of : env -> 'a evar_map -> constr -> sorts

