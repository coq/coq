
(* $Id$ *)

(*i*)
open Pp
open Names
open Term
open Sign
open Environ
(*i*)

val error_unbound_rel : path_kind -> 'a unsafe_env -> int -> 'b

val error_cant_execute : path_kind -> 'a unsafe_env -> constr -> 'b

val error_not_type : path_kind -> 'a unsafe_env -> constr -> 'b

val error_assumption : path_kind -> 'a unsafe_env -> constr -> 'b
 
val error_reference_variables : identifier -> 'a

val error_elim_expln : 'a unsafe_env -> constr -> constr -> string

val error_elim_arity : 
  path_kind -> 'a unsafe_env -> constr -> constr list -> constr 
    -> constr -> constr -> (constr * constr * string) option -> 'b

val error_case_not_inductive : 
  path_kind -> 'a unsafe_env -> constr -> constr -> 'b

val error_number_branches : 
  path_kind -> 'a unsafe_env -> constr -> constr -> int -> 'b

val error_ill_formed_branch :
  path_kind -> 'a unsafe_env -> constr -> int -> constr -> constr -> 'b

val error_generalization :
  path_kind -> 'a unsafe_env -> name * typed_type -> constr -> 'b

val error_actual_type :
  path_kind -> 'a unsafe_env -> unsafe_judgment -> unsafe_judgment -> 'b

val error_cant_apply : 
  string -> path_kind -> 'a unsafe_env -> unsafe_judgment 
    -> unsafe_judgment list -> 'b

val error_ill_formed_rec_body :
  std_ppcmds -> path_kind -> 'a unsafe_env 
    -> name list -> int -> constr array -> 'b

val error_ill_typed_rec_body  :
  path_kind -> 'a unsafe_env -> int -> name list -> unsafe_judgment array 
    -> typed_type array -> 'b

