
(* $Id$ *)

(*i*)
open Names
open Term
open Evd
open Sign
open Environ
(*i*)

(* Instantiation of constants and inductives on their real arguments. *)

val instantiate_constr : 
  named_context -> constr -> constr list -> constr
val instantiate_type : 
  named_context -> typed_type -> constr list -> typed_type

(*s [constant_value env c] raises [NotEvaluableConst Opaque] if
   [c] is opaque and [NotEvaluableConst NoBody] if it has no
   body and [Not_found] if it does not exist in [env] *)

type const_evaluation_result = NoBody | Opaque
exception NotEvaluableConst of const_evaluation_result

val constant_value : env -> constant -> constr
val constant_type : env -> 'a evar_map -> constant -> typed_type
val constant_opt_value : env -> constant -> constr option

(*s [existential_value sigma ev] raises [NotInstantiatedEvar] if [ev] has
no body and [Not_found] if it does not exist in [sigma] *)

exception NotInstantiatedEvar
val existential_value : 'a evar_map -> existential -> constr
val existential_type : 'a evar_map -> existential -> constr
val existential_opt_value : 'a evar_map -> existential -> constr option
