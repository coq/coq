
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

type const_evaluation_error = NotDefinedConst | OpaqueConst
exception NotEvaluableConst of const_evaluation_error

(* [constant_value env c] raises [NotEvaluableConst OpaqueConst] if
   [c] is opaque and [NotEvaluableConst NotDefinedConst] if undefined *)
val constant_value : env -> constr -> constr
val constant_type : env -> 'a evar_map -> constant -> typed_type

val existential_value : 'a evar_map -> constr -> constr
val existential_type : 'a evar_map -> constr -> constr

val const_abst_opt_value : env -> 'a evar_map -> constr -> constr option
