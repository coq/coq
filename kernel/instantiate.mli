(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Term
open Evd
open Sign
open Environ
(*i*)

(* Instantiation of constants and inductives on their real arguments. *)

val instantiate_constr : 
  section_context -> constr -> constr list -> constr

val instantiate_type : 
  section_context -> types -> constr list -> types

(*s [constant_value env c] raises [NotEvaluableConst Opaque] if
   [c] is opaque and [NotEvaluableConst NoBody] if it has no
   body and [Not_found] if it does not exist in [env] *)

type const_evaluation_result = NoBody | Opaque
exception NotEvaluableConst of const_evaluation_result

val constant_value : env -> constant -> constr
val constant_type : env -> 'a evar_map -> constant -> types
val constant_opt_value : env -> constant -> constr option

(*s [existential_value sigma ev] raises [NotInstantiatedEvar] if [ev] has
no body and [Not_found] if it does not exist in [sigma] *)

exception NotInstantiatedEvar
val existential_value : 'a evar_map -> existential -> constr
val existential_type : 'a evar_map -> existential -> constr
val existential_opt_value : 'a evar_map -> existential -> constr option

type evaluable_reference =
  | EvalConst of constant
  | EvalVar of identifier
  | EvalRel of int
  | EvalEvar of existential

val destEvalRef : constr -> evaluable_reference
val mkEvalRef : evaluable_reference -> constr
val isEvalRef : constr -> bool

val evaluable_reference : 'a evar_map -> env -> evaluable_reference -> bool

val reference_opt_value :
  'a evar_map -> env -> evaluable_reference -> constr option

(* This may raise NotEvaluable *)
exception NotEvaluable
val reference_value :   'a evar_map -> env -> evaluable_reference -> constr
