(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Pp
open Names
open Term
open Univ
open Sign
open Declarations
open Inductive
open Environ
open Typeops
(*i*)

(*s Safe environments. Since we are now able to type terms, we can define an
  abstract type of safe environments, where objects are typed before being
  added. Internally, the datatype is still [env]. We re-export the
  functions of [Environ] for the new type [environment]. *)

type safe_environment

val empty_environment : safe_environment

val universes : safe_environment -> universes
val context : safe_environment -> context
val named_context : safe_environment -> named_context

val push_named_assum :
  identifier * constr -> safe_environment -> safe_environment
val push_named_def :
  identifier * constr -> safe_environment -> safe_environment

val check_and_push_named_assum :
  identifier * constr -> safe_environment ->
    (constr option * types * constraints) * safe_environment
val check_and_push_named_def :
  identifier * constr -> safe_environment -> 
    (constr option * types * constraints) * safe_environment

type local_names = (identifier * variable) list

val add_parameter :
  section_path -> constr -> local_names -> safe_environment -> safe_environment
val add_constant : 
  section_path -> constant_entry -> local_names -> 
    safe_environment -> safe_environment
val add_discharged_constant : 
  section_path -> Cooking.recipe -> local_names -> safe_environment -> safe_environment

val add_mind : 
  section_path -> mutual_inductive_entry -> local_names -> safe_environment 
    -> safe_environment
val add_constraints : constraints -> safe_environment -> safe_environment

val pop_named_decls : identifier list -> safe_environment -> safe_environment

val lookup_named : identifier -> safe_environment -> constr option * types
val lookup_constant : section_path -> safe_environment -> constant_body
val lookup_mind : section_path -> safe_environment -> mutual_inductive_body
val lookup_mind_specif : inductive -> safe_environment -> inductive_instance

val export : safe_environment -> dir_path -> compiled_env
val import : compiled_env -> safe_environment -> safe_environment

val env_of_safe_env : safe_environment -> env


(*s Typing judgments *)

type judgment

val j_val : judgment -> constr
val j_type : judgment -> constr

val safe_infer : safe_environment -> constr -> judgment * constraints

val typing : safe_environment -> constr -> judgment
val typing_in_unsafe_env : env -> constr -> judgment


