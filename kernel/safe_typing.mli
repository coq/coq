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
open Declarations
(*i*)

(*s Safe environments. Since we are now able to type terms, we can define an
  abstract type of safe environments, where objects are typed before being
  added. Internally, the datatype is still [env]. We re-export the
  functions of [Environ] for the new type [environment]. *)

type safe_environment

val env_of_safe_env : safe_environment -> Environ.env

val empty_environment : safe_environment

(* Adding and removing local declarations (Local or Variables) *)
val push_named_assum :
  identifier * types -> safe_environment ->
    Univ.constraints * safe_environment
val push_named_def :
  identifier * constr -> safe_environment ->
    Univ.constraints * safe_environment
val pop_named_decls : identifier list -> safe_environment -> safe_environment

(* Adding global axioms or definitions *)

val add_parameter :
  section_path -> constr -> safe_environment -> safe_environment

(*s Global and local constant declaration. *)

type constant_entry = {
  const_entry_body   : constr;
  const_entry_type   : types option;
  const_entry_opaque : bool }

val add_constant : 
  section_path -> constant_entry -> safe_environment -> safe_environment
val add_discharged_constant : 
  section_path -> Cooking.recipe -> safe_environment -> safe_environment

(* Adding an inductive type *)
val add_mind : 
  section_path -> Indtypes.mutual_inductive_entry -> safe_environment ->
    safe_environment

(* Adding universe constraints *)
val add_constraints : Univ.constraints -> safe_environment -> safe_environment

(* Loading and saving a module *)
val export : safe_environment -> dir_path -> Environ.compiled_env
val import : Environ.compiled_env -> safe_environment -> safe_environment


(*s Typing judgments *)

type judgment

val j_val : judgment -> constr
val j_type : judgment -> constr

(* Safe typing of a term returning a typing judgment and universe
   constraints to be added to the environment for the judgment to
   hold. It is guaranteed that the constraints are satisfiable
 *)
val safe_infer : safe_environment -> constr -> judgment * Univ.constraints

val typing : safe_environment -> constr -> judgment


