(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Identifier
open Names
open Term
open Univ
open Declarations
open Mod_declarations
open Inductive
open Environ
open Typeops
(*i*)

(*s Safe environments. Since we are now able to type terms, we can
  define an abstract type of safe environments, where objects are
  typed before being added. Internally, the datatype is still [env].
  We re-export the functions of [Environ] for the new type
  [safe_environment]. 

  We also add [open_structure] and [close_section], [close_module]
  to provide functionnality for sections and interactive modules *)

type safe_environment

val empty_environment : safe_environment

(*i Safe environment is only global *)

(* section variable/hypothesis *)
val push_named_assum :
  identifier * constr -> safe_environment -> safe_environment
(* section definition *)
val push_named_def :
  identifier * constr -> safe_environment -> safe_environment

(*i*)

(* [add_thing l thing_entry env] checks [thing_entry] and adds it to
   the environment [env]. The return value contains new environment
   and the name by which newly added [thing] must be referred to *)

(* global constant *)
val add_constant : 
  label -> constant_entry -> safe_environment 
    -> safe_environment * long_name

(* inductive *)
val add_mind : 
  mutual_inductive_entry -> safe_environment 
    -> safe_environment * long_name

val add_module :
  label -> module_entry -> safe_environment 
    -> safe_environment * module_path
val add_modtype :
  label -> module_type_entry -> safe_environment 
    -> safe_environment * long_name

(*i safe environment is only global  *)
(* section variable/definition *)
val lookup_named : identifier -> safe_environment -> constr option * types
(*i*)

(* lookup functions *)
val lookup_constant : long_name -> safe_environment -> constant_body
val lookup_mind : long_name -> safe_environment -> mutual_inductive_body
val lookup_mind_specif : inductive -> safe_environment -> inductive_instance
val lookup_module : module_path -> safe_environment -> module_body
val lookup_modtype : long_name -> safe_environment -> module_type_body


(* interactive module functions *)
val begin_module : 
  label -> (mod_bound_id * module_type_entry) list 
    -> module_type_entry option 
      -> safe_environment -> safe_environment
val end_module :
  label -> safe_environment 
    -> safe_environment * module_path

val current_modpath : safe_environment -> module_path


(* other functionnality *)

val set_opaque : safe_environment -> long_name -> unit
val set_transparent : safe_environment -> long_name -> unit


(* exporting and importing modules *)
type compiled_module

val export : safe_environment -> dir_path -> compiled_module
val import : compiled_module -> Digest.t -> safe_environment 
  -> safe_environment * module_path


val env_of_safe_env : safe_environment -> env


(*s Typing judgments *)

type judgment

val j_val : judgment -> constr
val j_type : judgment -> types

val safe_infer : safe_environment -> constr -> judgment * constraints

val typing : safe_environment -> constr -> judgment
val typing_in_unsafe_env : env -> constr -> unsafe_judgment


