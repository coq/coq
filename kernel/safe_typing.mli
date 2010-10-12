(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term
open Declarations
open Entries
open Mod_subst

(** {6 Safe environments } *)

(** Since we are now able to type terms, we can
  define an abstract type of safe environments, where objects are
  typed before being added.

  We also add [open_structure] and [close_section], [close_module] to
  provide functionnality for sections and interactive modules
*)

type safe_environment

val env_of_safe_env : safe_environment -> Environ.env

val empty_environment : safe_environment
val is_empty : safe_environment -> bool

(** Adding and removing local declarations (Local or Variables) *)
val push_named_assum :
  identifier * types -> safe_environment ->
    Univ.constraints * safe_environment
val push_named_def :
  identifier * constr * types option -> safe_environment ->
    Univ.constraints * safe_environment

(** Adding global axioms or definitions *)
type global_declaration =
  | ConstantEntry of constant_entry
  | GlobalRecipe of Cooking.recipe

val add_constant :
  dir_path -> label -> global_declaration -> safe_environment ->
      constant * safe_environment

(** Adding an inductive type *)
val add_mind :
  dir_path -> label -> mutual_inductive_entry -> safe_environment ->
    mutual_inductive * safe_environment

(** Adding a module *)
val add_module :
  label -> module_entry -> bool -> safe_environment
    -> module_path * delta_resolver * safe_environment

(** Adding a module type *)
val add_modtype :
  label -> module_struct_entry -> bool -> safe_environment
    -> module_path * safe_environment

(** Adding universe constraints *)
val add_constraints :
  Univ.constraints -> safe_environment -> safe_environment

(** Settin the strongly constructive or classical logical engagement *)
val set_engagement : engagement -> safe_environment -> safe_environment


(** {6 Interactive module functions } *)

val start_module :
  label -> safe_environment -> module_path * safe_environment

val end_module :
  label -> (module_struct_entry * bool) option
      -> safe_environment -> module_path * delta_resolver * safe_environment 

val add_module_parameter :
  mod_bound_id -> module_struct_entry -> bool -> safe_environment -> delta_resolver * safe_environment

val start_modtype :
  label -> safe_environment -> module_path * safe_environment

val end_modtype :
  label -> safe_environment -> module_path * safe_environment

val add_include :
  module_struct_entry -> bool -> bool -> safe_environment ->
   delta_resolver * safe_environment

val pack_module : safe_environment -> module_body
val current_modpath : safe_environment -> module_path
val delta_of_senv : safe_environment -> delta_resolver*delta_resolver
  

(** Loading and saving compilation units *)

(** exporting and importing modules *)
type compiled_library

val start_library : dir_path -> safe_environment
      -> module_path * safe_environment

val export : safe_environment -> dir_path
      -> module_path * compiled_library

val import : compiled_library -> Digest.t -> safe_environment
      -> module_path * safe_environment

(** Remove the body of opaque constants *)

module LightenLibrary :
sig
  type table 
  type lightened_compiled_library 
  val save : compiled_library -> lightened_compiled_library * table
  val load : load_proof:bool -> (unit -> table) -> lightened_compiled_library -> compiled_library
end

(** {6 Typing judgments } *)

type judgment

val j_val : judgment -> constr
val j_type : judgment -> constr

(** Safe typing of a term returning a typing judgment and universe
   constraints to be added to the environment for the judgment to
   hold. It is guaranteed that the constraints are satisfiable
 *)
val safe_infer : safe_environment -> constr -> judgment * Univ.constraints

val typing : safe_environment -> constr -> judgment


(* Retroknowledge of inductive *)

val register : 
    constr -> Native.retro_action -> safe_environment -> safe_environment
