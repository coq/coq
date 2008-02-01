(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Term
open Declarations
open Entries
(*i*)

(*s Safe environments. Since we are now able to type terms, we can
  define an abstract type of safe environments, where objects are
  typed before being added.

  We also add [open_structure] and [close_section], [close_module] to
  provide functionnality for sections and interactive modules 
*)

type safe_environment

val env_of_safe_env : safe_environment -> Environ.env

val empty_environment : safe_environment
val is_empty : safe_environment -> bool

(* Adding and removing local declarations (Local or Variables) *)
val push_named_assum :
  identifier * types -> safe_environment ->
    Univ.constraints * safe_environment
val push_named_def :
  identifier * constr * types option -> safe_environment ->
    Univ.constraints * safe_environment

(* Adding global axioms or definitions *)
type global_declaration = 
  | ConstantEntry of constant_entry
  | GlobalRecipe of Cooking.recipe

val add_constant : 
  dir_path -> label -> global_declaration -> safe_environment -> 
      constant * safe_environment

(* Adding an inductive type *)
val add_mind : 
  dir_path -> label -> mutual_inductive_entry -> safe_environment ->
    mutual_inductive * safe_environment

(* Adding a module *)
val add_module :
  label -> module_entry -> safe_environment 
    -> module_path * safe_environment

(* Adding a module type *)
val add_modtype :
  label -> module_struct_entry -> safe_environment 
    -> module_path * safe_environment

(* Adding universe constraints *)
val add_constraints : 
  Univ.constraints -> safe_environment -> safe_environment

(* Settin the strongly constructive or classical logical engagement *)
val set_engagement : engagement -> safe_environment -> safe_environment


(*s Interactive module functions *)
val start_module : 
  label -> safe_environment -> module_path * safe_environment
val end_module :
  label -> module_struct_entry option 
      -> safe_environment -> module_path * safe_environment 

val add_module_parameter :
  mod_bound_id -> module_struct_entry -> safe_environment -> safe_environment

val start_modtype :
  label -> safe_environment -> module_path * safe_environment

val end_modtype :
  label -> safe_environment -> module_path * safe_environment

val add_include :
  module_struct_entry -> safe_environment -> safe_environment

val current_modpath : safe_environment -> module_path
val current_msid : safe_environment -> mod_self_id


(* Loading and saving compilation units *)

(* exporting and importing modules *)
type compiled_library

val start_library : dir_path -> safe_environment 
      -> module_path * safe_environment

val export : safe_environment -> dir_path  
      -> mod_self_id * compiled_library

val import : compiled_library -> Digest.t -> safe_environment 
      -> module_path * safe_environment

(* Remove the body of opaque constants *)

val lighten_library : compiled_library -> compiled_library

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



(*spiwack: safe retroknowledge functionalities *)

open Retroknowledge

val retroknowledge : (retroknowledge-> 'a) -> safe_environment -> 'a

val register : safe_environment -> field -> Retroknowledge.entry -> constr
                                         -> safe_environment
