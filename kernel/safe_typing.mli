(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
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

val sideff_of_con : safe_environment -> constant -> side_effect 

val is_curmod_library : safe_environment -> bool


(* safe_environment has functional data affected by lazy computations,
 * thus this function returns a new safe_environment *)
val join_safe_environment : safe_environment -> safe_environment

val empty_environment : safe_environment
val is_empty : safe_environment -> bool

(** Adding and removing local declarations (Local or Variables) *)
val push_named_assum :
  Id.t * types -> safe_environment ->
    Univ.constraints * safe_environment
val push_named_def :
  Id.t * definition_entry -> safe_environment ->
    Univ.constraints * safe_environment

(** Adding global axioms or definitions *)
type global_declaration =
  | ConstantEntry of constant_entry
  | GlobalRecipe of Cooking.recipe

val add_constant :
  DirPath.t -> Label.t -> global_declaration -> safe_environment ->
      constant * safe_environment

(** Adding an inductive type *)
val add_mind :
  DirPath.t -> Label.t -> mutual_inductive_entry -> safe_environment ->
    mutual_inductive * safe_environment

(** Adding a module *)
val add_module :
  Label.t -> module_entry -> inline -> safe_environment
    -> module_path * delta_resolver * safe_environment

(** Adding a module type *)
val add_modtype :
  Label.t -> module_struct_entry -> inline -> safe_environment
    -> module_path * safe_environment

(** Adding universe constraints *)
val add_constraints :
  Univ.constraints -> safe_environment -> safe_environment

(** Settin the strongly constructive or classical logical engagement *)
val set_engagement : engagement -> safe_environment -> safe_environment


(** {6 Interactive module functions } *)

val start_module :
  Label.t -> safe_environment -> module_path * safe_environment

val end_module :
  Label.t -> (module_struct_entry * inline) option
      -> safe_environment -> module_path * delta_resolver * safe_environment 

val add_module_parameter :
  MBId.t -> module_struct_entry -> inline -> safe_environment -> delta_resolver * safe_environment

val start_modtype :
  Label.t -> safe_environment -> module_path * safe_environment

val end_modtype :
  Label.t -> safe_environment -> module_path * safe_environment

val add_include :
  module_struct_entry -> bool -> inline -> safe_environment ->
   delta_resolver * safe_environment

val delta_of_senv : safe_environment -> delta_resolver*delta_resolver

(** Loading and saving compilation units *)

(** exporting and importing modules *)
type compiled_library

type native_library = Nativecode.global list

val start_library : DirPath.t -> safe_environment
      -> module_path * safe_environment

val export : safe_environment -> DirPath.t
      -> module_path * compiled_library * native_library

val import : compiled_library -> Digest.t -> safe_environment
      -> module_path * safe_environment * Nativecode.symbol array

val join_compiled_library : compiled_library -> unit

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

(** {7 Query } *)

val exists_objlabel : Label.t -> safe_environment -> bool

(*spiwack: safe retroknowledge functionalities *)

open Retroknowledge

val retroknowledge : (retroknowledge-> 'a) -> safe_environment -> 'a

val register : safe_environment -> field -> Retroknowledge.entry -> constr
                                         -> safe_environment

val register_inline : constant -> safe_environment -> safe_environment
