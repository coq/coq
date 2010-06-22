(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Names
open Univ
open Environ
open Declarations
open Entries
open Mod_subst

(** Various operations on modules and module types *)


val module_body_of_type : module_path -> module_type_body  -> module_body 

val module_type_of_module : env -> module_path option -> module_body -> 
  module_type_body

val destr_functor :
  env -> struct_expr_body -> mod_bound_id * module_type_body * struct_expr_body

val subst_struct_expr :  substitution -> struct_expr_body -> struct_expr_body

val subst_signature : substitution -> structure_body -> structure_body

val add_signature :
  module_path -> structure_body -> delta_resolver -> env -> env

(** adds a module and its components, but not the constraints *)
val add_module : module_body -> env -> env

val check_modpath_equiv : env -> module_path -> module_path -> unit

val strengthen : env -> module_type_body -> module_path -> module_type_body

val complete_inline_delta_resolver :
  env -> module_path -> mod_bound_id -> module_type_body ->
  delta_resolver -> delta_resolver

val strengthen_and_subst_mb : module_body -> module_path -> env -> bool 
  -> module_body

val subst_modtype_and_resolver : module_type_body -> module_path -> env ->
  module_type_body

val clean_bounded_mod_expr : struct_expr_body -> struct_expr_body

val error_existing_label : label -> 'a

val error_declaration_not_path : module_struct_entry -> 'a

val error_application_to_not_path : module_struct_entry -> 'a

val error_not_a_functor :  module_struct_entry -> 'a

val error_incompatible_modtypes :
  module_type_body -> module_type_body -> 'a

val error_not_equal : module_path -> module_path -> 'a

val error_not_match : label -> structure_field_body -> 'a

val error_incompatible_labels : label -> label -> 'a

val error_no_such_label : label -> 'a

val error_result_must_be_signature : unit -> 'a

val error_signature_expected : struct_expr_body -> 'a

val error_no_module_to_end : unit -> 'a

val error_no_modtype_to_end : unit -> 'a

val error_not_a_modtype_loc : loc -> string -> 'a

val error_not_a_module_loc : loc -> string -> 'a

val error_not_a_module_or_modtype_loc : loc -> string -> 'a

val error_not_a_module : string -> 'a

val error_not_a_constant : label -> 'a

val error_with_incorrect : label -> 'a

val error_a_generative_module_expected : label -> 'a

val error_local_context : label option -> 'a

val error_no_such_label_sub : label->string->'a

val error_with_in_module : unit -> 'a

val error_application_to_module_type : unit -> 'a

