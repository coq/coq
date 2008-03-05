(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Util
open Names
open Univ
open Environ
open Declarations
open Entries
open Mod_subst
(*i*)

(* Various operations on modules and module types *)

(* make the environment entry out of type *)
val module_body_of_type : struct_expr_body -> module_body


val destr_functor : 
  env -> struct_expr_body -> mod_bound_id * struct_expr_body * struct_expr_body

val subst_modtype : substitution -> struct_expr_body -> struct_expr_body
val subst_structure : substitution -> structure_body -> structure_body

val subst_signature_msid :
  mod_self_id -> module_path -> 
  structure_body -> structure_body

(* Evaluation functions *)
val eval_struct : env -> struct_expr_body -> struct_expr_body

val type_of_mb : env -> module_body -> struct_expr_body

(* [add_signature mp sign env] assumes that the substitution [msid]
   $\mapsto$ [mp] has already been performed (or is not necessary, like
   when [mp = MPself msid]) *)
val add_signature : 
  module_path -> structure_body -> env -> env

(* adds a module and its components, but not the constraints *)
val add_module :
  module_path -> module_body -> env -> env

val check_modpath_equiv : env -> module_path -> module_path -> unit

val strengthen : env -> struct_expr_body -> module_path -> struct_expr_body

val error_existing_label : label -> 'a

val error_declaration_not_path : module_struct_entry -> 'a

val error_application_to_not_path : module_struct_entry -> 'a

val error_not_a_functor :  module_struct_entry -> 'a

val error_incompatible_modtypes : 
    struct_expr_body -> struct_expr_body -> 'a

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

val error_not_a_module : string -> 'a 

val error_not_a_constant : label -> 'a

val error_with_incorrect : label -> 'a

val error_a_generative_module_expected : label -> 'a

val error_local_context : label option -> 'a

val error_no_such_label_sub : label->string->string->'a

val resolver_of_environment :
  mod_bound_id -> struct_expr_body -> module_path -> env -> resolver
