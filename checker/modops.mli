(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i*)
open Util
open Names
open Univ
open Term
open Declarations
open Environ
(*i*)

(* Various operations on modules and module types *)

(* make the envirconment entry out of type *)
val module_body_of_type : module_path -> module_type_body -> module_body

val module_type_of_module : env -> module_path option -> module_body ->
  module_type_body

val destr_functor :
  env -> struct_expr_body -> mod_bound_id * module_type_body * struct_expr_body

val add_signature : module_path -> structure_body -> delta_resolver -> env -> env

(* adds a module and its components, but not the constraints *)
val add_module : module_body ->  env -> env

val check_modpath_equiv : env -> module_path -> module_path -> unit

val strengthen : env -> module_type_body -> module_path -> module_type_body

val subst_and_strengthen : module_body -> module_path -> env -> module_body 

val error_incompatible_modtypes :
  module_type_body -> module_type_body -> 'a

val error_not_match : label -> structure_field_body -> 'a

val error_with_incorrect : label -> 'a

val error_no_such_label : label -> 'a

val error_no_such_label_sub :
  label -> module_path -> 'a

val error_signature_expected : struct_expr_body -> 'a

val error_not_a_constant : label -> 'a

val error_not_a_module : label -> 'a

val error_a_generative_module_expected : label -> 'a

val error_application_to_not_path : struct_expr_body -> 'a
