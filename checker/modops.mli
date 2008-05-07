(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: modops.mli 9821 2007-05-11 17:00:58Z aspiwack $ i*)

(*i*)
open Util
open Names
open Univ
open Term
open Declarations
open Environ
(*i*)

(* Various operations on modules and module types *)

(* make the environment entry out of type *)
val module_body_of_type : module_type_body -> module_body

val module_type_of_module : module_path option -> module_body -> 
  module_type_body 

val destr_functor : 
  env -> struct_expr_body -> mod_bound_id * module_type_body * struct_expr_body

(* Evaluation functions *)
val eval_struct : env -> struct_expr_body -> struct_expr_body

val type_of_mb : env -> module_body -> struct_expr_body

(* [add_signature mp sign env] assumes that the substitution [msid]
   $\mapsto$ [mp] has already been performed (or is not necessary, like
   when [mp = MPself msid]) *)
val add_signature : module_path -> structure_body -> env -> env

(* adds a module and its components, but not the constraints *)
val add_module : module_path -> module_body ->  env -> env

val check_modpath_equiv : env -> module_path -> module_path -> unit

val strengthen : env -> struct_expr_body -> module_path -> struct_expr_body

val update_subst : env -> module_body -> module_path -> bool * substitution

val error_incompatible_modtypes : 
  module_type_body -> module_type_body -> 'a

val error_not_match : label -> structure_field_body -> 'a

val error_with_incorrect : label -> 'a

val error_no_such_label : label -> 'a

val error_no_such_label_sub :
  label -> mod_self_id -> mod_self_id -> 'a

val error_signature_expected : struct_expr_body -> 'a

val error_not_a_constant : label -> 'a

val error_not_a_module : label -> 'a 

val error_a_generative_module_expected : label -> 'a

val error_application_to_not_path : struct_expr_body -> 'a
