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
open Environ
open Mod_declarations
(*i*)

(* Various operations on modules and module types *)

val scrape_modtype : env -> module_type_body -> module_type_body

val module_body : module_type_body -> module_body

val destr_functor : 
  module_type_body -> mod_bound_id * module_type_body * module_type_body


val subst_modtype_mbid : 
  mod_bound_id -> module_path -> module_type_body -> module_type_body

val subst_modtype_msid : 
  mod_str_id -> module_path -> module_type_body -> module_type_body

val subst_signature_msid :
  mod_str_id -> module_path -> 
    module_signature_body -> module_signature_body

(* [add_signature mp sign env] assumes that the substitution [msid]
   \mapsto [mp] has already been performed (or is not necessary, like
   when [mp = MPdot msid]) *)
val add_signature : 
  module_path -> module_signature_body -> env -> env

val add_module :
  module_path -> module_body -> env -> env

val check_modpath_equiv : env -> module_path -> module_path -> unit

val error_existing_label : label -> 'a

val error_declaration_not_path : module_expr -> 'a

val error_application_to_not_path : module_expr -> 'a

val error_not_a_functor : module_expr -> 'a

val error_incompatible_modtypes : 
  module_type_body -> module_type_body -> 'a

val error_not_match : label -> specification_body -> 'a
  
val error_incompatible_labels : label -> label -> 'a

val error_no_such_label : label -> 'a
