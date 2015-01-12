(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i*)
open Names
open Cic
open Environ
(*i*)

(* Various operations on modules and module types *)

val module_type_of_module :
  module_path option -> module_body -> module_type_body

val is_functor : ('ty,'a) functorize -> bool

val destr_functor : ('ty,'a) functorize -> MBId.t * 'ty * ('ty,'a) functorize

(* adds a module and its components, but not the constraints *)
val add_module : module_body ->  env -> env

val add_module_type : module_path -> module_type_body -> env -> env

val strengthen : module_type_body -> module_path -> module_type_body

val subst_and_strengthen : module_body -> module_path -> module_body

val error_incompatible_modtypes :
  module_type_body -> module_type_body -> 'a

val error_not_match : label -> structure_field_body -> 'a

val error_with_module : unit -> 'a

val error_no_such_label : label -> 'a

val error_no_such_label_sub :
  label -> module_path -> 'a

val error_not_a_constant : label -> 'a

val error_not_a_module : label -> 'a
