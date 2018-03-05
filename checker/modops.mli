(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*i*)
open Names
open Cic
open Environ
(*i*)

(* Various operations on modules and module types *)

val module_type_of_module :
  ModPath.t option -> module_body -> module_type_body

val is_functor : ('ty,'a) functorize -> bool

val destr_functor : ('ty,'a) functorize -> MBId.t * 'ty * ('ty,'a) functorize

(* adds a module and its components, but not the constraints *)
val add_module : module_body ->  env -> env

val add_module_type : ModPath.t -> module_type_body -> env -> env

val strengthen : module_type_body -> ModPath.t -> module_type_body

val subst_and_strengthen : module_body -> ModPath.t -> module_body

val error_incompatible_modtypes :
  module_type_body -> module_type_body -> 'a

val error_not_match : Label.t -> structure_field_body -> 'a

val error_with_module : unit -> 'a

val error_no_such_label : Label.t -> 'a

val error_no_such_label_sub :
  Label.t -> ModPath.t -> 'a

val error_not_a_constant : Label.t -> 'a

val error_not_a_module : Label.t -> 'a
