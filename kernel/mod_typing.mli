(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Declarations
open Environ
open Entries
open Mod_subst
open Names


val translate_module : env -> module_path -> bool -> module_entry
  -> module_body

val translate_module_type : env -> module_path -> bool -> module_struct_entry ->
  module_type_body

val translate_struct_module_entry : env -> module_path -> bool -> module_struct_entry ->
  struct_expr_body * struct_expr_body * delta_resolver * Univ.constraints

val translate_struct_type_entry : env -> bool -> module_struct_entry ->
  struct_expr_body * struct_expr_body option * delta_resolver * module_path * Univ.constraints

val translate_struct_include_module_entry : env -> module_path 
  -> bool -> module_struct_entry -> struct_expr_body * delta_resolver * Univ.constraints

val add_modtype_constraints : env -> module_type_body -> env

val add_module_constraints : env -> module_body -> env

val add_struct_expr_constraints : env -> struct_expr_body -> env

val struct_expr_constraints : struct_expr_body -> Univ.constraints

val module_constraints : module_body -> Univ.constraints
