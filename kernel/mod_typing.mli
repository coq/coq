(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Declarations
open Environ
open Entries
open Mod_subst
open Names

(** Main functions for translating module entries *)

val translate_module :
  env -> module_path -> inline -> module_entry -> module_body

val translate_modtype :
  env -> module_path -> inline -> module_type_entry -> module_type_body

(** Low-level function for translating a module struct entry :
    - We translate to a module when a [module_path] is given,
      otherwise to a module type.
    - The first output is the expanded signature
    - The second output is the algebraic expression, kept for the extraction.
      It is never None when translating to a module, but for module type
      it could not be contain applications or functors.
*)

type 'alg translation =
  module_signature * 'alg option * delta_resolver * Univ.constraints

val translate_mse :
  env -> module_path option -> inline -> module_struct_entry ->
    module_alg_expr translation

val translate_mse_incl :
  env -> module_path -> inline -> module_struct_entry ->
    module_alg_expr translation

val finalize_module :
  env -> module_path -> module_expression translation ->
  (module_type_entry * inline) option ->
  module_body
