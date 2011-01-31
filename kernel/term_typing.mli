(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term
open Univ
open Declarations
open Inductive
open Environ
open Entries
open Typeops

val translate_local_def : env -> constr * types option ->
  constr * types * Univ.constraints

val translate_local_assum : env -> types ->
  types * Univ.constraints

val infer_declaration : env -> constant_entry ->
   constr_substituted option * constant_type * constraints * bool * inline

val build_constant_declaration : env -> 'a ->
    constr_substituted option * constant_type * constraints * bool * inline ->
      constant_body

val translate_constant : env -> constant -> constant_entry -> constant_body

val translate_mind :
  env -> mutual_inductive -> mutual_inductive_entry -> mutual_inductive_body

val translate_recipe :
  env -> constant -> Cooking.recipe -> constant_body
