(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term
open Univ
open Environ
open Declarations
open Entries

val translate_local_def : env -> Id.t -> definition_entry ->
  constant_def * types * constant_universes

val translate_local_assum : env -> types -> types

val mk_pure_proof : constr -> proof_output

(* returns the same definition_entry but with side effects turned into
 * let-ins or beta redexes. it is meant to get a term out of a not yet
 * type checked proof *)
val handle_side_effects : env -> definition_entry -> definition_entry

val translate_constant : env -> constant -> constant_entry -> constant_body

val translate_mind :
  env -> mutual_inductive -> mutual_inductive_entry -> mutual_inductive_body

val translate_recipe : env -> constant -> Cooking.recipe -> constant_body

(** Internal functions, mentioned here for debug purpose only *)

val infer_declaration : env -> constant option -> 
  constant_entry -> Cooking.result

val build_constant_declaration :
  constant -> env -> Cooking.result -> constant_body

val set_suggest_proof_using :
  (constant -> env -> Id.Set.t -> Id.Set.t -> Id.t list -> unit) -> unit
