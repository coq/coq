(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Term
open Univ
open Declarations
open Inductive
open Environ
open Entries
open Typeops
(*i*)

val translate_local_def : env -> constr * types option -> 
  constr * types * Univ.constraints

val translate_local_assum : env -> types ->
  types * Univ.constraints

val translate_constant : env -> constant_entry -> constant_body

val translate_mind : 
  env -> mutual_inductive_entry -> mutual_inductive_body

val translate_recipe : 
  env -> Cooking.recipe -> constant_body
