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
open Univ
open Term
open Declarations
open Indtypes
open Safe_typing
   (*i*)

(* This module defines the global environment of Coq. 
 * The functions below are exactly the same as the ones in [Typing],
 * operating on that global environment. *)

val safe_env : unit -> safe_environment
val env : unit -> Environ.env

val universes : unit -> universes
val named_context : unit -> Sign.named_context

(* Extending env with variables, constants and inductives *)
val push_named_assum : (identifier * types) -> Univ.constraints
val push_named_def   : (identifier * constr * types option) -> Univ.constraints

val add_constant    : constant -> global_declaration -> unit
val add_mind        : mutual_inductive -> mutual_inductive_entry -> unit
val add_constraints : constraints -> unit

(* Queries *)
val lookup_named     : variable -> named_declaration
val lookup_constant  : constant -> constant_body
val lookup_inductive : inductive -> mutual_inductive_body * one_inductive_body
val lookup_mind      : mutual_inductive -> mutual_inductive_body

(* Modules *)
val export : dir_path -> Environ.compiled_env
val import : Environ.compiled_env -> unit

(*s Function to get an environment from the constants part of the global
 * environment and a given context. *)
  
val type_of_global : Libnames.global_reference -> types
val env_of_context : Sign.named_context -> Environ.env

(* [get_kn dir id] creates a kernel_name for an object in the current
 * module, in section dir, named id *)
val get_kn : dir_path -> label -> kernel_name

