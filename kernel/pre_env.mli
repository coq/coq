(***********************************************************************
    v      *   The Coq Proof Assistant  /  The Coq Development Team     
   <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud 
     \VV/  *************************************************************
      //   *      This file is distributed under the terms of the       
           *       GNU Lesser General Public License Version 2.1        
  ***********************************************************************)

open Util
open Names
open Sign
open Univ
open Term
open Declarations

(** The type of environments. *)


type key = int option ref

type constant_key = constant_body * key

type globals = {
  env_constants : constant_key Cmap_env.t;
  env_inductives : mutual_inductive_body Mindmap_env.t;
  env_modules : module_body MPmap.t;
  env_modtypes : module_type_body MPmap.t}

type stratification = {
  env_universes : universes;
  env_engagement : engagement option
}

type val_kind =
    | VKvalue of values * Idset.t
    | VKnone

type lazy_val = val_kind ref

type named_vals = (identifier * lazy_val) list

type env = {
    env_globals       : globals;
    env_named_context : named_context;
    env_named_vals    : named_vals;
    env_rel_context   : rel_context;
    env_rel_val       : lazy_val list;
    env_nb_rel        : int;
    env_stratification : stratification;
    retroknowledge : Retroknowledge.retroknowledge }

type named_context_val = named_context * named_vals

val empty_named_context_val : named_context_val

val empty_env : env

(** Rel context *)

val nb_rel         : env -> int
val push_rel       : rel_declaration -> env -> env
val lookup_rel_val : int -> env -> lazy_val
val env_of_rel     : int -> env -> env

(** Named context *)

val push_named_context_val  :
    named_declaration -> named_context_val -> named_context_val
val push_named       : named_declaration -> env -> env
val lookup_named_val : identifier -> env -> lazy_val
val env_of_named     : identifier -> env -> env

(** Global constants *)


val lookup_constant_key : constant -> env -> constant_key
val lookup_constant : constant -> env -> constant_body

(** Mutual Inductives *)
val lookup_mind : mutual_inductive -> env -> mutual_inductive_body

