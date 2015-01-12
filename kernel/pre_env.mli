(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term
open Context
open Declarations
open Univ

(** The type of environments. *)

type link_info =
  | Linked of string
  | LinkedInteractive of string
  | NotLinked

type key = int Ephemeron.key option ref 

type constant_key = constant_body * (link_info ref * key)

type mind_key = mutual_inductive_body * link_info ref

type globals = {
  env_constants : constant_key Cmap_env.t;
  env_inductives : mind_key Mindmap_env.t;
  env_modules : module_body MPmap.t;
  env_modtypes : module_type_body MPmap.t}

type stratification = {
  env_universes : universes;
  env_engagement : engagement option;
  env_type_in_type : bool
}

type lazy_val

val force_lazy_val : lazy_val -> (values * Id.Set.t) option
val dummy_lazy_val : unit -> lazy_val
val build_lazy_val : lazy_val -> (values * Id.Set.t) -> unit

type named_vals = (Id.t * lazy_val) list

type env = {
    env_globals       : globals;
    env_named_context : named_context;
    env_named_vals    : named_vals;
    env_rel_context   : rel_context;
    env_rel_val       : lazy_val list;
    env_nb_rel        : int;
    env_stratification : stratification;
    env_conv_oracle   : Conv_oracle.oracle;
    retroknowledge : Retroknowledge.retroknowledge;
    indirect_pterms : Opaqueproof.opaquetab;
}

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
val lookup_named_val : Id.t -> env -> lazy_val
val env_of_named     : Id.t -> env -> env

(** Global constants *)


val lookup_constant_key : constant -> env -> constant_key
val lookup_constant : constant -> env -> constant_body

(** Mutual Inductives *)
val lookup_mind_key : mutual_inductive -> env -> mind_key
val lookup_mind : mutual_inductive -> env -> mutual_inductive_body
