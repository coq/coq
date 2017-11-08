(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Constr
open Declarations

(** The type of environments. *)

type link_info =
  | Linked of string
  | LinkedInteractive of string
  | NotLinked

type key = int CEphemeron.key option ref 

type constant_key = constant_body * (link_info ref * key)

type mind_key = mutual_inductive_body * link_info ref

type globals = {
  env_constants : constant_key Cmap_env.t;
  env_inductives : mind_key Mindmap_env.t;
  env_modules : module_body MPmap.t;
  env_modtypes : module_type_body MPmap.t}

type stratification = {
  env_universes : UGraph.t;
  env_engagement : engagement
}

type lazy_val

val force_lazy_val : lazy_val -> (values * Id.Set.t) option
val dummy_lazy_val : unit -> lazy_val
val build_lazy_val : lazy_val -> (values * Id.Set.t) -> unit

type named_context_val = private {
  env_named_ctx : Context.Named.t;
  env_named_map : (Context.Named.Declaration.t * lazy_val) Id.Map.t;
}

type env = {
    env_globals       : globals;
    env_named_context : named_context_val;
    env_rel_context   : Context.Rel.t;
    env_rel_val       : lazy_val list;
    env_nb_rel        : int;
    env_stratification : stratification;
    env_typing_flags  : typing_flags;
    env_conv_oracle   : Conv_oracle.oracle;
    retroknowledge : Retroknowledge.retroknowledge;
    indirect_pterms : Opaqueproof.opaquetab;
}

val empty_named_context_val : named_context_val

val empty_env : env

(** Rel context *)

val nb_rel         : env -> int
val push_rel       : Context.Rel.Declaration.t -> env -> env
val lookup_rel_val : int -> env -> lazy_val
val env_of_rel     : int -> env -> env

(** Named context *)

val push_named_context_val  :
    Context.Named.Declaration.t -> named_context_val -> named_context_val
val push_named_context_val_val  :
    Context.Named.Declaration.t -> lazy_val -> named_context_val -> named_context_val
val match_named_context_val  :
  named_context_val -> (Context.Named.Declaration.t * lazy_val * named_context_val) option
val map_named_val :
   (constr -> constr) -> named_context_val -> named_context_val

val push_named       : Context.Named.Declaration.t -> env -> env
val lookup_named     : Id.t -> env -> Context.Named.Declaration.t
val lookup_named_val : Id.t -> env -> lazy_val
val env_of_named     : Id.t -> env -> env

(** Global constants *)


val lookup_constant_key : Constant.t -> env -> constant_key
val lookup_constant : Constant.t -> env -> constant_body

(** Mutual Inductives *)
val lookup_mind_key : MutInd.t -> env -> mind_key
val lookup_mind : MutInd.t -> env -> mutual_inductive_body
