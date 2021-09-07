(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Constr

(** This module provides support for registering inductive scheme builders,
   declaring schemes and generating schemes on demand *)

(** A scheme is either a "mutual scheme_kind" or an "individual scheme_kind" *)

type mutual
type individual
type 'a scheme_kind

type handle

type scheme_dependency =
| SchemeMutualDep of MutInd.t * mutual scheme_kind
| SchemeIndividualDep of inductive * individual scheme_kind

type mutual_scheme_object_function =
  Environ.env -> handle -> MutInd.t -> constr array Evd.in_evar_universe_context
type individual_scheme_object_function =
  Environ.env -> handle -> inductive -> constr Evd.in_evar_universe_context

(** Main functions to register a scheme builder. Note these functions
   are not safe to be used by plugins as their effects won't be undone
   on backtracking *)

val declare_mutual_scheme_object : string ->
  ?deps:(Environ.env -> MutInd.t -> scheme_dependency list) ->
  ?aux:string ->
  mutual_scheme_object_function -> mutual scheme_kind

val declare_individual_scheme_object : string ->
  ?deps:(Environ.env -> inductive -> scheme_dependency list) ->
  ?aux:string ->
  individual_scheme_object_function ->
  individual scheme_kind

(** Force generation of a (mutually) scheme with possibly user-level names *)

val define_individual_scheme : individual scheme_kind ->
  Id.t option -> inductive -> unit

val define_mutual_scheme : mutual scheme_kind ->
  (int * Id.t) list -> MutInd.t -> unit

(** Main function to retrieve a scheme in the cache or to generate it *)
val find_scheme : 'a scheme_kind -> inductive -> Constant.t Proofview.tactic

(** Like [find_scheme] but does not generate a constant on the fly *)
val lookup_scheme : 'a scheme_kind -> inductive -> Constant.t option

(** To be used by scheme-generating functions when looking for a subscheme. *)
val local_lookup_scheme : handle -> 'a scheme_kind -> inductive -> Constant.t option

val pr_scheme_kind : 'a scheme_kind -> Pp.t

val declare_definition_scheme :
  (internal : bool
   -> univs:UState.named_universes_entry
   -> role:Evd.side_effect_role
   -> name:Id.t
   -> Constr.t
   -> Constant.t * Evd.side_effects) ref
