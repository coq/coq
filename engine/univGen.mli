(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Constr
open Environ
open Univ


(** The global universe counter *)
type universe_id = DirPath.t * int

val set_remote_new_univ_id : universe_id RemoteCounter.installer

(** Side-effecting functions creating new universe levels. *)

val new_univ_id : unit -> universe_id
val new_univ_level : unit -> Level.t
val new_univ : unit -> Universe.t
val new_Type : unit -> types
val new_Type_sort : unit -> Sorts.t

val new_global_univ : unit -> Universe.t in_universe_context_set
val new_sort_in_family : Sorts.family -> Sorts.t

(** Build a fresh instance for a given context, its associated substitution and
    the instantiated constraints. *)

val fresh_instance_from_context : AUContext.t ->
  Instance.t constrained

val fresh_instance_from : AUContext.t -> Instance.t option ->
  Instance.t in_universe_context_set

val fresh_sort_in_family : Sorts.family ->
  Sorts.t in_universe_context_set
val fresh_constant_instance : env -> Constant.t ->
  pconstant in_universe_context_set
val fresh_inductive_instance : env -> inductive ->
  pinductive in_universe_context_set
val fresh_constructor_instance : env -> constructor ->
  pconstructor in_universe_context_set

val fresh_global_instance : ?names:Univ.Instance.t -> env -> GlobRef.t ->
  constr in_universe_context_set

val fresh_global_or_constr_instance : env -> Globnames.global_reference_or_constr ->
  constr in_universe_context_set

(** Get fresh variables for the universe context.
    Useful to make tactics that manipulate constrs in universe contexts polymorphic. *)
val fresh_universe_context_set_instance : ContextSet.t ->
  universe_level_subst * ContextSet.t

(** Raises [Not_found] if not a global reference. *)
val global_of_constr : constr -> GlobRef.t puniverses

val constr_of_global_univ : GlobRef.t puniverses -> constr

val extend_context : 'a in_universe_context_set -> ContextSet.t ->
  'a in_universe_context_set

(** Create a fresh global in the global environment, without side effects.
    BEWARE: this raises an ANOMALY on polymorphic constants/inductives:
    the constraints should be properly added to an evd.
    See Evd.fresh_global, Evarutil.new_global, and pf_constr_of_global for
    the proper way to get a fresh copy of a global reference. *)
val constr_of_global : GlobRef.t -> constr

(** Returns the type of the global reference, by creating a fresh instance of polymorphic
    references and computing their instantiated universe context. (side-effect on the
    universe counter, use with care). *)
val type_of_global : GlobRef.t -> types in_universe_context_set
