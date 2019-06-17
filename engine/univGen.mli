(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
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
type univ_unique_id
val set_remote_new_univ_id : univ_unique_id RemoteCounter.installer
val new_univ_id : unit -> univ_unique_id (** for the stm *)

(** Side-effecting functions creating new universe levels. *)

val new_univ_global : unit -> Level.UGlobal.t
val fresh_level : unit -> Level.t

val new_global_univ : unit -> Universe.t in_universe_context_set

(** Build a fresh instance for a given context, its associated substitution and
    the instantiated constraints. *)

val fresh_instance : AUContext.t -> Instance.t in_universe_context_set

val fresh_instance_from : ?loc:Loc.t -> AUContext.t -> Instance.t option ->
  Instance.t in_universe_context_set

val fresh_sort_in_family : Sorts.family ->
  Sorts.t in_universe_context_set
val fresh_constant_instance : env -> Constant.t ->
  pconstant in_universe_context_set
val fresh_inductive_instance : env -> inductive ->
  pinductive in_universe_context_set
val fresh_constructor_instance : env -> constructor ->
  pconstructor in_universe_context_set

val fresh_global_instance : ?loc:Loc.t -> ?names:Univ.Instance.t -> env -> GlobRef.t ->
  constr in_universe_context_set

val fresh_global_or_constr_instance : env -> Globnames.global_reference_or_constr ->
  constr in_universe_context_set

(** Get fresh variables for the universe context.
    Useful to make tactics that manipulate constrs in universe contexts polymorphic. *)
val fresh_universe_context_set_instance : ContextSet.t ->
  universe_level_subst * ContextSet.t

(** Raises [Not_found] if not a global reference. *)
val global_of_constr : constr -> GlobRef.t puniverses

(** Create a fresh global in the global environment, without side effects.
    BEWARE: this raises an error on polymorphic constants/inductives:
    the constraints should be properly added to an evd.
    See Evd.fresh_global, Evarutil.new_global, and pf_constr_of_global for
    the proper way to get a fresh copy of a polymorphic global reference. *)
val constr_of_monomorphic_global : GlobRef.t -> constr
