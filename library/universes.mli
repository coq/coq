(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Pp
open Names
open Term
open Context
open Environ
open Locus
open Univ

(** Universes *)
val new_univ_level : Names.dir_path -> universe_level
val set_remote_new_univ_level : universe_level RemoteCounter.installer
val new_univ : Names.dir_path -> universe
val new_Type : Names.dir_path -> types
val new_Type_sort : Names.dir_path -> sorts

(** Build a fresh instance for a given context, its associated substitution and 
    the instantiated constraints. *)

val fresh_instance_from_context : universe_context -> 
  (universe_instance * universe_subst) constrained

val fresh_instance_from : universe_context -> 
  (universe_instance * universe_subst) in_universe_context_set

val new_global_univ : unit -> universe in_universe_context_set
val new_sort_in_family : sorts_family -> sorts

val fresh_sort_in_family : env -> sorts_family -> 
  sorts in_universe_context_set
val fresh_constant_instance : env -> constant -> 
  pconstant in_universe_context_set
val fresh_inductive_instance : env -> inductive -> 
  pinductive in_universe_context_set
val fresh_constructor_instance : env -> constructor -> 
  pconstructor in_universe_context_set

val fresh_global_instance : env -> Globnames.global_reference -> 
  constr in_universe_context_set

val fresh_global_or_constr_instance : env -> Globnames.global_reference_or_constr -> 
  constr in_universe_context_set

(** Raises [Not_found] if not a global reference. *)
val global_of_constr : constr -> Globnames.global_reference puniverses

val global_app_of_constr : constr -> Globnames.global_reference puniverses * constr option

val constr_of_global_univ : Globnames.global_reference puniverses -> constr

val extend_context : 'a in_universe_context_set -> universe_context_set -> 
  'a in_universe_context_set

(** Simplification and pruning of constraints:
    [normalize_context_set ctx us]

    - Instantiate the variables in [us] with their most precise
    universe levels respecting the constraints.

    - Normalizes the context [ctx] w.r.t. equality constraints, 
    choosing a canonical universe in each equivalence class 
    (a global one if there is one) and transitively saturate
    the constraints w.r.t to the equalities. *)

module UF : Unionfind.PartitionSig with type elt = universe_level

type universe_opt_subst = universe option universe_map

val make_opt_subst : universe_opt_subst -> universe_subst_fn

val subst_opt_univs_constr : universe_opt_subst -> constr -> constr

val choose_canonical : universe_set -> (Level.t -> bool) (* flexibles *) -> universe_set -> universe_set -> 
  universe_level * (universe_set * universe_set * universe_set)

val instantiate_with_lbound : 
  Univ.LMap.key ->
  Univ.universe ->
  bool ->
  bool ->
  Univ.LSet.t * Univ.universe option Univ.LMap.t *
    Univ.LSet.t *
    (bool * bool * Univ.universe) Univ.LMap.t * Univ.constraints ->
  (Univ.LSet.t * Univ.universe option Univ.LMap.t *
    Univ.LSet.t *
     (bool * bool * Univ.universe) Univ.LMap.t * Univ.constraints) *
    (bool * bool * Univ.universe)
    
val compute_lbound : (constraint_type * Univ.universe) list -> universe option

type constraints_map = (Univ.constraint_type * Univ.LMap.key) list Univ.LMap.t

val pr_constraints_map : constraints_map -> Pp.std_ppcmds

val minimize_univ_variables : 
           Univ.LSet.t ->
           Univ.universe option Univ.LMap.t ->
           Univ.LSet.t ->
  constraints_map -> constraints_map ->
           Univ.constraints ->
           Univ.LSet.t * Univ.universe option Univ.LMap.t *
	     Univ.LSet.t *
           (bool * bool * Univ.universe) Univ.LMap.t * Univ.constraints


val normalize_context_set : universe_context_set -> 
  universe_opt_subst (* The defined and undefined variables *) ->
  universe_set (* univ variables that can be substituted by algebraics *) -> 
  (universe_opt_subst * universe_set) in_universe_context_set

val normalize_univ_variables : universe_opt_subst -> 
  universe_opt_subst * universe_set * universe_set * universe_subst

val normalize_univ_variable : 
  find:(universe_level -> universe) ->
  update:(universe_level -> universe -> universe) ->
  universe_level -> universe

val normalize_univ_variable_opt_subst : universe_opt_subst ref ->
  (universe_level -> universe)

val normalize_univ_variable_subst : universe_subst ref ->
  (universe_level -> universe)

val normalize_universe_opt_subst : universe_opt_subst ref ->
  (universe -> universe)

val normalize_universe_subst : universe_subst ref ->
  (universe -> universe)

(** Create a fresh global in the global environment, without side effects.
    BEWARE: this raises an ANOMALY on polymorphic constants/inductives: 
    the constraints should be properly added to an evd. 
    See Evd.fresh_global, Evarutil.new_global, and pf_constr_of_global for
    the proper way to get a fresh copy of a global reference. *)

val constr_of_global : Globnames.global_reference -> constr

(** [unsafe_constr_of_global gr] turns [gr] into a constr, works on polymorphic
    references by taking the original universe instance that is not recorded 
    anywhere. The constraints are forgotten as well. DO NOT USE in new code. *)
val unsafe_constr_of_global : Globnames.global_reference -> constr in_universe_context

(** Returns the type of the global reference, by creating a fresh instance of polymorphic 
    references and computing their instantiated universe context. (side-effect on the
    universe counter, use with care). *)
val type_of_global : Globnames.global_reference -> types in_universe_context_set

(** Full universes substitutions into terms *)

val nf_evars_and_universes_local : (existential -> constr option) -> universe_level_subst -> 
  constr -> constr

val nf_evars_and_universes_opt_subst : (existential -> constr option) -> 
  universe_opt_subst -> constr -> constr

(** Get fresh variables for the universe context.
    Useful to make tactics that manipulate constrs in universe contexts polymorphic. *)
val fresh_universe_context_set_instance : universe_context_set -> 
  universe_level_subst * universe_context_set

val pr_universe_opt_subst : universe_opt_subst -> Pp.std_ppcmds

(** Shrink a universe context to a restricted set of variables *)

val universes_of_constr : constr -> universe_set
val shrink_universe_context : universe_context_set -> universe_set -> universe_context_set
val restrict_universe_context : universe_context_set -> universe_set -> universe_context_set
val simplify_universe_context : universe_context_set -> 
  universe_context_set * universe_level_subst

val refresh_constraints : universes -> universe_context_set -> universe_context_set * universes

val remove_trivial_constraints : universe_context_set -> universe_context_set
