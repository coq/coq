(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
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

type universe_names = 
  Univ.universe_level Idmap.t * Id.t Univ.LMap.t

val global_universe_names : unit -> universe_names
val set_global_universe_names : universe_names -> unit

val pr_with_global_universes : Level.t -> Pp.std_ppcmds

(** The global universe counter *)
val set_remote_new_univ_level : universe_level RemoteCounter.installer

(** Side-effecting functions creating new universe levels. *)

val new_univ_level : Names.dir_path -> universe_level
val new_univ : Names.dir_path -> universe
val new_Type : Names.dir_path -> types
val new_Type_sort : Names.dir_path -> sorts

val new_global_univ : unit -> universe in_universe_context_set
val new_sort_in_family : sorts_family -> sorts

(** {6 Constraints for type inference}
    
    When doing conversion of universes, not only do we have =/<= constraints but
    also Lub constraints which correspond to unification of two levels which might
    not be necessary if unfolding is performed.
*)

type universe_constraint_type = ULe | UEq | ULub

type universe_constraint = universe * universe_constraint_type * universe
module Constraints : sig
  include Set.S with type elt = universe_constraint
		       
  val pr : t -> Pp.std_ppcmds
end

type universe_constraints = Constraints.t
type 'a universe_constrained = 'a * universe_constraints
type 'a universe_constraint_function = 'a -> 'a -> universe_constraints -> universe_constraints

val subst_univs_universe_constraints : universe_subst_fn -> 
  universe_constraints -> universe_constraints

val enforce_eq_instances_univs : bool -> universe_instance universe_constraint_function

val to_constraints : universes -> universe_constraints -> constraints

(** [eq_constr_univs_infer u a b] is [true, c] if [a] equals [b] modulo alpha, casts,
   application grouping, the universe constraints in [u] and additional constraints [c]. *)
val eq_constr_univs_infer : Univ.universes -> constr -> constr -> bool universe_constrained

(** [leq_constr_univs u a b] is [true, c] if [a] is convertible to [b]
    modulo alpha, casts, application grouping, the universe constraints
    in [u] and additional constraints [c]. *)
val leq_constr_univs_infer : Univ.universes -> constr -> constr -> bool universe_constrained

(** [eq_constr_universes a b] [true, c] if [a] equals [b] modulo alpha, casts,
    application grouping and the universe constraints in [c]. *)
val eq_constr_universes : constr -> constr -> bool universe_constrained

(** [leq_constr_universes a b] [true, c] if [a] is convertible to [b] modulo
    alpha, casts, application grouping and the universe constraints in [c]. *)
val leq_constr_universes : constr -> constr -> bool universe_constrained

(** [eq_constr_universes a b] [true, c] if [a] equals [b] modulo alpha, casts,
    application grouping and the universe constraints in [c]. *)
val eq_constr_universes_proj : env -> constr -> constr -> bool universe_constrained

(** Build a fresh instance for a given context, its associated substitution and 
    the instantiated constraints. *)

val fresh_instance_from_context : universe_context -> 
  universe_instance constrained

val fresh_instance_from : universe_context -> universe_instance option ->
  universe_instance in_universe_context_set

val fresh_sort_in_family : env -> sorts_family -> 
  sorts in_universe_context_set
val fresh_constant_instance : env -> constant ->
  pconstant in_universe_context_set
val fresh_inductive_instance : env -> inductive ->
  pinductive in_universe_context_set
val fresh_constructor_instance : env -> constructor ->
  pconstructor in_universe_context_set

val fresh_global_instance : ?names:Univ.Instance.t -> env -> Globnames.global_reference -> 
  constr in_universe_context_set

val fresh_global_or_constr_instance : env -> Globnames.global_reference_or_constr -> 
  constr in_universe_context_set

(** Get fresh variables for the universe context.
    Useful to make tactics that manipulate constrs in universe contexts polymorphic. *)
val fresh_universe_context_set_instance : universe_context_set -> 
  universe_level_subst * universe_context_set

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

(** ** DEPRECATED ** synonym of [constr_of_global] *)
val constr_of_reference : Globnames.global_reference -> constr

(** [unsafe_constr_of_global gr] turns [gr] into a constr, works on polymorphic
    references by taking the original universe instance that is not recorded 
    anywhere. The constraints are forgotten as well. DO NOT USE in new code. *)
val unsafe_constr_of_global : Globnames.global_reference -> constr in_universe_context

(** Returns the type of the global reference, by creating a fresh instance of polymorphic 
    references and computing their instantiated universe context. (side-effect on the
    universe counter, use with care). *)
val type_of_global : Globnames.global_reference -> types in_universe_context_set

(** [unsafe_type_of_global gr] returns [gr]'s type, works on polymorphic
    references by taking the original universe instance that is not recorded 
    anywhere. The constraints are forgotten as well. 
    USE with care. *)
val unsafe_type_of_global : Globnames.global_reference -> types

(** Full universes substitutions into terms *)

val nf_evars_and_universes_opt_subst : (existential -> constr option) -> 
  universe_opt_subst -> constr -> constr

(** Shrink a universe context to a restricted set of variables *)

val universes_of_constr : constr -> universe_set
val restrict_universe_context : universe_context_set -> universe_set -> universe_context_set
val simplify_universe_context : universe_context_set -> 
  universe_context_set * universe_level_subst

val refresh_constraints : universes -> universe_context_set -> universe_context_set * universes

(** Pretty-printing *)

val pr_universe_opt_subst : universe_opt_subst -> Pp.std_ppcmds

(* For tracing *)

type constraints_map = (Univ.constraint_type * Univ.LMap.key) list Univ.LMap.t

val pr_constraints_map : constraints_map -> Pp.std_ppcmds

val choose_canonical : universe_set -> (Level.t -> bool) (* flexibles *) -> universe_set -> universe_set -> 
  universe_level * (universe_set * universe_set * universe_set)
    
val compute_lbound : (constraint_type * Univ.universe) list -> universe option

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

val minimize_univ_variables : 
           Univ.LSet.t ->
           Univ.universe option Univ.LMap.t ->
           Univ.LSet.t ->
  constraints_map -> constraints_map ->
           Univ.constraints ->
           Univ.LSet.t * Univ.universe option Univ.LMap.t *
	     Univ.LSet.t *
           (bool * bool * Univ.universe) Univ.LMap.t * Univ.constraints

(** {6 Support for old-style sort-polymorphism } *)

val solve_constraints_system : universe option array -> universe array -> universe array ->
  universe array
