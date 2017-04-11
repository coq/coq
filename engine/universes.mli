(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Names
open Term
open Environ
open Univ

val set_minimization : bool ref
val is_set_minimization : unit -> bool

(** Universes *)

val pr_with_global_universes : Level.t -> Pp.std_ppcmds

(** Local universe name <-> level mapping *)

type universe_binders = (Id.t * Univ.universe_level) list
					   
val register_universe_binders : Globnames.global_reference -> universe_binders -> unit
val universe_binders_of_global : Globnames.global_reference -> universe_binders

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
type 'a constraint_accumulator = universe_constraints -> 'a -> 'a option
type 'a universe_constrained = 'a * universe_constraints
type 'a universe_constraint_function = 'a -> 'a -> universe_constraints -> universe_constraints

val subst_univs_universe_constraints : universe_subst_fn -> 
  universe_constraints -> universe_constraints

val enforce_eq_instances_univs : bool -> universe_instance universe_constraint_function

val to_constraints : UGraph.t -> universe_constraints -> constraints

(** [eq_constr_univs_infer u a b] is [true, c] if [a] equals [b] modulo alpha, casts,
   application grouping, the universe constraints in [u] and additional constraints [c]. *)
val eq_constr_univs_infer : UGraph.t -> 'a constraint_accumulator ->
  constr -> constr -> 'a -> 'a option

(** [eq_constr_univs_infer_With kind1 kind2 univs m n] is a variant of
    {!eq_constr_univs_infer} taking kind-of-term functions, to expose
    subterms of [m] and [n], arguments. *)
val eq_constr_univs_infer_with :
  (constr -> (constr, types, Sorts.t, Univ.Instance.t) kind_of_term) ->
  (constr -> (constr, types, Sorts.t, Univ.Instance.t) kind_of_term) ->
  UGraph.t -> 'a constraint_accumulator -> constr -> constr -> 'a -> 'a option

(** [leq_constr_univs u a b] is [true, c] if [a] is convertible to [b]
    modulo alpha, casts, application grouping, the universe constraints
    in [u] and additional constraints [c]. *)
val leq_constr_univs_infer : UGraph.t -> 'a constraint_accumulator ->
  constr -> constr -> 'a -> 'a option

(** [eq_constr_universes a b] [true, c] if [a] equals [b] modulo alpha, casts,
    application grouping and the universe constraints in [c]. *)
val eq_constr_universes : constr -> constr -> universe_constraints option

(** [leq_constr_universes a b] [true, c] if [a] is convertible to [b] modulo
    alpha, casts, application grouping and the universe constraints in [c]. *)
val leq_constr_universes : constr -> constr -> universe_constraints option

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

val refresh_constraints : UGraph.t -> universe_context_set -> universe_context_set * UGraph.t

(** Pretty-printing *)

val pr_universe_opt_subst : universe_opt_subst -> Pp.std_ppcmds

(** {6 Support for template polymorphism } *)

val solve_constraints_system : universe option array -> universe array -> universe array ->
  universe array
