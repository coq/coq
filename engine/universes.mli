(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Names
open Constr
open Environ
open Univ

val set_minimization : bool ref
val is_set_minimization : unit -> bool

(** Universes *)

val pr_with_global_universes : Level.t -> Pp.t
val reference_of_level : Level.t -> Libnames.reference

(** Global universe information outside the kernel, to handle
    polymorphic universes in sections that have to be discharged. *)
val add_global_universe : Level.t -> Decl_kinds.polymorphic -> unit

val is_polymorphic : Level.t -> bool

(** Local universe name <-> level mapping *)

type universe_binders = Univ.Level.t Names.Id.Map.t

val empty_binders : universe_binders

val register_universe_binders : Globnames.global_reference -> universe_binders -> unit
val universe_binders_of_global : Globnames.global_reference -> universe_binders

type univ_name_list = Name.t Loc.located list

(** [universe_binders_with_opt_names ref u l]

    If [l] is [Some univs] return the universe binders naming the levels of [u] by [univs] (skipping Anonymous).
    May error if the lengths mismatch.

    Otherwise return [universe_binders_of_global ref]. *)
val universe_binders_with_opt_names : Globnames.global_reference ->
  Univ.Level.t list -> univ_name_list option -> universe_binders

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

(** {6 Constraints for type inference}

    When doing conversion of universes, not only do we have =/<= constraints but
    also Lub constraints which correspond to unification of two levels which might
    not be necessary if unfolding is performed.
*)

type universe_constraint_type = ULe | UEq | ULub

type universe_constraint = Universe.t * universe_constraint_type * Universe.t
module Constraints : sig
  include Set.S with type elt = universe_constraint

  val pr : t -> Pp.t
end

type universe_constraints = Constraints.t
[@@ocaml.deprecated "Use Constraints.t"]

type 'a constraint_accumulator = Constraints.t -> 'a -> 'a option
type 'a universe_constrained = 'a * Constraints.t
type 'a universe_constraint_function = 'a -> 'a -> Constraints.t -> Constraints.t

val subst_univs_universe_constraints : universe_subst_fn -> 
  Constraints.t -> Constraints.t

val enforce_eq_instances_univs : bool -> Instance.t universe_constraint_function

val to_constraints : UGraph.t -> Constraints.t -> Constraint.t

(** [eq_constr_univs_infer_With kind1 kind2 univs m n] is a variant of
    {!eq_constr_univs_infer} taking kind-of-term functions, to expose
    subterms of [m] and [n], arguments. *)
val eq_constr_univs_infer_with :
  (constr -> (constr, types, Sorts.t, Univ.Instance.t) kind_of_term) ->
  (constr -> (constr, types, Sorts.t, Univ.Instance.t) kind_of_term) ->
  UGraph.t -> 'a constraint_accumulator -> constr -> constr -> 'a -> 'a option

(** [eq_constr_universes a b] [true, c] if [a] equals [b] modulo alpha, casts,
    application grouping and the universe constraints in [c]. *)
val eq_constr_universes_proj : env -> constr -> constr -> bool universe_constrained

(** Build a fresh instance for a given context, its associated substitution and 
    the instantiated constraints. *)

val fresh_instance_from_context : AUContext.t -> 
  Instance.t constrained

val fresh_instance_from : AUContext.t -> Instance.t option ->
  Instance.t in_universe_context_set

val fresh_sort_in_family : env -> Sorts.family -> 
  Sorts.t in_universe_context_set
val fresh_constant_instance : env -> Constant.t ->
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
val fresh_universe_context_set_instance : ContextSet.t -> 
  universe_level_subst * ContextSet.t

(** Raises [Not_found] if not a global reference. *)
val global_of_constr : constr -> Globnames.global_reference puniverses

val constr_of_global_univ : Globnames.global_reference puniverses -> constr

val extend_context : 'a in_universe_context_set -> ContextSet.t -> 
  'a in_universe_context_set

(** Simplification and pruning of constraints:
    [normalize_context_set ctx us]

    - Instantiate the variables in [us] with their most precise
    universe levels respecting the constraints.

    - Normalizes the context [ctx] w.r.t. equality constraints, 
    choosing a canonical universe in each equivalence class 
    (a global one if there is one) and transitively saturate
    the constraints w.r.t to the equalities. *)

module UF : Unionfind.PartitionSig with type elt = Level.t

type universe_opt_subst = Universe.t option universe_map

val make_opt_subst : universe_opt_subst -> universe_subst_fn

val subst_opt_univs_constr : universe_opt_subst -> constr -> constr

val normalize_context_set : ContextSet.t -> 
  universe_opt_subst (* The defined and undefined variables *) ->
  LSet.t (* univ variables that can be substituted by algebraics *) -> 
  (universe_opt_subst * LSet.t) in_universe_context_set

val normalize_univ_variables : universe_opt_subst -> 
  universe_opt_subst * LSet.t * LSet.t * universe_subst

val normalize_univ_variable : 
  find:(Level.t -> Universe.t) ->
  update:(Level.t -> Universe.t -> Universe.t) ->
  Level.t -> Universe.t

val normalize_univ_variable_opt_subst : universe_opt_subst ref ->
  (Level.t -> Universe.t)

val normalize_univ_variable_subst : universe_subst ref ->
  (Level.t -> Universe.t)

val normalize_universe_opt_subst : universe_opt_subst ref ->
  (Universe.t -> Universe.t)

val normalize_universe_subst : universe_subst ref ->
  (Universe.t -> Universe.t)

(** Create a fresh global in the global environment, without side effects.
    BEWARE: this raises an ANOMALY on polymorphic constants/inductives: 
    the constraints should be properly added to an evd. 
    See Evd.fresh_global, Evarutil.new_global, and pf_constr_of_global for
    the proper way to get a fresh copy of a global reference. *)
val constr_of_global : Globnames.global_reference -> constr

(** ** DEPRECATED ** synonym of [constr_of_global] *)
val constr_of_reference : Globnames.global_reference -> constr
[@@ocaml.deprecated "synonym of [constr_of_global]"]

(** Returns the type of the global reference, by creating a fresh instance of polymorphic 
    references and computing their instantiated universe context. (side-effect on the
    universe counter, use with care). *)
val type_of_global : Globnames.global_reference -> types in_universe_context_set

(** Full universes substitutions into terms *)

val nf_evars_and_universes_opt_subst : (existential -> constr option) -> 
  universe_opt_subst -> constr -> constr

val refresh_constraints : UGraph.t -> ContextSet.t -> ContextSet.t * UGraph.t

(** Pretty-printing *)

val pr_universe_opt_subst : universe_opt_subst -> Pp.t

(** {6 Support for template polymorphism } *)

val solve_constraints_system : Universe.t option array -> Universe.t array -> Universe.t array ->
  Universe.t array

(** Operations for universe_info_ind *)

(** Given a universe context representing constraints of an inductive
    this function produces a UInfoInd.t that with the trivial subtyping relation. *)
val univ_inf_ind_from_universe_context : UContext.t -> CumulativityInfo.t
