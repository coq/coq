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

(** ************************************** *)
(** This entire module is deprecated. **** *)
(** ************************************** *)
[@@@ocaml.warning "-3"]

(** ****** Deprecated: moved to [UnivNames] *)

val pr_with_global_universes : Level.t -> Pp.t
[@@ocaml.deprecated "Use [UnivNames.pr_with_global_universes]"]
val reference_of_level : Level.t -> Libnames.qualid
[@@ocaml.deprecated "Use [UnivNames.qualid_of_level]"]

val add_global_universe : Level.t -> Decl_kinds.polymorphic -> unit
[@@ocaml.deprecated "Use [UnivNames.add_global_universe]"]

val is_polymorphic : Level.t -> bool
[@@ocaml.deprecated "Use [UnivNames.is_polymorphic]"]

type universe_binders = UnivNames.universe_binders
[@@ocaml.deprecated "Use [UnivNames.universe_binders]"]

val empty_binders : universe_binders
[@@ocaml.deprecated "Use [UnivNames.empty_binders]"]

val register_universe_binders : Globnames.global_reference -> universe_binders -> unit
[@@ocaml.deprecated "Use [UnivNames.register_universe_binders]"]
val universe_binders_of_global : Globnames.global_reference -> universe_binders
[@@ocaml.deprecated "Use [UnivNames.universe_binders_of_global]"]

type univ_name_list = UnivNames.univ_name_list
[@@ocaml.deprecated "Use [UnivNames.univ_name_list]"]

val universe_binders_with_opt_names : Globnames.global_reference ->
  Univ.Level.t list -> univ_name_list option -> universe_binders
[@@ocaml.deprecated "Use [UnivNames.universe_binders_with_opt_names]"]

(** ****** Deprecated: moved to [UnivGen] *)

type universe_id = UnivGen.universe_id
[@@ocaml.deprecated "Use [UnivGen.universe_id]"]

val set_remote_new_univ_id : universe_id RemoteCounter.installer
[@@ocaml.deprecated "Use [UnivGen.set_remote_new_univ_id]"]

val new_univ_id : unit -> universe_id
[@@ocaml.deprecated "Use [UnivGen.new_univ_id]"]

val new_univ_level : unit -> Level.t
[@@ocaml.deprecated "Use [UnivGen.new_univ_level]"]

val new_univ : unit -> Universe.t
[@@ocaml.deprecated "Use [UnivGen.new_univ]"]

val new_Type : unit -> types
[@@ocaml.deprecated "Use [UnivGen.new_Type]"]

val new_Type_sort : unit -> Sorts.t
[@@ocaml.deprecated "Use [UnivGen.new_Type_sort]"]

val new_global_univ : unit -> Universe.t in_universe_context_set
[@@ocaml.deprecated "Use [UnivGen.new_global_univ]"]

val new_sort_in_family : Sorts.family -> Sorts.t
[@@ocaml.deprecated "Use [UnivGen.new_sort_in_family]"]

val fresh_instance_from_context : AUContext.t ->
  Instance.t constrained
[@@ocaml.deprecated "Use [UnivGen.fresh_instance_from_context]"]

val fresh_instance_from : AUContext.t -> Instance.t option ->
  Instance.t in_universe_context_set
[@@ocaml.deprecated "Use [UnivGen.fresh_instance_from]"]

val fresh_sort_in_family : Sorts.family ->
  Sorts.t in_universe_context_set
[@@ocaml.deprecated "Use [UnivGen.fresh_sort_in_family]"]

val fresh_constant_instance : env -> Constant.t ->
  pconstant in_universe_context_set
[@@ocaml.deprecated "Use [UnivGen.fresh_constant_instance]"]

val fresh_inductive_instance : env -> inductive ->
  pinductive in_universe_context_set
[@@ocaml.deprecated "Use [UnivGen.fresh_inductive_instance]"]

val fresh_constructor_instance : env -> constructor ->
  pconstructor in_universe_context_set
[@@ocaml.deprecated "Use [UnivGen.fresh_constructor_instance]"]

val fresh_global_instance : ?names:Univ.Instance.t -> env -> Globnames.global_reference ->
  constr in_universe_context_set
[@@ocaml.deprecated "Use [UnivGen.fresh_global_instance]"]

val fresh_global_or_constr_instance : env -> Globnames.global_reference_or_constr ->
  constr in_universe_context_set
[@@ocaml.deprecated "Use [UnivGen.fresh_global_or_constr_instance]"]

val fresh_universe_context_set_instance : ContextSet.t ->
  universe_level_subst * ContextSet.t
[@@ocaml.deprecated "Use [UnivGen.fresh_universe_context_set_instance]"]

val global_of_constr : constr -> Globnames.global_reference puniverses
[@@ocaml.deprecated "Use [UnivGen.global_of_constr]"]

val constr_of_global_univ : Globnames.global_reference puniverses -> constr
[@@ocaml.deprecated "Use [UnivGen.constr_of_global_univ]"]

val extend_context : 'a in_universe_context_set -> ContextSet.t ->
  'a in_universe_context_set
[@@ocaml.deprecated "Use [UnivGen.extend_context]"]

val constr_of_global : Globnames.global_reference -> constr
[@@ocaml.deprecated "Use [UnivGen.constr_of_global]"]

val constr_of_reference : Globnames.global_reference -> constr
[@@ocaml.deprecated "Use [UnivGen.constr_of_global]"]

val type_of_global : Globnames.global_reference -> types in_universe_context_set
[@@ocaml.deprecated "Use [UnivGen.type_of_global]"]

(** ****** Deprecated: moved to [UnivSubst] *)

val level_subst_of : universe_subst_fn -> universe_level_subst_fn
[@@ocaml.deprecated "Use [UnivSubst.level_subst_of]"]

val subst_univs_constraints : universe_subst_fn -> Constraint.t -> Constraint.t
[@@ocaml.deprecated "Use [UnivSubst.subst_univs_constraints]"]

val subst_univs_constr : universe_subst -> constr -> constr
[@@ocaml.deprecated "Use [UnivSubst.subst_univs_constr]"]

type universe_opt_subst = UnivSubst.universe_opt_subst
[@@ocaml.deprecated "Use [UnivSubst.universe_opt_subst]"]

val make_opt_subst : universe_opt_subst -> universe_subst_fn
[@@ocaml.deprecated "Use [UnivSubst.make_opt_subst]"]

val subst_opt_univs_constr : universe_opt_subst -> constr -> constr
[@@ocaml.deprecated "Use [UnivSubst.subst_opt_univs_constr]"]

val normalize_univ_variables : universe_opt_subst ->
  universe_opt_subst * LSet.t * universe_subst
[@@ocaml.deprecated "Use [UnivSubst.normalize_univ_variables]"]

val normalize_univ_variable :
  find:(Level.t -> Universe.t) ->
  Level.t -> Universe.t
[@@ocaml.deprecated "Use [UnivSubst.normalize_univ_variable]"]

val normalize_univ_variable_opt_subst : universe_opt_subst ->
  (Level.t -> Universe.t)
[@@ocaml.deprecated "Use [UnivSubst.normalize_univ_variable_opt_subst]"]

val normalize_univ_variable_subst : universe_subst ->
  (Level.t -> Universe.t)
[@@ocaml.deprecated "Use [UnivSubst.normalize_univ_variable_subst]"]

val normalize_universe_opt_subst : universe_opt_subst ->
  (Universe.t -> Universe.t)
[@@ocaml.deprecated "Use [UnivSubst.normalize_universe_opt_subst]"]

val normalize_universe_subst : universe_subst ->
  (Universe.t -> Universe.t)
[@@ocaml.deprecated "Use [UnivSubst.normalize_universe_subst]"]

val nf_evars_and_universes_opt_subst : (existential -> constr option) ->
  universe_opt_subst -> constr -> constr
[@@ocaml.deprecated "Use [UnivSubst.nf_evars_and_universes_opt_subst]"]

val pr_universe_opt_subst : universe_opt_subst -> Pp.t
[@@ocaml.deprecated "Use [UnivSubst.pr_universe_opt_subst]"]

(** ****** Deprecated: moved to [UnivProblem] *)

type universe_constraint = UnivProblem.t =
  | ULe of Universe.t * Universe.t [@ocaml.deprecated "Use [UnivProblem.ULe]"]
  | UEq of Universe.t * Universe.t [@ocaml.deprecated "Use [UnivProblem.UEq]"]
  | ULub of Level.t * Level.t [@ocaml.deprecated "Use [UnivProblem.ULub]"]
  | UWeak of Level.t * Level.t [@ocaml.deprecated "Use [UnivProblem.UWeak]"]
[@@ocaml.deprecated "Use [UnivProblem.t]"]

module Constraints = UnivProblem.Set
[@@ocaml.deprecated "Use [UnivProblem.Set]"]

type 'a constraint_accumulator = 'a UnivProblem.accumulator
[@@ocaml.deprecated "Use [UnivProblem.accumulator]"]
type 'a universe_constrained = 'a UnivProblem.constrained
[@@ocaml.deprecated "Use [UnivProblem.constrained]"]
type 'a universe_constraint_function = 'a UnivProblem.constraint_function
[@@ocaml.deprecated "Use [UnivProblem.constraint_function]"]

val subst_univs_universe_constraints : universe_subst_fn ->
  Constraints.t -> Constraints.t
[@@ocaml.deprecated "Use [UnivProblem.Set.subst_univs]"]

val enforce_eq_instances_univs : bool -> Instance.t universe_constraint_function
[@@ocaml.deprecated "Use [UnivProblem.enforce_eq_instances_univs]"]

(** With [force_weak] UWeak constraints are turned into equalities,
   otherwise they're forgotten. *)
val to_constraints : force_weak:bool -> UGraph.t -> Constraints.t -> Constraint.t
[@@ocaml.deprecated "Use [UnivProblem.to_constraints]"]

(** [eq_constr_univs_infer_With kind1 kind2 univs m n] is a variant of
    {!eq_constr_univs_infer} taking kind-of-term functions, to expose
    subterms of [m] and [n], arguments. *)
val eq_constr_univs_infer_with :
  (constr -> (constr, types, Sorts.t, Univ.Instance.t) kind_of_term) ->
  (constr -> (constr, types, Sorts.t, Univ.Instance.t) kind_of_term) ->
  UGraph.t -> 'a constraint_accumulator -> constr -> constr -> 'a -> 'a option
[@@ocaml.deprecated "Use [UnivProblem.eq_constr_univs_infer_with]"]

(** ****** Deprecated: moved to [UnivMinim] *)

module UPairSet = UnivMinim.UPairSet
[@@ocaml.deprecated "Use [UnivMinim.UPairSet]"]

val normalize_context_set : UGraph.t -> ContextSet.t ->
  universe_opt_subst (* The defined and undefined variables *) ->
  LSet.t (* univ variables that can be substituted by algebraics *) ->
  UPairSet.t (* weak equality constraints *) ->
  (universe_opt_subst * LSet.t) in_universe_context_set
[@@ocaml.deprecated "Use [UnivMinim.normalize_context_set]"]
