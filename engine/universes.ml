(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Univ

(** Deprecated *)

(** UnivNames *)
type universe_binders = UnivNames.universe_binders
type univ_name_list = UnivNames.univ_name_list

let pr_with_global_universes = UnivNames.pr_with_global_universes
let reference_of_level = UnivNames.qualid_of_level

let add_global_universe = UnivNames.add_global_universe

let is_polymorphic = UnivNames.is_polymorphic

let empty_binders = UnivNames.empty_binders

let register_universe_binders = UnivNames.register_universe_binders
let universe_binders_of_global = UnivNames.universe_binders_of_global

let universe_binders_with_opt_names = UnivNames.universe_binders_with_opt_names

(** UnivGen *)
type universe_id = UnivGen.universe_id

let set_remote_new_univ_id = UnivGen.set_remote_new_univ_id
let new_univ_id = UnivGen.new_univ_id
let new_univ_level = UnivGen.new_univ_level
let new_univ = UnivGen.new_univ
let new_Type = UnivGen.new_Type
let new_Type_sort = UnivGen.new_Type_sort
let new_global_univ = UnivGen.new_global_univ
let new_sort_in_family = UnivGen.new_sort_in_family
let fresh_instance_from_context = UnivGen.fresh_instance_from_context
let fresh_instance_from = UnivGen.fresh_instance_from
let fresh_sort_in_family = UnivGen.fresh_sort_in_family
let fresh_constant_instance = UnivGen.fresh_constant_instance
let fresh_inductive_instance = UnivGen.fresh_inductive_instance
let fresh_constructor_instance = UnivGen.fresh_constructor_instance
let fresh_global_instance = UnivGen.fresh_global_instance
let fresh_global_or_constr_instance = UnivGen.fresh_global_or_constr_instance
let fresh_universe_context_set_instance = UnivGen.fresh_universe_context_set_instance
let global_of_constr = UnivGen.global_of_constr
let constr_of_global_univ = UnivGen.constr_of_global_univ
let extend_context = UnivGen.extend_context
let constr_of_global = UnivGen.constr_of_global
let constr_of_reference = UnivGen.constr_of_global
let type_of_global = UnivGen.type_of_global

(** UnivSubst *)

let level_subst_of = UnivSubst.level_subst_of
let subst_univs_constraints = UnivSubst.subst_univs_constraints
let subst_univs_constr = UnivSubst.subst_univs_constr
type universe_opt_subst = UnivSubst.universe_opt_subst
let make_opt_subst = UnivSubst.make_opt_subst
let subst_opt_univs_constr = UnivSubst.subst_opt_univs_constr
let normalize_univ_variables = UnivSubst.normalize_univ_variables
let normalize_univ_variable = UnivSubst.normalize_univ_variable
let normalize_univ_variable_opt_subst = UnivSubst.normalize_univ_variable_opt_subst
let normalize_univ_variable_subst = UnivSubst.normalize_univ_variable_subst
let normalize_universe_opt_subst = UnivSubst.normalize_universe_opt_subst
let normalize_universe_subst = UnivSubst.normalize_universe_subst
let nf_evars_and_universes_opt_subst = UnivSubst.nf_evars_and_universes_opt_subst
let pr_universe_opt_subst = UnivSubst.pr_universe_opt_subst

(** UnivProblem *)

type universe_constraint = UnivProblem.t =
  | ULe of Universe.t * Universe.t
  | UEq of Universe.t * Universe.t
  | ULub of Level.t * Level.t
  | UWeak of Level.t * Level.t

module Constraints = UnivProblem.Set
type 'a constraint_accumulator = 'a UnivProblem.accumulator
type 'a universe_constrained = 'a UnivProblem.constrained
type 'a universe_constraint_function = 'a UnivProblem.constraint_function
let subst_univs_universe_constraints = UnivProblem.Set.subst_univs
let enforce_eq_instances_univs = UnivProblem.enforce_eq_instances_univs
let to_constraints = UnivProblem.to_constraints
let eq_constr_univs_infer_with = UnivProblem.eq_constr_univs_infer_with

(** UnivMinim *)
module UPairSet = UnivMinim.UPairSet

let normalize_context_set = UnivMinim.normalize_context_set
