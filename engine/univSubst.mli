(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Constr
open Univ

type 'a universe_map = 'a Level.Map.t
type universe_subst = Universe.t universe_map
type universe_subst_fn = Level.t -> Universe.t
type universe_level_subst_fn = Level.t -> Level.t

val level_subst_of : universe_subst_fn -> universe_level_subst_fn
val subst_univs_constraints : universe_subst_fn -> Constraints.t -> Constraints.t
val subst_instance : universe_level_subst_fn -> Instance.t -> Instance.t

type universe_opt_subst = Universe.t option universe_map

val normalize_univ_variables : universe_opt_subst ->
  universe_opt_subst * Level.Set.t * universe_subst

val normalize_univ_variable_opt_subst : universe_opt_subst ->
  (Level.t -> Universe.t)

val normalize_universe_opt_subst : universe_opt_subst ->
  (Universe.t -> Universe.t)

val normalize_opt_subst : universe_opt_subst -> universe_opt_subst

(** Full universes substitutions into terms *)

val nf_evars_and_universes_opt_subst : (existential -> constr option) ->
  universe_opt_subst -> constr -> constr

val subst_univs_universe : (Level.t -> Universe.t) -> Universe.t -> Universe.t

val pr_universe_subst : universe_subst -> Pp.t

val enforce_eq : Universe.t constraint_function
val enforce_leq : Universe.t constraint_function

val enforce_eq_sort : Sorts.t -> Sorts.t -> Univ.Constraints.t -> Univ.Constraints.t
val enforce_leq_sort : Sorts.t -> Sorts.t -> Univ.Constraints.t -> Univ.Constraints.t

(** Picks an arbitrary set of constraints sufficient to ensure [u <= v]. *)
val enforce_leq_alg_sort : Sorts.t -> Sorts.t -> UGraph.t -> Univ.Constraints.t * UGraph.t
