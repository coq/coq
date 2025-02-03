(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Constr
open Univ
open Sorts

type 'a universe_map = 'a Level.Map.t
type universe_subst = Universe.t universe_map
type universe_subst_fn = Level.t -> Universe.t option
type universe_level_subst_fn = Level.t -> Level.t

type quality_subst = Quality.t QVar.Map.t
type quality_subst_fn = QVar.t -> Quality.t

val level_subst_of : universe_subst_fn -> universe_level_subst_fn
(** The resulting function must never be called on a level which would produce an algebraic. *)

val subst_univs_constraints : universe_subst_fn -> Constraints.t -> Constraints.t

(** Full universes substitutions into terms *)

val map_universes_opt_subst_with_binders
  : ('a -> 'a)
  -> ('a -> constr -> constr)
  -> (Sorts.relevance -> Sorts.relevance)
  -> quality_subst_fn
  -> universe_subst_fn
  -> 'a -> constr -> constr

val nf_evars_and_universes_opt_subst
  : (existential -> constr option)
  -> (Sorts.relevance -> Sorts.relevance)
  -> quality_subst_fn
  -> universe_subst_fn
  -> constr -> constr
  [@@ocaml.deprecated "(8.20) Use [UnivSubst.map_universes_opt_subst_with_binders]"]

val subst_univs_universe : universe_subst_fn -> Universe.t -> Universe.t

val pr_universe_subst : (Level.t -> Pp.t) -> universe_subst -> Pp.t

val enforce_eq : Universe.t constraint_function
val enforce_leq : Universe.t constraint_function

val enforce_eq_sort : Sorts.t -> Sorts.t -> Univ.Constraints.t -> Univ.Constraints.t
val enforce_leq_sort : Sorts.t -> Sorts.t -> Univ.Constraints.t -> Univ.Constraints.t

(** Picks an arbitrary set of constraints sufficient to ensure [u <= v]. *)
val enforce_leq_alg_sort : Sorts.t -> Sorts.t -> UGraph.t -> Univ.Constraints.t * UGraph.t
