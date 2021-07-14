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

val level_subst_of : universe_subst_fn -> universe_level_subst_fn
val subst_univs_constraints : universe_subst_fn -> Constraints.t -> Constraints.t

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
