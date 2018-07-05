(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Constr
open Univ

val level_subst_of : universe_subst_fn -> universe_level_subst_fn
val subst_univs_constraints : universe_subst_fn -> Constraint.t -> Constraint.t

val subst_univs_constr : universe_subst -> constr -> constr

type universe_opt_subst = Universe.t option universe_map

val make_opt_subst : universe_opt_subst -> universe_subst_fn

val subst_opt_univs_constr : universe_opt_subst -> constr -> constr

val normalize_univ_variables : universe_opt_subst ->
  universe_opt_subst * LSet.t * universe_subst

val normalize_univ_variable :
  find:(Level.t -> Universe.t) ->
  Level.t -> Universe.t

val normalize_univ_variable_opt_subst : universe_opt_subst ->
  (Level.t -> Universe.t)

val normalize_univ_variable_subst : universe_subst ->
  (Level.t -> Universe.t)

val normalize_universe_opt_subst : universe_opt_subst ->
  (Universe.t -> Universe.t)

val normalize_universe_subst : universe_subst ->
  (Universe.t -> Universe.t)

val normalize_opt_subst : universe_opt_subst -> universe_opt_subst

(** Full universes substitutions into terms *)

val nf_evars_and_universes_opt_subst : (existential -> constr option) ->
  universe_opt_subst -> constr -> constr

(** Pretty-printing *)

val pr_universe_opt_subst : universe_opt_subst -> Pp.t
