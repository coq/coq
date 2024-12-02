(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Univ

(** Unordered pairs of universe levels (ie (u,v) = (v,u)) *)
module UPairSet : CSet.S with type elt = (Universe.t * Universe.t)

type extra = {
  weak_constraints : UPairSet.t; (* weak equality constraints *)
  above_prop : Level.Set.t;
}

val empty_extra : extra

val extra_union : extra -> extra -> extra

type position =
  | InBinder of int
  | InTerm | InType

(* The position records the last position in the term where the variable was used relevantly. *)
type level_variances = (position * UVars.Variance.t) Univ.Level.Map.t
val pr_variances : (Univ.Level.t -> Pp.t) -> level_variances -> Pp.t

(** Simplification and pruning of constraints:
    [normalize_context_set ctx us]

    - Instantiate the variables in [us] with their most precise
    universe levels respecting the constraints.

    - Normalizes the context [ctx] w.r.t. equality constraints,
    choosing a canonical universe in each equivalence class
    (a global one if there is one) and transitively saturate
    the constraints w.r.t to the equalities. *)

val normalize_context_set : lbound:UGraph.Bound.t -> variances:level_variances -> UGraph.t -> ContextSet.t ->
  UnivFlex.t (* The defined and undefined variables *) ->
  ?binders:UnivNames.universe_binders ->
  extra ->
  UnivFlex.t in_universe_context_set
