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
  above_zero : Level.Set.t;
}

val empty_extra : extra

val extra_union : extra -> extra -> extra

val remove_from_extra : Level.Set.t -> extra -> extra

(** Operations on inferred variances *)

val update_variance : InferCumulativity.variances -> Level.t -> Level.t -> InferCumulativity.variances
(** [update_variance variances l l'] merges the variance information of [l] and [l'] in [l'] *)

val update_variances : InferCumulativity.variances -> Level.t -> Level.Set.t -> InferCumulativity.variances
(** [update_variances variances l ls] merges the variance information of [l] in each level in [ls] *)


val sup_variances : InferCumulativity.variances -> Level.Set.t -> InferCumulativity.infer_variance_occurrence
(** [sup_variances variances ls] Computes the supremum of the variance occurrences of all the levels in [ls] *)

val set_variance : InferCumulativity.variances -> Level.t -> InferCumulativity.infer_variance_occurrence -> InferCumulativity.variances
(** [set_variance variances l occ] sets the variance information attached to [l] to [occs] in the result *)

(** Simplification and pruning of constraints:
    [normalize_context_set ctx us]

    - Instantiate the variables in [us] with their most precise
      universe levels respecting the constraints, depending on
      their variance. If [solve_flexibles] is true, arbitrary
      instantiations respecting the constraints on rigid universes
      are performed. Otherwise only instantiations that preserve
      the principality of typing are allowed.

    - Normalizes the context [ctx] w.r.t. equality constraints,
    choosing a canonical universe in each equivalence class
    (a global one if there is one) and transitively saturate
    the constraints w.r.t to the equalities. *)

val normalize_context_set :
  solve_flexibles:bool ->
  variances:InferCumulativity.variances ->
  partial:bool ->
  UGraph.t -> (* The graph representing constraints and a level to universe substitution *)
  local_variables:Level.Set.t -> (* Local variables *)
  flexible_variables:Level.Set.t (* Subset of undefined flexible variables *) ->
  ?binders:UnivNames.universe_binders ->
  extra ->
  (Level.Set.t * (* Local variables *)
   Level.Set.t * (* Remaining flexible variables *)
   InferCumulativity.variances * (* Variances *)
   UGraph.t) (* Minimized graph *)
