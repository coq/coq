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
open UnivSubst

(** Unordered pairs of universe levels (ie (u,v) = (v,u)) *)
module UPairSet : CSet.S with type elt = (Level.t * Level.t)

(** Simplification and pruning of constraints:
    [normalize_context_set ctx us]

    - Instantiate the variables in [us] with their most precise
    universe levels respecting the constraints.

    - Normalizes the context [ctx] w.r.t. equality constraints,
    choosing a canonical universe in each equivalence class
    (a global one if there is one) and transitively saturate
    the constraints w.r.t to the equalities. *)

val normalize_context_set : UGraph.t -> ContextSet.t ->
  universe_opt_subst (* The defined and undefined variables *) ->
  LSet.t (* univ variables that can be substituted by algebraics *) ->
  UPairSet.t (* weak equality constraints *) ->
  (universe_opt_subst * LSet.t) in_universe_context_set
