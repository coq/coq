(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Univ

(** {6 Constraints for type inference}

    When doing conversion of universes, not only do we have =/<= constraints but
    also Lub constraints which correspond to unification of two levels which might
    not be necessary if unfolding is performed.

    UWeak constraints come from irrelevant universes in cumulative polymorphism.
*)

type t =
  | ULe of Universe.t * Universe.t
  | UEq of Universe.t * Universe.t
  | ULub of Level.t * Level.t
  | UWeak of Level.t * Level.t

val is_trivial : t -> bool

module Set : sig
  include Set.S with type elt = t

  val pr : t -> Pp.t
end

type 'a accumulator = Set.t -> 'a -> 'a option
type 'a constrained = 'a * Set.t
type 'a constraint_function = 'a -> 'a -> Set.t -> Set.t

val enforce_eq_instances_univs : bool -> Instance.t constraint_function

(** With [force_weak] UWeak constraints are turned into equalities,
   otherwise they're forgotten. *)
val to_constraints : force_weak:bool -> UGraph.t -> Set.t -> Constraint.t
