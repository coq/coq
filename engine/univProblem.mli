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
open UVars

(** {6 Constraints for type inference}

    When doing conversion of universes, not only do we have =/<= constraints but
    also Lub constraints which correspond to unification of two levels which might
    not be necessary if unfolding is performed.

    UWeak constraints come from irrelevant universes in cumulative polymorphism.
*)

type t =
  | QEq of Sorts.Quality.t * Sorts.Quality.t
  | QLeq of Sorts.Quality.t * Sorts.Quality.t
  | QElimTo of Sorts.Quality.t * Sorts.Quality.t
  | ULe of Sorts.t * Sorts.t
  | UEq of Sorts.t * Sorts.t
  | ULub of UnivConstraint.kind * Universe.t * Universe.t
  | UWeak of Universe.t * Universe.t

val is_trivial : t -> bool

(** Wrapper around the UGraph function to handle Prop *)
val check_eq : UGraph.t -> Universe.t -> Universe.t -> bool

module Set : sig
  include Set.S with type elt = t

  val pr : t -> Pp.t

  (** Replace ULub constraints by UEq *)
  val force : t -> t
end

type 'a constraint_function = 'a -> 'a -> Set.t -> Set.t

val enforce_eq_instances_univs : bool -> Instance.t constraint_function

val enforce_eq_qualities : Sorts.Quality.t array constraint_function

val compare_cumulative_instances : ?flex:bool -> Conversion.conv_pb -> nargs:application -> Variances.t -> Instance.t constraint_function
