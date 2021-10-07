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

val check : UGraph.t -> t -> bool

module Set : sig
  include Set.S with type elt = t

  val pr : t -> Pp.t

  (** Replace ULub constraints by UEq *)
  val force : t -> t

  val check : UGraph.t -> t -> bool
end

type 'a constraint_function = 'a -> 'a -> Set.t -> Set.t

val enforce_eq_instances_univs : bool -> Instance.t constraint_function
