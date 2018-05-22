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

  val subst_univs : universe_subst_fn -> t -> t
end

type 'a accumulator = Set.t -> 'a -> 'a option
type 'a constrained = 'a * Set.t
type 'a constraint_function = 'a -> 'a -> Set.t -> Set.t

val enforce_eq_instances_univs : bool -> Instance.t constraint_function

(** With [force_weak] UWeak constraints are turned into equalities,
   otherwise they're forgotten. *)
val to_constraints : force_weak:bool -> UGraph.t -> Set.t -> Constraint.t

(** [eq_constr_univs_infer_With kind1 kind2 univs m n] is a variant of
    {!eq_constr_univs_infer} taking kind-of-term functions, to expose
    subterms of [m] and [n], arguments. *)
val eq_constr_univs_infer_with :
  (constr -> (constr, types, Sorts.t, Univ.Instance.t) kind_of_term) ->
  (constr -> (constr, types, Sorts.t, Univ.Instance.t) kind_of_term) ->
  UGraph.t -> 'a accumulator -> constr -> constr -> 'a -> 'a option
