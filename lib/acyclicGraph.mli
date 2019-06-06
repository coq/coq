(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Graphs representing strict orders *)

type constraint_type = Lt | Le | Eq

module type Point = sig
  type t

  module Set : CSig.SetS with type elt = t
  module Map : CMap.ExtS with type key = t and module Set := Set

  module Constraint : CSet.S with type elt = (t * constraint_type * t)

  val equal : t -> t -> bool
  val compare : t -> t -> int

  type explanation = (constraint_type * t) list
  val error_inconsistency : constraint_type -> t -> t -> explanation lazy_t option -> 'a

  val pr : t -> Pp.t
end

module Make (Point:Point) : sig

  type t

  val empty : t

  val check_invariants : required_canonical:(Point.t -> bool) -> t -> unit

  exception AlreadyDeclared
  val add : ?rank:int -> Point.t -> t -> t
  (** All points must be pre-declared through this function before
     they can be mentioned in the others. NB: use a large [rank] to
     keep the node canonical *)

  exception Undeclared of Point.t
  val check_declared : t -> Point.Set.t -> unit
  (** @raise Undeclared if one of the points is not present in the graph. *)

  type 'a check_function = t -> 'a -> 'a -> bool

  val check_eq : Point.t check_function
  val check_leq : Point.t check_function
  val check_lt : Point.t check_function

  val enforce_eq : Point.t -> Point.t -> t -> t
  val enforce_leq : Point.t -> Point.t -> t -> t
  val enforce_lt : Point.t -> Point.t -> t -> t

  val constraints_of : t -> Point.Constraint.t * Point.Set.t list

  val constraints_for : kept:Point.Set.t -> t -> Point.Constraint.t

  val domain : t -> Point.Set.t

  val choose : (Point.t -> bool) -> t -> Point.t -> Point.t option

  val sort : (int -> Point.t) -> Point.t list -> t -> t
  (** [sort mk first g] builds a totally ordered graph. The output
     graph should imply the input graph (and the implication will be
     strict most of the time), but is not necessarily minimal. The
     lowest points in the result are identified with [first].
     Moreover, it adds levels [Type.n] to identify the points (not in
     [first]) at level n. An artificial constraint (last first < mk
     (length first)) is added to ensure that they are not merged.
     Note: the result is unspecified if the input graph already
     contains [mk n] nodes. *)

  val pr : (Point.t -> Pp.t) -> t -> Pp.t

  val dump : (constraint_type -> Point.t -> Point.t -> unit) -> t -> unit
end
