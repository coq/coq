(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
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

module Make (Level:Point) : sig

  type t

  val empty : t

  val check_invariants : required_canonical:(Level.t -> bool) -> t -> unit

  exception AlreadyDeclared
  val add : ?rank:int -> Level.t -> t -> t
  (** Use a large [rank] to keep the node canonical *)

  exception Undeclared of Level.t
  val check_declared : t -> Level.Set.t -> unit

  type 'a check_function = t -> 'a -> 'a -> bool

  val check_eq : Level.t check_function
  val check_leq : Level.t check_function
  val check_lt : Level.t check_function

  val enforce_eq : Level.t -> Level.t -> t -> t
  val enforce_leq : Level.t -> Level.t -> t -> t
  val enforce_lt : Level.t -> Level.t -> t -> t

  val constraints_of : t -> Level.Constraint.t * Level.Set.t list

  val constraints_for : kept:Level.Set.t -> t -> Level.Constraint.t

  val domain : t -> Level.Set.t

  val choose : (Level.t -> bool) -> t -> Level.t -> Level.t option

  val sort : (int -> Level.t) -> Level.t list -> t -> t
  (** [sort make_dummy points g] sorts [g]. The [points] are the first
     in the result graph. If the graph is bigger than the list, the
     rest is named according to [make_dummy]. *)

  val pr : (Level.t -> Pp.t) -> t -> Pp.t

  val dump : (constraint_type -> Level.t -> Level.t -> unit) -> t -> unit
end
