(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Graphs representing strict orders *)

type constraint_type = Lt | Le | Eq

module type Point = sig
  type t

  module Set : CSig.USetS with type elt = t
  module Map : CMap.UExtS with type key = t and module Set := Set

  val equal : t -> t -> bool
  val compare : t -> t -> int

  val raw_pr : t -> Pp.t
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

  val check_declared : t -> Point.Set.t -> (unit, Point.Set.t) result
  (** @raise Undeclared if one of the points is not present in the graph. *)

  type 'a check_function = t -> 'a -> 'a -> bool

  val check_eq : Point.t check_function
  val check_leq : Point.t check_function
  val check_lt : Point.t check_function

  val enforce_eq : Point.t -> Point.t -> t -> t option
  val enforce_leq : Point.t -> Point.t -> t -> t option
  val enforce_lt : Point.t -> Point.t -> t -> t option

  (** Type explanation is used to decorate error messages to provide a
      useful explanation why a given constraint is rejected. It is composed
      of a starting universe [u0] and a path of universes and relation kinds
      [(r1,u1);..;(rn,un)] meaning [u0 <(r1) u1 <(r2) ... <(rn) un]
      (where [<(ri)] is the relation symbol denoted by ri).
      When the rejected constraint is a [a <= b] or [a < b] then the path is from[b] to [a],
      ie [u0 == b] and [un == a].
      when the rejected constraint is an equality the path may go in either direction.
      Note that each step does not necessarily correspond to an actual constraint,
      but reflect how the system stores the graph
      and may result from combination of several Constraints.t...
  *)
  type explanation = Point.t * (constraint_type * Point.t) list

  val get_explanation : (Point.t * constraint_type * Point.t) -> t -> explanation
  (** Assuming that the corresponding call to [enforce_*] returned [None], this
      will give a trace for the failure. *)

  type 'a constraint_fold = Point.t * constraint_type * Point.t -> 'a -> 'a

  val constraints_of : t -> 'a constraint_fold -> 'a -> 'a * Point.Set.t list

  val constraints_for : kept:Point.Set.t -> t -> 'a constraint_fold -> 'a -> 'a

  val domain : t -> Point.Set.t

  val choose : (Point.t -> bool) -> t -> Point.t -> Point.t option

  (** {5 High-level representation} *)

  type node =
  | Alias of Point.t
  | Node of bool Point.Map.t (** Nodes v s.t. u < v (true) or u <= v (false) *)
  type repr = node Point.Map.t
  val repr : t -> repr

end
