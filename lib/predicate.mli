(** Infinite sets over a chosen [OrderedType].

    All operations over sets are purely applicative (no side-effects).
 *)

(** Input signature of the functor [Make]. *)
module type OrderedType =
  sig
    type t
    (** The type of the elements in the set.

	The chosen [t] {b must be infinite}. *)

    val compare : t -> t -> int
    (** A total ordering function over the set elements.
        This is a two-argument function [f] such that:
        - [f e1 e2] is zero if the elements [e1] and [e2] are equal,
        - [f e1 e2] is strictly negative if [e1] is smaller than [e2],
        - and [f e1 e2] is strictly positive if [e1] is greater than [e2].
     *)
  end

module type S =
  sig
    type elt
    (** The type of the elements in the set. *)

    type t
    (** The type of sets. *)

    val empty: t
    (** The empty set. *)

    val full: t
    (** The set of all elements (of type [elm]). *)

    val is_empty: t -> bool
    (** Test whether a set is empty or not. *)

    val is_full: t -> bool
    (** Test whether a set contains the whole type or not. *)

    val mem: elt -> t -> bool
    (** [mem x s] tests whether [x] belongs to the set [s]. *)

    val singleton: elt -> t
    (** [singleton x] returns the one-element set containing only [x]. *)

    val add: elt -> t -> t
    (** [add x s] returns a set containing all elements of [s],
        plus [x]. If [x] was already in [s], then [s] is returned unchanged. *)

    val remove: elt -> t -> t
        (** [remove x s] returns a set containing all elements of [s],
            except [x]. If [x] was not in [s], then [s] is returned unchanged. *)

    val union: t -> t -> t
    (** Set union. *)

    val inter: t -> t -> t
    (** Set intersection. *)

    val diff: t -> t -> t
    (** Set difference. *)

    val complement: t -> t
    (** Set complement. *)

    val equal: t -> t -> bool
    (** [equal s1 s2] tests whether the sets [s1] and [s2] are
        equal, that is, contain equal elements. *)

    val subset: t -> t -> bool
        (** [subset s1 s2] tests whether the set [s1] is a subset of
            the set [s2]. *)

    val elements: t -> bool * elt list
        (** Gives a finite representation of the predicate: if the
           boolean is false, then the predicate is given in extension.
           if it is true, then the complement is given *)
  end

(** The [Make] functor constructs an implementation for any [OrderedType]. *)
module Make (Ord : OrderedType) : (S with type elt = Ord.t)
