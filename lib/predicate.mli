
(*i $Id$ i*)

(* Module [Pred]: sets over infinite ordered types with complement. *)

(* This module implements the set data structure, given a total ordering
   function over the set elements. All operations over sets
   are purely applicative (no side-effects).
   The implementation uses the Set library. *)

module type OrderedType =
  sig
    type t
    val compare: t -> t -> int
  end
          (* The input signature of the functor [Pred.Make].
             [t] is the type of the set elements.
             [compare] is a total ordering function over the set elements.
             This is a two-argument function [f] such that
             [f e1 e2] is zero if the elements [e1] and [e2] are equal,
             [f e1 e2] is strictly negative if [e1] is smaller than [e2],
             and [f e1 e2] is strictly positive if [e1] is greater than [e2].
             Example: a suitable ordering function is
             the generic structural comparison function [compare]. *)

module type S =
  sig
    type elt
          (* The type of the set elements. *)
    type t
          (* The type of sets. *)
    val empty: t
          (* The empty set. *)
    val full: t
          (* The whole type. *)
    val is_empty: t -> bool
        (* Test whether a set is empty or not. *)
    val is_full: t -> bool
        (* Test whether a set contains the whole type or not. *)
    val mem: elt -> t -> bool
        (* [mem x s] tests whether [x] belongs to the set [s]. *)
    val singleton: elt -> t
        (* [singleton x] returns the one-element set containing only [x]. *)
    val add: elt -> t -> t
        (* [add x s] returns a set containing all elements of [s],
           plus [x]. If [x] was already in [s], [s] is returned unchanged. *)
    val remove: elt -> t -> t
        (* [remove x s] returns a set containing all elements of [s],
           except [x]. If [x] was not in [s], [s] is returned unchanged. *)
    val union: t -> t -> t
    val inter: t -> t -> t
    val diff: t -> t -> t
    val complement: t -> t
        (* Union, intersection, difference and set complement. *)
    val equal: t -> t -> bool
        (* [equal s1 s2] tests whether the sets [s1] and [s2] are
           equal, that is, contain equal elements. *)
    val subset: t -> t -> bool
        (* [subset s1 s2] tests whether the set [s1] is a subset of
           the set [s2]. *)
    val elements: t -> bool * elt list
        (* Gives a finite representation of the predicate: if the
           boolean is false, then the predicate is given in extension.
           if it is true, then the complement is given *)
  end

module Make(Ord: OrderedType): (S with type elt = Ord.t)
        (* Functor building an implementation of the set structure
           given a totally ordered type. *)
