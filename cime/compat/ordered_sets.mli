(***************************************************************************

Sets over ordered sets. Same as the standard set module of ocaml, but
polymorphic and allow extraction of min and max

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

module type OrderedSet =
sig
  type 'a elt
  type 'a t
  val empty: 'a t
    (* The empty set. *)
  val is_empty: 'a t -> bool
      (* Test whether a set is empty or not. *)
  val mem: 'a elt -> 'a t -> bool
      (* [mem x s] tests whether [x] belongs to the set [s]. *)
  val add: 'a elt -> 'a t -> 'a t
      (* [add x s] returns a set containing all elements of [s],
         plus [x]. If [x] was already in [s], [s] is returned unchanged. *)
  val singleton: 'a elt -> 'a t
      (* [singleton x] returns a set containing [x]. *)
  val remove: 'a elt -> 'a t -> 'a t
      (* [remove x s] returns a set containing all elements of [s],
         except [x]. If [x] was not in [s], [s] is returned unchanged. *)
  val union: 'a t -> 'a t -> 'a t
  val inter: 'a t -> 'a t -> 'a t
  val diff: 'a t -> 'a t -> 'a t
      (* Union, intersection and set difference. *)
  val compare: 'a t -> 'a t -> int
      (* Total ordering between sets. Can be used as the ordering function
         for doing sets of sets. *)
  val equal: 'a t -> 'a t -> bool
      (* [equal s1 s2] tests whether the sets [s1] and [s2] are
         equal, that is, contain the same elements. *)
  val subset: 'a t -> 'a t -> bool
      (* [subset s1 s2] tests whether the set [s1] is a subset of
         the set [s2]. *)
  val iter: ('a elt -> unit) -> 'a t -> unit
      (* [iter f s] applies [f] in turn to all elements of [s].
         The order in which the elements of [s] are presented to [f]
         is unspecified. *)
  val fold: ('a elt -> 'b -> 'b) -> 'a t -> 'b -> 'b
      (* [fold f s a] computes [(f xN ... (f x2 (f x1 a))...)],
         where [x1 ... xN] are the elements of [s].
         The order in which elements of [s] are presented to [f] is
         unspecified. *)
  val filter: ('a elt -> bool) -> 'a t -> 'a t
      (* [filter p s returns the set of all elements in s that 
	 satisfy predicate p. *)
  val cardinal: 'a t -> int
      (* Return the number of elements of a set. *)
  val elements: 'a t -> 'a elt list
      (* Return the list of all elements of the given set.
         The elements appear in the list in some unspecified order. *)
  val choose: 'a t -> 'a elt
      (* Return one element of the given set, or raise [Not_found] if
         the set is empty. Which element is chosen is unspecified,
         but equal elements will be chosen for equal sets. *)
  val min_elt: 'a t -> 'a elt
      (* Return the smallest element of the given set, or raise 
	 [Not_found] if the set is empty.  *)
  val find : ('a elt -> bool) -> 'a t -> 'a elt
  val exists : ('a elt -> bool) -> 'a t -> bool
end

module Make(Ord: Ordered_types.OrderedType): 
  (OrderedSet with type 'a elt = Ord.t)
        (* Functor building an implementation of the set structure
           given a totally ordered type. *)

module MakePoly(Ord: Ordered_types.OrderedPolyType): 
  (OrderedSet with type 'a elt = 'a Ord.t)
        (* Functor building an implementation of the set structure
           given a totally ordered polymorphic type. *)


