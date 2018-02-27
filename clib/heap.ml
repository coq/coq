(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*s Heaps *)

module type Ordered = sig
  type t
  val compare : t -> t -> int
end

module type S =sig

  (* Type of functional heaps *)
  type t

  (* Type of elements *)
  type elt

  (* The empty heap *)
  val empty : t

  (* [add x h] returns a new heap containing the elements of [h], plus [x];
     complexity $O(log(n))$ *)
  val add : elt -> t -> t

  (* [maximum h] returns the maximum element of [h]; raises [EmptyHeap]
     when [h] is empty; complexity $O(1)$ *)
  val maximum : t -> elt

  (* [remove h] returns a new heap containing the elements of [h], except
     the maximum of [h]; raises [EmptyHeap] when [h] is empty;
     complexity $O(log(n))$ *)
  val remove : t -> t

  (* usual iterators and combinators; elements are presented in
     arbitrary order *)
  val iter : (elt -> unit) -> t -> unit

  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a

end

exception EmptyHeap

(*s Functional implementation *)

module Functional(X : Ordered) = struct

  (* Heaps are encoded as Braun trees, that are binary trees
     where size r <= size l <= size r + 1 for each node Node (l, x, r) *)

  type t =
    | Leaf
    | Node of t * X.t * t

  type elt = X.t

  let empty = Leaf

  let rec add x = function
    | Leaf ->
        Node (Leaf, x, Leaf)
    | Node (l, y, r) ->
        if X.compare x y >= 0 then
          Node (add y r, x, l)
        else
          Node (add x r, y, l)

  let rec extract = function
    | Leaf ->
        assert false
    | Node (Leaf, y, r) ->
        assert (r = Leaf);
        y, Leaf
    | Node (l, y, r) ->
        let x, l = extract l in
        x, Node (r, y, l)

  let is_above x = function
    | Leaf -> true
    | Node (_, y, _) -> X.compare x y >= 0

  let rec replace_min x = function
    | Node (l, _, r) when is_above x l && is_above x r ->
        Node (l, x, r)
    | Node ((Node (_, lx, _) as l), _, r) when is_above lx r ->
        (* lx <= x, rx necessarily *)
        Node (replace_min x l, lx, r)
    | Node (l, _, (Node (_, rx, _) as r)) ->
        (* rx <= x, lx necessarily *)
        Node (l, rx, replace_min x r)
    | Leaf | Node (Leaf, _, _) | Node (_, _, Leaf) ->
        assert false

  (* merges two Braun trees [l] and [r],
     with the assumption that [size r <= size l <= size r + 1] *)
  let rec merge l r = match l, r with
    | _, Leaf ->
        l
    | Node (ll, lx, lr), Node (_, ly, _) ->
        if X.compare lx ly >= 0 then
          Node (r, lx, merge ll lr)
        else
          let x, l = extract l in
          Node (replace_min x r, ly, l)
    | Leaf, _ ->
        assert false (* contradicts the assumption *)

  let maximum = function
    | Leaf -> raise EmptyHeap
    | Node (_, x, _) -> x

  let remove = function
    | Leaf ->
        raise EmptyHeap
    | Node (l, _, r) ->
        merge l r

  let rec iter f = function
    | Leaf -> ()
    | Node (l, x, r) -> iter f l; f x; iter f r

  let rec fold f h x0 = match h with
    | Leaf ->
	x0
    | Node (l, x, r) ->
	fold f l (fold f r (f x x0))

end
