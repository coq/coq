(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type 'a tree =
| Leaf of 'a
| Node of 'a * 'a tree * 'a tree

type 'a t = Nil | Cons of int * 'a tree * 'a t

let oob () = invalid_arg "index out of bounds"

let empty = Nil

let cons x l = match l with
| Cons (h1, t1, Cons (h2, t2, rem)) ->
  if Int.equal h1 h2 then Cons (1 + h1 + h2, Node (x, t1, t2), rem)
  else Cons (1, Leaf x, l)
| _ -> Cons (1, Leaf x, l)

let is_empty = function
| Nil -> true
| _ -> false

let rec tree_get h t i = match t with
| Leaf x ->
  if i = 0 then x else oob ()
| Node (x, t1, t2) ->
  if i = 0 then x
  else
    let h = h / 2 in
    if i <= h then tree_get h t1 (i - 1) else tree_get h t2 (i - h - 1)

let rec get l i = match l with
| Nil -> oob ()
| Cons (h, t, rem) ->
  if i < h then tree_get h t i else get rem (i - h)

let length l =
  let rec length accu = function
  | Nil -> accu
  | Cons (h, _, l) -> length (h + accu) l
  in
  length 0 l

let rec tree_map f = function
| Leaf x -> Leaf (f x)
| Node (x, t1, t2) -> Node (f x, tree_map f t1, tree_map f t2)

let rec map f = function
| Nil -> Nil
| Cons (h, t, l) -> Cons (h, tree_map f t, map f l)

let rec tree_fold_left f accu = function
| Leaf x -> f accu x
| Node (x, t1, t2) ->
  tree_fold_left f (tree_fold_left f (f accu x) t1) t2

let rec fold_left f accu = function
| Nil -> accu
| Cons (_, t, l) -> fold_left f (tree_fold_left f accu t) l

let rec tree_fold_right f t accu = match t with
| Leaf x -> f x accu
| Node (x, t1, t2) ->
  f x (tree_fold_right f t1 (tree_fold_right f t2 accu))

let rec fold_right f l accu = match l with
| Nil -> accu
| Cons (_, t, l) -> tree_fold_right f t (fold_right f l accu)

let hd = function
| Nil -> failwith "hd"
| Cons (_, Leaf x, _) -> x
| Cons (_, Node (x, _, _), _) -> x

let tl = function
| Nil -> failwith "tl"
| Cons (_, Leaf _, l) -> l
| Cons (h, Node (_, t1, t2), l) ->
  let h = h / 2 in
  Cons (h, t1, Cons (h, t2, l))

let rec skipn n l =
  if n = 0 then l
  else if is_empty l then failwith "List.skipn"
  else skipn (pred n) (tl l)
