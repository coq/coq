(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type 'a node =
  | Nil
  | Cons of 'a * 'a t

and 'a t = 'a node Lazy.t

let empty = Lazy.from_val Nil

let cons x s = Lazy.from_val (Cons (x, s))

let peek x : _ node = Lazy.force x

let thunk f : _ t = Lazy.from_fun f

let rec force s = match peek s with
| Nil -> ()
| Cons (_, s) -> force s

let force s = force s; s

let is_empty s = match peek s with
| Nil -> true
| Cons (_, _) -> false

let rec of_list = function
| [] -> empty
| x :: l -> cons x (of_list l)

let rec to_list s = match peek s with
| Nil -> []
| Cons (x, s) -> x :: (to_list s)

let rec iter f s = match peek s with
| Nil -> ()
| Cons (x, s) -> f x; iter f s

let rec map_node f = function
| Nil -> Nil
| Cons (x, s) -> Cons (f x, map f s)

and map f s = lazy (map_node f (peek s))

let rec app_node n1 s2 = match n1 with
| Nil -> peek s2
| Cons (x, s1) -> Cons (x, app s1 s2)

and app s1 s2 = lazy (app_node (peek s1) s2)

let rec fold f accu s = match peek s with
| Nil -> accu
| Cons (x, s) -> fold f (f accu x) s

let rec map_filter_node f = function
| Nil -> Nil
| Cons (x, s) ->
  begin match f x with
  | None -> map_filter_node f (peek s)
  | Some y -> Cons (y, map_filter f s)
  end

and map_filter f s = lazy (map_filter_node f (peek s))

let rec concat_node = function
| Nil -> Nil
| Cons (s, sl) -> app_node (peek s) (concat sl)

and concat (s : 'a t t) =
  lazy (concat_node (peek s))

let rec concat_map_node f = function
| Nil -> Nil
| Cons (x,s) -> app_node (peek (f x)) (concat_map f s)

and concat_map f l = lazy (concat_map_node f (peek l))
