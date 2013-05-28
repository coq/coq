(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

type 'a t =
| Nil
| Cons of 'a * 'a t
| Lazy of 'a t Lazy.t

let empty = Nil

let cons x s = Cons (x, s)

let thunk s = Lazy s

let rec force = function
| Nil -> ()
| Cons (_, s) -> force s
| Lazy t -> force (Lazy.force t)

let force s = force s; s

let rec is_empty = function
| Nil -> true
| Cons (_, _) -> false
| Lazy t -> is_empty (Lazy.force t)

let rec peek = function
| Nil -> None
| Cons (x, s) -> Some (x, s)
| Lazy t -> peek (Lazy.force t)

let rec of_list = function
| [] -> Nil
| x :: l -> Cons (x, of_list l)

let rec to_list = function
| Nil -> []
| Cons (x, s) -> x :: (to_list s)
| Lazy t -> to_list (Lazy.force t)

let rec iter f = function
| Nil -> ()
| Cons (x, s) -> f x; iter f s
| Lazy t -> iter f (Lazy.force t)

let rec map f = function
| Nil -> Nil
| Cons (x, s) -> Cons (f x, map f s)
| Lazy t -> Lazy (lazy (map f (Lazy.force t)))

let rec app s1 s2 = match s1 with
| Nil -> s2
| Cons (x, s1) -> Cons (x, app s1 s2)
| Lazy t ->
  let t = lazy (app (Lazy.force t) s2) in
  Lazy t

let rec fold f accu = function
| Nil -> accu
| Cons (x, s) -> fold f (f accu x) s
| Lazy t -> fold f accu (Lazy.force t)

let rec map_filter f = function
| Nil -> Nil
| Cons (x, s) ->
  begin match f x with
  | None -> map_filter f s
  | Some y -> Cons (y, map_filter f s)
  end
| Lazy t ->
  let t = lazy (map_filter f (Lazy.force t)) in
  Lazy t

let rec concat = function
| Nil -> Nil
| Cons (s, sl) -> app s (concat sl)
| Lazy t ->
  let t = lazy (concat (Lazy.force t)) in
  Lazy t

let lempty = Lazy (lazy Nil)
