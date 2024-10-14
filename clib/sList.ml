(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type 'a t =
| Nil
| Cons of 'a * 'a t
| Default of int * 'a t
(* Invariant: no two consecutive [Default] nodes, the integer is always > 0 *)

let empty = Nil
let cons x l = Cons (x, l)
let defaultn n l =
  if Int.equal n 0 then l
  else match l with
  | Nil | Cons _ -> Default (n, l)
  | Default (m, l) -> Default (n + m, l)

let default l = match l with
| Nil | Cons _ -> Default (1, l)
| Default (m, l) -> Default (m + 1, l)

let cons_opt o l = match o with
| None -> default l
| Some x -> cons x l

let is_empty = function
| Nil -> true
| Cons _ | Default _ -> false

let is_default = function
| Nil -> true
| Default (_, Nil) -> true
| Cons _ | Default _ -> false

let view = function
| Nil -> None
| Cons (x, l) -> Some (Some x, l)
| Default (1, l) -> Some (None, l)
| Default (n, l) -> Some (None, Default (n - 1, l))

let rec to_list l = match l with
| Nil -> []
| Cons (x, l) -> Some x :: to_list l
| Default (n, l) ->
  let l = to_list l in
  let rec iterate n l = if n <= 0 then l else iterate (n - 1) (None :: l) in
  iterate n l

let of_full_list l = List.fold_right cons l empty

let equal eq l1 l2 =
  let eq o1 o2 = match o1, o2 with
  | None, None -> true
  | Some x1, Some x2 -> eq x1 x2
  | Some _, None | None, Some _ -> false
  in
  CList.for_all2eq eq (to_list l1) (to_list l2)

let compare cmp l1 l2 = CList.compare (Option.compare cmp) (to_list l1) (to_list l2)

let length l =
  let rec length n = function
  | Nil -> n
  | Cons (_, l) -> length (n + 1) l
  | Default (k, l) -> length (k + n) l
  in
  length 0 l

module Skip =
struct

let rec iter f = function
| Nil -> ()
| Cons (x, l) ->
  let () = f x in
  iter f l
| Default (_, l) -> iter f l

let rec map f = function
| Nil -> Nil
| Cons (x, l) -> Cons (f x, map f l)
| Default (n, l) -> Default (n, map f l)

let rec fold f accu = function
| Nil -> accu
| Cons (x, l) -> fold f (f accu x) l
| Default (_, l) -> fold f accu l

let rec for_all f l = match l with
| Nil -> true
| Cons (x, l) -> f x && for_all f l
| Default (_, l) -> for_all f l

let rec exists f l = match l with
| Nil -> false
| Cons (x, l) -> f x || exists f l
| Default (_, l) -> exists f l

end

module Smart =
struct

let rec map f l = match l with
| Nil -> empty
| Cons (x, r) ->
  let x' = f x in
  let r' = map f r in
  if x' == x && r' == r then l else cons x' r'
| Default (n, r) ->
  let r' = map f r in
  if r' == r then l else Default (n, r')

let rec fold_left_map f accu l0 = match l0 with
| Nil -> accu, empty
| Cons (x, l) ->
  let accu, x' = f accu x in
  let accu, l' = fold_left_map f accu l in
  let r = if x' == x && l' == l then l0 else Cons (x', l') in
  accu, r
| Default (n, l) ->
  let accu, l' = fold_left_map f accu l in
  let r = if l' == l then l0 else Default (n, l') in
  accu, r

end
