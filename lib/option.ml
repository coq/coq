(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Module implementing basic combinators for OCaml option type.
   It tries follow closely the style of OCaml standard library.

   Actually, some operations have the same name as [List] ones:
   they actually are similar considering ['a option] as a type
   of lists with at most one element. *)

(** [has_some x] is [true] if [x] is of the form [Some y] and [false]
    otherwise.  *)
let has_some = function
  | None -> false
  | _ -> true

let is_empty = function
| None -> true
| Some _ -> false

(** Lifting equality onto option types. *)
let equal f x y = match x, y with
| None, None -> true
| Some x, Some y -> f x y
| _, _ -> false

let compare f x y = match x, y with
| None, None -> 0
| Some x, Some y -> f x y
| None, Some _ -> -1
| Some _, None -> 1

let hash f = function
| None -> 0
| Some x -> f x

exception IsNone

(** [get x] returns [y] where [x] is [Some y]. It raises IsNone
    if [x] equals [None]. *)
let get = function
  | Some y -> y
  | _ -> raise IsNone

(** [make x] returns [Some x]. *)
let make x = Some x

(** [init b x] returns [Some x] if [b] is [true] and [None] otherwise. *)
let init b x =
  if b then
    Some x
  else
    None


(** [flatten x] is [Some y] if [x] is [Some (Some y)] and [None] otherwise. *)
let flatten = function
  | Some (Some y) -> Some y
  | _ -> None


(** [append x y] is the first element of the concatenation of [x] and
    [y] seen as lists. *)
let append o1 o2 =
  match o1 with
  | Some _ -> o1
  | None  -> o2


(** {6 "Iterators"} ***)

(** [iter f x] executes [f y] if [x] equals [Some y]. It does nothing
    otherwise. *)
let iter f = function
  | Some y -> f y
  | _ -> ()


exception Heterogeneous

(** [iter2 f x y] executes [f z w] if [x] equals [Some z] and [y] equals
    [Some w]. It does nothing if both [x] and [y] are [None]. And raises
    [Heterogeneous] otherwise. *)
let iter2 f x y =
  match x,y with
  | Some z, Some w -> f z w
  | None,None -> ()
  | _,_ -> raise Heterogeneous

(** [map f x] is [None] if [x] is [None] and [Some (f y)] if [x] is [Some y]. *)
let map f = function
  | Some y -> Some (f y)
  | _ -> None

(** [smartmap f x] does the same as [map f x] except that it tries to share
    some memory. *)
let smartmap f = function
  | Some y as x -> let y' = f y in if y' == y then x else Some y'
  | _ -> None

(** [fold_left f a x] is [f a y] if [x] is [Some y], and [a] otherwise. *)
let fold_left f a = function
  | Some y -> f a y
  | _ -> a

(** [fold_left2 f a x y] is [f z w] if [x] is [Some z] and [y] is [Some w].
    It is [a] if both [x] and [y] are [None]. Otherwise it raises
    [Heterogeneous]. *)
let fold_left2 f a x y =
  match x,y with
  | Some x, Some y -> f a x y
  | None, None -> a
  | _ -> raise Heterogeneous

(** [fold_right f x a] is [f y a] if [x] is [Some y], and [a] otherwise. *)
let fold_right f x a =
  match x with
  | Some y -> f y a
  | _ -> a

(** [fold_map f a x] is [a, f y] if [x] is [Some y], and [a] otherwise. *)
let fold_map f a x =
  match x with
  | Some y -> let a, z = f a y in a, Some z
  | _ -> a, None

(** [cata f a x] is [a] if [x] is [None] and [f y] if [x] is [Some y]. *)
let cata f a = function
  | Some c -> f c
  | None -> a

(** {6 More Specific operations} ***)

(** [default a x] is [y] if [x] is [Some y] and [a] otherwise. *)
let default a = function
  | Some y -> y
  | _ -> a

(** [lift f x] is the same as [map f x]. *)
let lift = map

(** [lift_right f a x] is [Some (f a y)] if [x] is [Some y], and
    [None] otherwise. *)
let lift_right f a = function
  | Some y -> Some (f a y)
  | _ -> None

(** [lift_left f x a] is [Some (f y a)] if [x] is [Some y], and
    [None] otherwise. *)
let lift_left f x a =
  match x with
  | Some y -> Some (f y a)
  | _ -> None

(** [lift2 f x y] is [Some (f z w)] if [x] equals [Some z] and [y] equals
    [Some w]. It is [None] otherwise. *)
let lift2 f x y =
  match x,y with
  | Some z, Some w -> Some (f z w)
  | _,_ -> None



(** {6 Operations with Lists} *)

module List =
 struct
  (** [List.cons x l] equals [y::l] if [x] is [Some y] and [l] otherwise. *)
  let cons x l =
    match x with
    | Some y -> y::l
    | _ -> l

  (** [List.flatten l] is the list of all the [y]s such that [l] contains
      [Some y] (in the same order). *)
  let rec flatten = function
    | x::l -> cons x (flatten l)
    | [] -> []

  let rec find f = function
    |[] -> None
    |h :: t -> match f h with
	 |None -> find f t
	 |x -> x

end
