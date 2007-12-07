(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

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


(** {6 More Specific operations} ***)

(** [default f x a] is [f y] if [x] is [Some y] and [a] otherwise. *)
let default f x a = 
  match x with
  | Some y -> f y
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
end


(** {6 Miscelaneous Primitives} *)

module Misc =
 struct
  (** [Misc.compare f x y] lifts the equality predicate [f] to 
      option types. That is, if both [x] and [y] are [None] then 
      it returns [true], if they are bothe [Some _] then
      [f] is called. Otherwise it returns [false]. *)
   let compare f x y =
     match x,y with
     | None, None -> true
     | Some z, Some w -> f z w
     | _,_ -> false
end
