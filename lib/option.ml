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
