(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Module implementing basic combinators for OCaml option type.
   It tries follow closely the style of OCaml standard library.

   Actually, some operations have the same name as [List] ones:
   they actually are similar considering ['a option] as a type
   of lists with at most one element. *)

exception IsNone

(** [has_some x] is [true] if [x] is of the form [Some y] and [false]
    otherwise.  *)
val has_some : 'a option -> bool

(** Negation of [has_some] *)
val is_empty : 'a option -> bool

(** [equal f x y] lifts the equality predicate [f] to
    option types. That is, if both [x] and [y] are [None] then
    it returns [true], if they are both [Some _] then
    [f] is called. Otherwise it returns [false]. *)
val equal : ('a -> 'a -> bool) -> 'a option -> 'a option -> bool

(** Same as [equal], but with comparison. *)
val compare : ('a -> 'a -> int) -> 'a option -> 'a option -> int

(** Lift a hash to option types. *)
val hash : ('a -> int) -> 'a option -> int

(** [get x] returns [y] where [x] is [Some y].
    @raise IsNone if [x] equals [None]. *)
val get : 'a option -> 'a

(** [make x] returns [Some x]. *)
val make : 'a -> 'a option

(** [bind x f] is [f y] if [x] is [Some y] and [None] otherwise *)
val bind : 'a option -> ('a -> 'b option) -> 'b option

(** [init b x] returns [Some x] if [b] is [true] and [None] otherwise. *)
val init : bool -> 'a -> 'a option

(** [flatten x] is [Some y] if [x] is [Some (Some y)] and [None] otherwise. *)
val flatten : 'a option option -> 'a option

(** [append x y] is the first element of the concatenation of [x] and
    [y] seen as lists.  In other words, [append (Some a) y] is [Some
    a], [append None (Some b)] is [Some b], and [append None None] is
    [None]. *)
val append : 'a option -> 'a option -> 'a option


(** {6 "Iterators"} *)

(** [iter f x] executes [f y] if [x] equals [Some y]. It does nothing
    otherwise. *)
val iter : ('a -> unit) -> 'a option -> unit

exception Heterogeneous

(** [iter2 f x y] executes [f z w] if [x] equals [Some z] and [y] equals
    [Some w]. It does nothing if both [x] and [y] are [None].
    @raise Heterogeneous otherwise. *)
val iter2 : ('a -> 'b -> unit) -> 'a option -> 'b option -> unit

(** [map f x] is [None] if [x] is [None] and [Some (f y)] if [x] is [Some y]. *)
val map : ('a -> 'b) -> 'a option -> 'b option

val smartmap : ('a -> 'a) -> 'a option -> 'a option
[@@ocaml.deprecated "Same as [Smart.map]"]

(** [fold_left f a x] is [f a y] if [x] is [Some y], and [a] otherwise. *)
val fold_left : ('b -> 'a -> 'b) -> 'b -> 'a option -> 'b

(** [fold_left2 f a x y] is [f z w] if [x] is [Some z] and [y] is [Some w].
    It is [a] if both [x] and [y] are [None].
    @raise Heterogeneous otherwise. *)
val fold_left2 : ('a -> 'b -> 'c -> 'a) -> 'a -> 'b option -> 'c option -> 'a

(** [fold_right f x a] is [f y a] if [x] is [Some y], and [a] otherwise. *)
val fold_right : ('a -> 'b -> 'b) -> 'a option -> 'b -> 'b

(** [fold_left_map f a x] is [a, f y] if [x] is [Some y], and [a] otherwise. *)
val fold_left_map : ('a -> 'b -> 'a * 'c) -> 'a -> 'b option -> 'a * 'c option

(** Same as [fold_left_map] on the right *)
val fold_right_map : ('b -> 'a -> 'c * 'a) -> 'b option -> 'a -> 'c option * 'a

(** @deprecated Same as [fold_left_map] *)
val fold_map : ('a -> 'b -> 'a * 'c) -> 'a -> 'b option -> 'a * 'c option
[@@ocaml.deprecated "Same as [fold_left_map]"]

(** [cata f e x] is [e] if [x] is [None] and [f a] if [x] is [Some a] *)
val cata : ('a -> 'b) -> 'b -> 'a option -> 'b

(** {6 More Specific Operations} *)

(** [default a x] is [y] if [x] is [Some y] and [a] otherwise. *)
val default : 'a -> 'a option -> 'a

(** [lift] is the same as {!map}. *)
val lift : ('a -> 'b) -> 'a option -> 'b option

(** [lift_right f a x] is [Some (f a y)] if [x] is [Some y], and
    [None] otherwise. *)
val lift_right : ('a -> 'b -> 'c) -> 'a -> 'b option -> 'c option

(** [lift_left f x a] is [Some (f y a)] if [x] is [Some y], and
    [None] otherwise. *)
val lift_left : ('a -> 'b -> 'c) -> 'a option -> 'b -> 'c option

(** [lift2 f x y] is [Some (f z w)] if [x] equals [Some z] and [y] equals
    [Some w]. It is [None] otherwise. *)
val lift2 : ('a -> 'b -> 'c) -> 'a option -> 'b option -> 'c option

(** {6 Smart operations} *)

module Smart :
sig

  (** [Smart.map f x] does the same as [map f x] except that it tries to share
      some memory. *)
  val map : ('a -> 'a) -> 'a option -> 'a option

end

(** {6 Operations with Lists} *)

module List : sig
  (** [List.cons x l] equals [y::l] if [x] is [Some y] and [l] otherwise. *)
  val cons : 'a option -> 'a list -> 'a list

  (** [List.flatten l] is the list of all the [y]s such that [l] contains
      [Some y] (in the same order). *)
  val flatten : 'a option list -> 'a list

  (** [List.find f l] is the first [f a] different from [None],
      scrolling through elements [a] of [l] in left-to-right order;
      it is [None] if no such element exists. *)
  val find : ('a -> 'b option) -> 'a list -> 'b option

  (** [List.map f [a1;...;an]] is the list [Some [b1;...;bn]] if
      for all i, there is a [bi] such that [f ai] is [Some bi]; it is
      [None] if, for at least one i, [f ai] is [None]. *)
  val map : ('a -> 'b option) -> 'a list -> 'b list option

end
