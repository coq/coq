(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Sparse lists. *)

(** {5 Constructors} *)

type +'a t = private
| Nil
| Cons of 'a * 'a t
| Default of int * 'a t
(** ['a t] is an efficient representation of ['a option list]. *)

val empty : 'a t
(** The empty list. *)

val cons : 'a -> 'a t -> 'a t
(** Isomorphic to [Some x :: l]. *)

val default : 'a t -> 'a t
(** Isomorphic to [None :: l]. *)

val cons_opt : 'a option -> 'a t -> 'a t
(** {!cons} if [Some], {!default} otherwise *)

val defaultn : int -> 'a t -> 'a t
(** Iterated variant of [default]. *)

(** {5 Destructor} *)

val view : 'a t -> ('a option * 'a t) option

val is_empty : 'a t -> bool

val is_default : 'a t -> bool

(** {5 Usual list-like operators} *)

val length : 'a t -> int

val equal : ('a -> 'b -> bool) -> 'a t -> 'b t -> bool

val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int

val to_list : 'a t -> 'a option list

val of_full_list : 'a list -> 'a t

(** {5 Iterators ignoring optional values} *)

module Skip :
sig

val iter : ('a -> unit) -> 'a t -> unit
val map : ('a -> 'b) -> 'a t -> 'b t
val fold : ('a -> 'b -> 'a) -> 'a -> 'b t -> 'a
val for_all : ('a -> bool) -> 'a t -> bool
val exists : ('a -> bool) -> 'a t -> bool

end
(** These iterators ignore the default values in the list. *)

(** {5 Smart iterators} *)

module Smart :
sig
val map : ('a -> 'a) -> 'a t -> 'a t
val fold_left_map : ('a -> 'b -> 'a * 'b) -> 'a -> 'b t -> 'a * 'b t
end
(** These iterators also ignore the default values in the list. *)
