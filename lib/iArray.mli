(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(** This module defines immutable arrays. Compared to usual arrays, they ensure
    that they cannot be modified dynamically. We also use some optimization
    tricks taking advantage of this fact. *)

type +'a t
(** Immutable arrays containing elements of type ['a]. *)

(** {5 Operations inherited from [Array]}

  Refer to the documentation of [CArray] for greater detail. *)

val get : 'a t -> int -> 'a
val length : 'a t -> int
val make : int -> 'a -> 'a t
val is_empty : 'a t -> bool
val init : int -> (int -> 'a) -> 'a t
val append : 'a t -> 'a t -> 'a t
val concat : 'a t list -> 'a t
val sub : 'a t -> int -> int -> 'a t
val of_list : 'a list -> 'a t
val to_list : 'a t -> 'a list
val iter : ('a -> unit) -> 'a t -> unit
val iteri : (int -> 'a -> unit) -> 'a t -> unit

val map : ('a -> 'b) -> 'a t -> 'b t
val mapi : (int -> 'a -> 'b) -> 'a t -> 'b t
val map2 : ('a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t
val map2i : (int -> 'a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t
val map3 : ('a -> 'b -> 'c -> 'd) -> 'a t -> 'b t -> 'c t -> 'd t
val smartmap : ('a -> 'a) -> 'a t -> 'a t

val fold_right : ('a -> 'b -> 'b) -> 'a t -> 'b -> 'b
val fold_right2 : ('a -> 'b -> 'c -> 'c) -> 'a t -> 'b t -> 'c -> 'c

val fold_left : ('a -> 'b -> 'a) -> 'a -> 'b t -> 'a
val fold_lefti : (int -> 'a -> 'b -> 'a) -> 'a -> 'b t -> 'a
val fold_left2 : ('a -> 'b -> 'c -> 'a) -> 'a -> 'b t -> 'c t -> 'a
val fold_left2i : (int -> 'a -> 'b -> 'c -> 'a) -> 'a -> 'b t -> 'c t -> 'a

val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int

val exists : ('a -> bool) -> 'a t -> bool

val for_all : ('a -> bool) -> 'a t -> bool
val for_all2 : ('a -> 'b -> bool) -> 'a t -> 'b t -> bool

(** {5 Purely functional version of [Array] operations} *)

(** These functions are equivalent to the eponymous versions in [Array], but
    they do not work in place. Instead, they generate a fresh copy. *)

val set : 'a t -> int -> 'a -> 'a t
val fill : 'a t -> int -> int -> 'a -> 'a t
val blit : 'a t -> int -> 'a t -> int -> int -> 'a t

(** {5 Immutable array specific operations}*)

val empty : 'a t
(** The empty array. *)

val singleton : 'a -> 'a t
(** The singleton array. *)

val diff : 'a t -> (int * 'a) list -> 'a t
(** [diff t [(i1, x1); ...; (in, xn)]] create an array identical to [t] except on
    indices [ik] that will contain [xk]. If the same index is present several
    times on the diff, which value is chosen is undefined. *)

val of_array : 'a array -> 'a t
(** Create a new immutable array with the same elements as the argument. *)

val to_array : 'a t -> 'a array
(** Create a new mutable array with the same elements as the argument. *)

(** {5 Unsafe operations} *)

module Unsafe :
sig
  val get : 'a t -> int -> 'a
  (** Get a value, does not do bound checking. *)

  val of_array : 'a array -> 'a t
  (** Cast a mutable array into an immutable one. Essentially identity. *)

  val to_array : 'a t -> 'a array
  (** Cast an immutable array into a mutable one. Essentially identity. *)
end
(** Unsafe operations. Use with caution! *)
