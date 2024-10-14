(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Non-empty lists *)
type +'a t

val head : 'a t -> 'a

val tail : 'a t -> 'a t option

val singleton : 'a -> 'a t

val iter : ('a -> unit) -> 'a t -> unit

val map : ('a -> 'b) -> 'a t -> 'b t

val map2 : ('a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t

val map_head : ('a -> 'a) -> 'a t -> 'a t

val push : 'a -> 'a t option -> 'a t

val to_list : 'a t -> 'a list

(** May raise Invalid_argument *)
val of_list : 'a list -> 'a t

val repr : 'a t -> 'a * 'a list

val of_repr : 'a * 'a list -> 'a t
