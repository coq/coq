(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val max_length : Uint63.t

type 'a t
val length  : 'a t -> Uint63.t
val length_int : 'a t -> int
val get     : 'a t -> Uint63.t -> 'a
val set     : 'a t -> Uint63.t -> 'a -> 'a t
val default : 'a t -> 'a
val make    : Uint63.t -> 'a -> 'a t
val init    : Uint63.t -> (int -> 'a) -> 'a -> 'a t
val copy    : 'a t -> 'a t

val map : ('a -> 'b) -> 'a t -> 'b t

val to_array : 'a t -> 'a array * 'a (* default *)
(* 'a should not be float (no Obj.double_tag) *)

val of_array : 'a array -> 'a (* default *) -> 'a t

val unsafe_of_obj : Obj.t -> 'a -> 'a t
(* [unsafe_of_obj] injects an untyped mutable array into a persistent one, but
   does not perform a copy. This means that if the persistent array is mutated,
   the original one will be too. The array must be a non-flat array. *)

val fold_left : ('a -> 'b -> 'a) -> 'a -> 'b t -> 'a
val fold_left2 : ('a -> 'b -> 'c -> 'a) -> 'a -> 'b t -> 'c t -> 'a
