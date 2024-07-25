(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Like a Parray, but the old pointers are invalidated instead of updated *)
type 'a t
val make : int -> 'a t

val get : int -> 'a t -> 'a option

val is_filled : int -> 'a t -> bool

val add : int -> 'a -> 'a t -> 'a t

val fill_remaining : 'a -> 'a t -> 'a t

val to_array : 'a t -> 'a array

val to_array_opt : 'a t -> 'a array option
(** The NoDupArray is still invalidated if the result is None *)

module Internal : sig
  val unsafe_to_array : 'a t -> 'a option array
end
