(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This module defines existential variables, which are isomorphic to [int].
    Nonetheless, casting from an [int] to a variable is deemed unsafe, so that
    to keep track of such casts, one has to use the provided {!unsafe_of_int}
    function. *)

type t
(** Type of existential variables. *)

val repr : t -> int
(** Recover the underlying integer. *)

val unsafe_of_int : int -> t
(** This is not for dummies. Do not use this function if you don't know what you
    are doing. *)

val equal : t -> t -> bool
(** Equality over existential variables. *)

val compare : t -> t -> int
(** Comparison over existential variables. *)

val hash : t -> int
(** Hash over existential variables. *)

val print : t -> Pp.t
(** Printing representation *)

module Cache :
sig
  type t
  (** This is essentially an integer that indicates the length of the prefix of
      an evar instance that is not known to be the identity instance. That is,
      [Constr.Evar (evk, l, n)] is well-formed iff [l = a @ id] where
      [length a = n] and [id] is a suffix of [evk]'s identity instance.*)

  val none : t
  (** Unknown integer. *)

  val make : int -> t

  val length : t -> int option

  module List :
  sig
    val map : t -> ('a -> 'a) -> 'a list -> t * 'a list
    val map_prefix : t -> ('a -> 'a) -> 'a list -> 'a list
    val iter_prefix : t -> ('a -> unit) -> 'a list -> unit
    val prefix : t -> 'a list -> 'a list
  end
  (** This module offers functions similar to the generic list module, except
      that they only consider the non-trivial prefix of the argument. *)

end

module Set : Set.S with type elt = t
module Map : CMap.ExtS with type key = t and module Set := Set
