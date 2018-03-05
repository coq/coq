(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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

module Set : Set.S with type elt = t
module Map : CMap.ExtS with type key = t and module Set := Set
