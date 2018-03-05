(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module type HashedType =
sig
  type t
  val compare : t -> t -> int
  (** Total ordering *)
  val hash : t -> int
  (** Hashing function compatible with [compare], i.e. [compare x y = 0] implies
      [hash x = hash y]. *)
end

(** Hash maps are maps that take advantage of having a hash on keys. This is
    essentially a hash table, except that it uses purely functional maps instead
    of arrays.

    CAVEAT: order-related functions like [fold] or [iter] do not respect the
    provided order anymore! It's your duty to do something sensible to prevent
    this if you need it. In particular, [min_binding] and [max_binding] are now
    made meaningless.
*)
module Make(M : HashedType) : CMap.ExtS with type key = M.t
