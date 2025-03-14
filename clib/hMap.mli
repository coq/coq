(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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
    this if you need it.
*)
module Make(M : HashedType) : CMap.UExtS with type key = M.t

module HashconsSet (M : HashedType) (_ : Hashcons.HashedType with type t = CSet.Make(M).t)
  : Hashcons.S with type t = Make(M).Set.t

module Hashcons (M : HashedType) (V:sig type t end)
    (_ : Hashcons.HashedType with type t = V.t CMap.Make(M).t)
    : Hashcons.S with type t = V.t Make(M).t
