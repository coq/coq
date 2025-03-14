(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module type OrderedType =
sig
  type t
  val compare : t -> t -> int
end

module type S = Set.S

module type ExtS =
sig
  include CSig.SetS
  (** The underlying Set library *)

  module List : sig
    val union : t list -> t
    (** Union of sets from a list *)
  end
end

module Make(M : Map.OrderedType) : ExtS
  with type elt = M.t
  and type t = Set.Make(M).t

module Hashcons (M : OrderedType) (_ : Hashcons.HashedType with type t = M.t) : Hashcons.S with
  type t = Set.Make(M).t
(** Create hash-consing for sets. The hashing function provided must be
    compatible with the comparison function. *)
