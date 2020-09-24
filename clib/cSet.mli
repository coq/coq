(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
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

module Make(M : OrderedType) : S
  with type elt = M.t
  and type t = Set.Make(M).t

module Hashcons (M : OrderedType) : Hashcons.S with
  type t = Set.Make(M).t
  and type u = M.t Hashcons.hfun
(** Create hash-consing for sets. The hashing function provided must be
    compatible with the comparison function. *)
