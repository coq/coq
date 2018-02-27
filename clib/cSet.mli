(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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

module type HashedType =
sig
  type t
  val hash : t -> int
end

module Hashcons (M : OrderedType) (H : HashedType with type t = M.t) : Hashcons.S with
  type t = Set.Make(M).t
  and type u = M.t -> M.t
(** Create hash-consing for sets. The hashing function provided must be
    compatible with the comparison function. *)
