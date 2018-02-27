(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** An imperative implementation of partitions via Union-Find *)

(** Paths are compressed imperatively at each lookup of a
    canonical representative. Each union also modifies in-place
    the partition structure.

    Nota: for the moment we use Pervasive's comparison for
    choosing the smallest object as representative. This could
    be made more generic.
*)

module type PartitionSig = sig

  (** The type of elements in the partition *)
  type elt

  (** A set structure over elements *)
  type set

  (** The type of partitions *)
  type t

  (** Initialise an empty partition *)
  val create : unit -> t

  (** Add (in place) an element in the partition, or do nothing
      if the element is already in the partition. *)
  val add : elt -> t -> unit

  (** Find the canonical representative of an element.
      Raise [not_found] if the element isn't known yet. *)
  val find : elt -> t -> elt

  (** Merge (in place) the equivalence classes of two elements.
      This will add the elements in the partition if necessary. *)
  val union : elt -> elt -> t -> unit

  (** Merge (in place) the equivalence classes of many elements. *)
  val union_set : set -> t -> unit

  (** Listing the different components of the partition *)
  val partition : t -> set list

end

module type SetS =
sig
  type t
  type elt
  val singleton : elt -> t
  val union : t -> t -> t
  val choose : t -> elt
  val iter : (elt -> unit) -> t -> unit
end
(** Minimal interface for sets, subtype of stdlib's Set. *)

module type MapS =
sig
  type key
  type +'a t
  val empty : 'a t
  val find : key -> 'a t -> 'a
  val add : key -> 'a -> 'a t -> 'a t
  val mem : key -> 'a t -> bool
  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
end
(** Minimal interface for maps, subtype of stdlib's Map. *)

module Make :
  functor (S:SetS) ->
    functor (M:MapS with type key = S.elt) ->
      PartitionSig with type elt = S.elt and type set = S.t
