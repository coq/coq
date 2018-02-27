(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** A native integer module with usual utility functions. *)

type t = int

external equal : t -> t -> bool = "%eq"

external compare : t -> t -> int = "caml_int_compare"

val hash : t -> int

module Set : Set.S with type elt = t
module Map : CMap.ExtS with type key = t and module Set := Set

module List : sig
  val mem : int -> int list -> bool
  val assoc : int -> (int * 'a) list -> 'a
  val mem_assoc : int -> (int * 'a) list -> bool
  val remove_assoc : int -> (int * 'a) list -> (int * 'a) list
end

module PArray :
sig
  type 'a t
  (** Persistent, auto-resizable arrays. The [get] and [set] functions never
      fail whenever the index is between [0] and [Sys.max_array_length - 1]. *)
  val empty : int -> 'a t
  (** The empty array, with a given starting size. *)
  val get : 'a t -> int -> 'a option
  (** Get a value at the given index. Returns [None] if undefined. *)
  val set : 'a t -> int -> 'a option -> 'a t
  (** Set/unset a value at the given index. *)
end

module PMap :
sig
  type key = int
  type 'a t
  val empty : 'a t
  val is_empty : 'a t -> bool
  val mem : key -> 'a t -> bool
  val add : key -> 'a -> 'a t -> 'a t
  val singleton : key -> 'a -> 'a t
  val remove : key -> 'a t -> 'a t
(*   val merge : (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t *)
(*   val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int *)
(*   val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool *)
  val iter : (key -> 'a -> unit) -> 'a t -> unit
  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  val for_all : (key -> 'a -> bool) -> 'a t -> bool
  val exists : (key -> 'a -> bool) -> 'a t -> bool
(*   val filter : (key -> 'a -> bool) -> 'a t -> 'a t *)
(*   val partition : (key -> 'a -> bool) -> 'a t -> 'a t * 'a t *)
(*   val cardinal : 'a t -> int *)
(*   val bindings : 'a t -> (key * 'a) list *)
(*   val min_binding : 'a t -> key * 'a *)
(*   val max_binding : 'a t -> key * 'a *)
(*   val choose : 'a t -> key * 'a *)
(*   val split : key -> 'a t -> 'a t * 'a option * 'a t *)
  val find : key -> 'a t -> 'a
(*   val map : ('a -> 'b) -> 'a t -> 'b t *)
(*   val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t *)
  val domain : 'a t -> Set.t
  val cast : 'a t -> 'a Map.t
end
(** This is a (partial) implementation of a [Map] interface on integers, except
    that it internally uses persistent arrays. This ensures O(1) accesses in
    non-backtracking cases. It is thus better suited for zero-starting,
    contiguous keys, or otherwise a lot of space will be empty. To keep track of
    the present keys, a binary tree is also used, so that adding a key is
    still logarithmic. It is therefore essential that most of the operations
    are accesses and not add/removes. *)
