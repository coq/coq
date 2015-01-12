(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** {5 Extended version of OCaml's maps} *)

module type OrderedType =
sig
  type t
  val compare : t -> t -> int
end

module type S = Map.S

module type ExtS =
sig
  include Map.S
  (** The underlying Map library *)

  module Set : CSig.SetS with type elt = key
  (** Sets used by the domain function *)

  val update : key -> 'a -> 'a t -> 'a t
  (** Same as [add], but expects the key to be present, and thus faster.
      @raise Not_found when the key is unbound in the map. *)

  val modify : key -> (key -> 'a -> 'a) -> 'a t -> 'a t
  (** Apply the given function to the binding of the given key.
      @raise Not_found when the key is unbound in the map. *)

  val domain : 'a t -> Set.t
  (** Recover the set of keys defined in the map. *)

  val bind : (key -> 'a) -> Set.t -> 'a t
  (** [bind f s] transform the set [x1; ...; xn] into [x1 := f x1; ...;
      xn := f xn]. *)

  val fold_left : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  (** Alias for {!fold}, to easily track where we depend on fold order. *)

  val fold_right : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  (** Folding keys in decreasing order. *)

  val smartmap : ('a -> 'a) -> 'a t -> 'a t
  (** As [map] but tries to preserve sharing. *)

  val smartmapi : (key -> 'a -> 'a) -> 'a t -> 'a t
  (** As [mapi] but tries to preserve sharing. *)

  module Unsafe :
  sig
    val map : (key -> 'a -> key * 'b) -> 'a t -> 'b t
    (** As the usual [map], but also allows modifying the key of a binding.
        It is required that the mapping function [f] preserves key equality,
        i.e.: for all (k : key) (x : 'a), compare (fst (f k x)) k = 0. *)
  end

end

module Make(M : Map.OrderedType) : ExtS with
  type key = M.t
  and type 'a t = 'a Map.Make(M).t
  and module Set := Set.Make(M)
