(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** {5 Extended version of OCaml's maps} *)

module type OrderedType =
sig
  type t
  val compare : t -> t -> int
end

module type MonadS =
sig
  type +'a t
  val return : 'a -> 'a t
  val (>>=) : 'a t -> ('a -> 'b t) -> 'b t
end

module type S = Map.S

module type ExtS =
sig
  include CSig.MapS
  (** The underlying Map library *)

  module Set : CSig.SetS with type elt = key
  (** Sets used by the domain function *)

  val get : key -> 'a t -> 'a
  (** Same as {!find} but fails an assertion instead of raising [Not_found] *)

  val set : key -> 'a -> 'a t -> 'a t
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

  val height : 'a t -> int
  (** An indication of the logarithmic size of a map *)

  val filter_range : (key -> int) -> 'a t -> 'a t
  (** [find_range in_range m] Given a comparison function [in_range x],
      that tests if [x] is below, above, or inside a given range
      [filter_range] returns the submap of [m] whose keys are in
      range. Note that [in_range] has to define a continouous range. *)

  module Smart :
  sig
    val map : ('a -> 'a) -> 'a t -> 'a t
    (** As [map] but tries to preserve sharing. *)

    val mapi : (key -> 'a -> 'a) -> 'a t -> 'a t
    (** As [mapi] but tries to preserve sharing. *)
  end

  module Monad(M : MonadS) :
  sig
    val fold : (key -> 'a -> 'b -> 'b M.t) -> 'a t -> 'b -> 'b M.t
    val fold_left : (key -> 'a -> 'b -> 'b M.t) -> 'a t -> 'b -> 'b M.t
    val fold_right : (key -> 'a -> 'b -> 'b M.t) -> 'a t -> 'b -> 'b M.t
  end
  (** Fold operators parameterized by any monad. *)

end

module Make(M : Map.OrderedType) : ExtS with
  type key = M.t
  and type 'a t = 'a Map.Make(M).t
  and module Set := Set.Make(M)
