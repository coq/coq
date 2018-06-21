(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Dynamically typed values *)

module type ValueS =
sig
  type 'a t
end

module type MapS =
sig
  type t
  type 'a key
  type 'a value
  val empty : t
  val add : 'a key -> 'a value -> t -> t
  val remove : 'a key -> t -> t
  val find : 'a key -> t -> 'a value
  val mem : 'a key -> t -> bool

  type map = { map : 'a. 'a key -> 'a value -> 'a value }
  val map : map -> t -> t

  type any = Any : 'a key * 'a value -> any
  val iter : (any -> unit) -> t -> unit
  val fold : (any -> 'r -> 'r) -> t -> 'r -> 'r
end

module type S =
sig
  type 'a tag
  type t = Dyn : 'a tag * 'a -> t
  val create : string -> 'a tag
  val eq : 'a tag -> 'b tag -> ('a, 'b) CSig.eq option
  val repr : 'a tag -> string

  val dump : unit -> (int * string) list

  type any = Any : 'a tag -> any
  val name : string -> any option

  module Map(Value : ValueS) :
    MapS with type 'a key = 'a tag and type 'a value = 'a Value.t

  module Easy : sig
    (* To create a dynamic type on the fly *)
    val make_dyn_tag : string -> ('a -> t) * (t -> 'a) * 'a tag
    val make_dyn : string -> ('a -> t) * (t -> 'a)

    (* For types declared with the [create] function above *)
    val inj : 'a -> 'a tag -> t
    val prj : t -> 'a tag -> 'a option
  end
end

module Make () : S
