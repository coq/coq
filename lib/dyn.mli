(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Dynamically typed values *)

module type TParam =
sig
  type 'a t
end

module type S =
sig
type 'a tag
type t = Dyn : 'a tag * 'a -> t

val create : string -> 'a tag
val eq : 'a tag -> 'b tag -> ('a, 'b) CSig.eq option
val repr : 'a tag -> string

type any = Any : 'a tag -> any

val name : string -> any option

module Map(M : TParam) :
sig
  type t
  val empty : t
  val add : 'a tag -> 'a M.t -> t -> t
  val remove : 'a tag -> t -> t
  val find : 'a tag -> t -> 'a M.t
  val mem : 'a tag -> t -> bool

  type any = Any : 'a tag * 'a M.t -> any

  type map = { map : 'a. 'a tag -> 'a M.t -> 'a M.t }
  val map : map -> t -> t

  val iter : (any -> unit) -> t -> unit
  val fold : (any -> 'r -> 'r) -> t -> 'r -> 'r

end

val dump : unit -> (int * string) list

module Easy : sig

  (* To create a dynamic type on the fly *)
  val make_dyn : string -> ('a -> t) * (t -> 'a)

  (* For types declared with the [create] function above *)
  val inj : 'a -> 'a tag -> t
  val prj : t -> 'a tag -> 'a option
end

end

module Make () : S
