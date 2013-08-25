(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

module type OrderedType =
sig
  type t
  val compare : t -> t -> int
end

module type S = Map.S

module type ExtS =
sig
  include Map.S
  module Set : Set.S with type elt = key
  val domain : 'a t -> Set.t
  val bind : (key -> 'a) -> Set.t -> 'a t
end

module MapExt (M : Map.OrderedType) :
sig
  val domain : 'a Map.Make(M).t -> Set.Make(M).t
  val bind : (M.t -> 'a) -> Set.Make(M).t -> 'a Map.Make(M).t
end =
struct
  (** This unsafe module is a way to access to the actual implementations of
      OCaml sets and maps without reimplementing them ourselves. It is quite
      dubious that these implementations will ever be changed... Nonetheless,
      if this happens, we can still implement a less clever version of [domain].
  *)

  type 'a map = 'a Map.Make(M).t
  type set = Set.Make(M).t

  type 'a _map =
  | MEmpty
  | MNode of 'a map * M.t * 'a * 'a map * int

  type _set =
  | SEmpty
  | SNode of set * M.t * set * int

  let rec domain (s : 'a map) : set = match Obj.magic s with
  | MEmpty -> Obj.magic SEmpty
  | MNode (l, k, _, r, h) ->
    Obj.magic (SNode (domain l, k, domain r, h))
  (** This function is essentially identity, but OCaml current stdlib does not
      take advantage of the similarity of the two structures, so we introduce
      this unsafe loophole. *)

  let rec bind f (s : set) : 'a map = match Obj.magic s with
  | SEmpty -> Obj.magic MEmpty
  | SNode (l, k, r, h) ->
    Obj.magic (MNode (bind f l, k, f k, bind f r, h))
  (** Dual operation of [domain]. *)

end

module Make(M : Map.OrderedType) =
struct
  include Map.Make(M)
  include MapExt(M)
end
