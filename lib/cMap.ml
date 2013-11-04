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
  val update : key -> 'a -> 'a t -> 'a t
  val modify : key -> (key -> 'a -> 'a) -> 'a t -> 'a t
  val domain : 'a t -> Set.t
  val bind : (key -> 'a) -> Set.t -> 'a t
end

module MapExt (M : Map.OrderedType) :
sig
  type 'a map = 'a Map.Make(M).t
  val update : M.t -> 'a -> 'a map -> 'a map
  val modify : M.t -> (M.t -> 'a -> 'a) -> 'a map -> 'a map
  val domain : 'a map -> Set.Make(M).t
  val bind : (M.t -> 'a) -> Set.Make(M).t -> 'a map
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

  let map_prj : 'a map -> 'a _map = Obj.magic
  let map_inj : 'a _map -> 'a map = Obj.magic
  let set_prj : set -> _set = Obj.magic
  let set_inj : _set -> set = Obj.magic

  let rec update k v (s : 'a map) : 'a map = match map_prj s with
  | MEmpty -> raise Not_found
  | MNode (l, k', v', r, h) ->
    let c = M.compare k k' in
    if c < 0 then
      map_inj (MNode (update k v l, k', v', r, h))
    else if c = 0 then
      map_inj (MNode (l, k', v, r, h))
    else
      map_inj (MNode (l, k', v', update k v r, h))

  let rec modify k f (s : 'a map) : 'a map = match map_prj s with
  | MEmpty -> raise Not_found
  | MNode (l, k', v, r, h) ->
    let c = M.compare k k' in
    if c < 0 then
      map_inj (MNode (modify k f l, k', v, r, h))
    else if c = 0 then
      map_inj (MNode (l, k', f k' v, r, h))
    else
      map_inj (MNode (l, k', v, modify k f r, h))

  let rec domain (s : 'a map) : set = match map_prj s with
  | MEmpty -> set_inj SEmpty
  | MNode (l, k, _, r, h) ->
    set_inj (SNode (domain l, k, domain r, h))
  (** This function is essentially identity, but OCaml current stdlib does not
      take advantage of the similarity of the two structures, so we introduce
      this unsafe loophole. *)

  let rec bind f (s : set) : 'a map = match set_prj s with
  | SEmpty -> map_inj MEmpty
  | SNode (l, k, r, h) ->
    map_inj (MNode (bind f l, k, f k, bind f r, h))
  (** Dual operation of [domain]. *)

end

module Make(M : Map.OrderedType) =
struct
  include Map.Make(M)
  include MapExt(M)
end
