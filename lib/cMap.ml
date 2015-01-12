(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
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
  module Set : CSig.SetS with type elt = key
  val update : key -> 'a -> 'a t -> 'a t
  val modify : key -> (key -> 'a -> 'a) -> 'a t -> 'a t
  val domain : 'a t -> Set.t
  val bind : (key -> 'a) -> Set.t -> 'a t
  val fold_left : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  val fold_right : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  val smartmap : ('a -> 'a) -> 'a t -> 'a t
  val smartmapi : (key -> 'a -> 'a) -> 'a t -> 'a t
  module Unsafe :
  sig
    val map : (key -> 'a -> key * 'b) -> 'a t -> 'b t
  end
end

module MapExt (M : Map.OrderedType) :
sig
  type 'a map = 'a Map.Make(M).t
  val update : M.t -> 'a -> 'a map -> 'a map
  val modify : M.t -> (M.t -> 'a -> 'a) -> 'a map -> 'a map
  val domain : 'a map -> Set.Make(M).t
  val bind : (M.t -> 'a) -> Set.Make(M).t -> 'a map
  val fold_left : (M.t -> 'a -> 'b -> 'b) -> 'a map -> 'b -> 'b
  val fold_right : (M.t -> 'a -> 'b -> 'b) -> 'a map -> 'b -> 'b
  val smartmap : ('a -> 'a) -> 'a map -> 'a map
  val smartmapi : (M.t -> 'a -> 'a) -> 'a map -> 'a map
  module Unsafe :
  sig
    val map : (M.t -> 'a -> M.t * 'b) -> 'a map -> 'b map
  end
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
      let l' = update k v l in
      if l == l' then s
      else map_inj (MNode (l', k', v', r, h))
    else if c = 0 then
      if v' == v then s
      else map_inj (MNode (l, k', v, r, h))
    else
      let r' = update k v r in
      if r == r' then s
      else map_inj (MNode (l, k', v', r', h))

  let rec modify k f (s : 'a map) : 'a map = match map_prj s with
  | MEmpty -> raise Not_found
  | MNode (l, k', v, r, h) ->
    let c = M.compare k k' in
    if c < 0 then
      let l' = modify k f l in
      if l == l' then s
      else map_inj (MNode (l', k', v, r, h))
    else if c = 0 then
      let v' = f k' v in
      if v' == v then s
      else map_inj (MNode (l, k', v', r, h))
    else
      let r' = modify k f r in
      if r == r' then s
      else map_inj (MNode (l, k', v, r', h))

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

  let rec fold_left f (s : 'a map) accu = match map_prj s with
  | MEmpty -> accu
  | MNode (l, k, v, r, h) ->
    let accu = f k v (fold_left f l accu) in
    fold_left f r accu

  let rec fold_right f (s : 'a map) accu = match map_prj s with
  | MEmpty -> accu
  | MNode (l, k, v, r, h) ->
    let accu = f k v (fold_right f r accu) in
    fold_right f l accu

  let rec smartmap f (s : 'a map) = match map_prj s with
  | MEmpty -> map_inj MEmpty
  | MNode (l, k, v, r, h) ->
    let l' = smartmap f l in
    let r' = smartmap f r in
    let v' = f v in
    if l == l' && r == r' && v == v' then s
    else map_inj (MNode (l', k, v', r', h))

  let rec smartmapi f (s : 'a map) = match map_prj s with
  | MEmpty -> map_inj MEmpty
  | MNode (l, k, v, r, h) ->
    let l' = smartmapi f l in
    let r' = smartmapi f r in
    let v' = f k v in
    if l == l' && r == r' && v == v' then s
    else map_inj (MNode (l', k, v', r', h))

  module Unsafe =
  struct

    let rec map f (s : 'a map) : 'b map = match map_prj s with
    | MEmpty -> map_inj MEmpty
    | MNode (l, k, v, r, h) ->
      let (k, v) = f k v in
      map_inj (MNode (map f l, k, v, map f r, h))

  end

end

module Make(M : Map.OrderedType) =
struct
  include Map.Make(M)
  include MapExt(M)
end
