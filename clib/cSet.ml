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

module Make(M : OrderedType)= Set.Make(M)

module type HashedType =
sig
  type t
  val hash : t -> int
end

module Hashcons(M : OrderedType)(H : HashedType with type t = M.t)  =
struct
  module Set = Make(M)

  type set = Set.t
  type _set =
  | SEmpty
  | SNode of set * M.t * set * int

  let set_prj : set -> _set = Obj.magic
  let set_inj : _set -> set = Obj.magic

  let rec spine s accu = match set_prj s with
  | SEmpty -> accu
  | SNode (l, v, r, _) -> spine l ((v, r) :: accu)

  let rec umap f s = match set_prj s with
  | SEmpty -> set_inj SEmpty
  | SNode (l, v, r, h) ->
    let l' = umap f l in
    let r' = umap f r in
    let v' = f v in
    set_inj (SNode (l', v', r', h))

  let rec eqeq s1 s2 = match s1, s2 with
  | [], [] -> true
  | (v1, r1) :: s1, (v2, r2) :: s2 ->
      v1 == v2 && eqeq (spine r1 s1) (spine r2 s2)
  | _ -> false

  module Hashed =
  struct
    open Hashset.Combine
    type t = set
    type u = M.t -> M.t
    let eq s1 s2 = s1 == s2 || eqeq (spine s1 []) (spine s2 [])
    let hash s = Set.fold (fun v accu -> combine (H.hash v) accu) s 0
    let hashcons = umap
  end

  include Hashcons.Make(Hashed)

end
