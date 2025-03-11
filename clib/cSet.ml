(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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

module type ExtS =
sig
  include CSig.SetS
  module List : sig
    val union : t list -> t
  end
end

module SetExt (M : Set.OrderedType) :
sig
  type set = Set.Make(M).t
  module List : sig
    val union : set list -> set
  end
end =
struct
  module S = Set.Make(M)
  type set = S.t

  module List = struct
    let union = List.fold_left S.union S.empty
  end
end

module Make(M : Set.OrderedType) =
struct
  include Set.Make(M)
  include SetExt(M)
end

module type HashedType =
sig
  type t
  val hash : t -> int
end

module Hashcons(M : OrderedType)(H : Hashcons.HashedType with type t = M.t)  =
struct
  module Set = Make(M)

  type set = Set.t
  type _set =
  | SEmpty
  | SNode of set * M.t * set * int

  let set_prj : set -> _set = Obj.magic
  let set_inj : _set -> set = Obj.magic

  (* equivalent sets may have different structure, so we don't hash and compare by
     the actual structure but only by the list of elements *)
  let rec spine s accu = match set_prj s with
  | SEmpty -> accu
  | SNode (l, v, r, _) -> spine l ((v, r) :: accu)

  let rec umap hacc s = match set_prj s with
  | SEmpty -> hacc, set_inj SEmpty
  | SNode (l, v, r, h) ->
    let hacc, l' = umap hacc l in
    let hv, v' = H.hcons v in
    let hacc = Hashset.Combine.combine hacc hv in
    let hacc, r' = umap hacc r in
    hacc, set_inj (SNode (l', v', r', h))

  let rec eqeq s1 s2 = match s1, s2 with
  | [], [] -> true
  | (v1, r1) :: s1, (v2, r2) :: s2 ->
      v1 == v2 && eqeq (spine r1 s1) (spine r2 s2)
  | _ -> false

  module Hashed =
  struct
    type t = set
    let eq s1 s2 = s1 == s2 || eqeq (spine s1 []) (spine s2 [])
    let hashcons v = umap 0 v
  end

  include Hashcons.Make(Hashed)

end
