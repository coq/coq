(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Univ

type contents = Pos | Null

type family = InProp | InSet | InType

type t =
  | Prop of contents                      (* proposition types *)
  | Type of universe

let prop = Prop Null
let set = Prop Pos
let type1 = Type type1_univ

let compare s1 s2 =
  if s1 == s2 then 0 else
  match s1, s2 with
  | Prop c1, Prop c2 ->
    begin match c1, c2 with
    | Pos, Pos | Null, Null -> 0
    | Pos, Null -> -1
    | Null, Pos -> 1
    end
  | Type u1, Type u2 -> Universe.compare u1 u2
  | Prop _, Type _ -> -1
  | Type _, Prop _ -> 1

let equal s1 s2 = Int.equal (compare s1 s2) 0

let is_prop = function
| Prop Null -> true
| _ -> false

let family = function
  | Prop Null -> InProp
  | Prop Pos -> InSet
  | Type _ -> InType

let family_equal = (==)

module Hsorts =
  Hashcons.Make(
    struct
      type _t = t
      type t = _t
      type u = universe -> universe
      let hashcons huniv = function
        | Type u -> Type (huniv u)
        | s -> s
      let equal s1 s2 = match (s1,s2) with
        | (Prop c1, Prop c2) -> c1 == c2
        | (Type u1, Type u2) -> u1 == u2
        |_ -> false
      let hash = Hashtbl.hash
    end)

let hcons = Hashcons.simple_hcons Hsorts.generate hcons_univ
