(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Univ

type contents = Pos | Null

type family = InProp | InSet | InType

type t =
  | Prop of contents                      (* proposition types *)
  | Type of Universe.t

let prop = Prop Null
let set = Prop Pos
let type1 = Type type1_univ

let univ_of_sort = function
  | Type u -> u
  | Prop Pos -> Universe.type0
  | Prop Null -> Universe.type0m

let sort_of_univ u =
  if is_type0m_univ u then prop
  else if is_type0_univ u then set
  else Type u

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
  | Type u when Universe.equal Universe.type0m u -> true
  | _ -> false

let is_set = function
  | Prop Pos -> true
  | Type u when Universe.equal Universe.type0 u -> true
  | _ -> false

let is_small = function
  | Prop _ -> true
  | Type u -> is_small_univ u

let family = function
  | Prop Null -> InProp
  | Prop Pos -> InSet
  | Type u when is_type0m_univ u -> InProp
  | Type u when is_type0_univ u -> InSet
  | Type _ -> InType

let family_equal = (==)

open Hashset.Combine

let hash = function
| Prop p ->
  let h = match p with
  | Pos -> 0
  | Null -> 1
  in
  combinesmall 1 h
| Type u ->
 let h = Univ.Universe.hash u in
  combinesmall 2 h

module List = struct
  let mem = List.memq
  let intersect l l' = CList.intersect family_equal l l'
end

module Hsorts =
  Hashcons.Make(
    struct
      type _t = t
      type t = _t
      type u = Universe.t -> Universe.t

      let hashcons huniv = function
        | Type u as c -> 
	  let u' = huniv u in 
	    if u' == u then c else Type u'
        | s -> s
      let eq s1 s2 = match (s1,s2) with
        | (Prop c1, Prop c2) -> c1 == c2
        | (Type u1, Type u2) -> u1 == u2
        |_ -> false

      let hash = hash
    end)

let hcons = Hashcons.simple_hcons Hsorts.generate Hsorts.hcons hcons_univ
