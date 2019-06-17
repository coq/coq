(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Univ

type family = InSProp | InProp | InSet | InType

type t =
  | SProp
  | Prop
  | Set
  | Type of Universe.t

let sprop = SProp
let prop = Prop
let set = Set
let type1 = Type type1_univ

let univ_of_sort = function
  | Type u -> u
  | Set -> Universe.type0
  | Prop -> Universe.type0m
  | SProp -> Universe.sprop

let sort_of_univ u =
  if Universe.is_sprop u then sprop
  else if is_type0m_univ u then prop
  else if is_type0_univ u then set
  else Type u

let compare s1 s2 =
  if s1 == s2 then 0 else
    match s1, s2 with
    | SProp, SProp -> 0
    | SProp, _ -> -1
    | _, SProp -> 1
    | Prop, Prop -> 0
    | Prop, _ -> -1
    | Set, Prop -> 1
    | Set, Set -> 0
    | Set, _ -> -1
    | Type u1, Type u2 -> Universe.compare u1 u2
    | Type _, _ -> -1

let equal s1 s2 = Int.equal (compare s1 s2) 0

let super = function
  | SProp | Prop | Set -> Type (Universe.type1)
  | Type u -> Type (Universe.super u)

let is_sprop = function
  | SProp -> true
  | Prop | Set | Type _ -> false

let is_prop = function
  | Prop -> true
  | SProp | Set | Type _ -> false

let is_set = function
  | Set -> true
  | SProp | Prop | Type _ -> false

let is_small = function
  | SProp | Prop | Set -> true
  | Type _ -> false

let family = function
  | SProp -> InSProp
  | Prop -> InProp
  | Set -> InSet
  | Type _ -> InType

let family_compare a b = match a,b with
  | InSProp, InSProp -> 0
  | InSProp, _ -> -1
  | _, InSProp -> 1
  | InProp, InProp -> 0
  | InProp, _ -> -1
  | _, InProp -> 1
  | InSet, InSet -> 0
  | InSet, _ -> -1
  | _, InSet -> 1
  | InType, InType -> 0

let family_equal = (==)

let family_leq a b = family_compare a b <= 0

open Hashset.Combine

let hash = function
  | SProp -> combinesmall 1 0
  | Prop -> combinesmall 1 1
  | Set -> combinesmall 1 2
  | Type u ->
    let h = Univ.Universe.hash u in
    combinesmall 2 h

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
        | Prop, Prop | Set, Set -> true
        | (Type u1, Type u2) -> u1 == u2
        |_ -> false

      let hash = hash
    end)

let hcons = Hashcons.simple_hcons Hsorts.generate Hsorts.hcons hcons_univ

(** On binders: is this variable proof relevant *)
type relevance = Relevant | Irrelevant

let relevance_equal r1 r2 = match r1,r2 with
  | Relevant, Relevant | Irrelevant, Irrelevant -> true
  | (Relevant | Irrelevant), _ -> false

let relevance_of_sort_family = function
  | InSProp -> Irrelevant
  | _ -> Relevant

let relevance_hash = function
  | Relevant -> 0
  | Irrelevant -> 1

let relevance_of_sort = function
  | SProp -> Irrelevant
  | _ -> Relevant

let debug_print = function
  | SProp -> Pp.(str "SProp")
  | Prop -> Pp.(str "Prop")
  | Set -> Pp.(str "Set")
  | Type u -> Pp.(str "Type(" ++ Univ.Universe.pr u ++ str ")")

let pr_sort_family = function
  | InSProp -> Pp.(str "SProp")
  | InProp -> Pp.(str "Prop")
  | InSet -> Pp.(str "Set")
  | InType -> Pp.(str "Type")
