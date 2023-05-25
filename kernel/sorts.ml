(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Univ

type family = InSProp | InProp | InSet | InType | InQSort

let all_families = [InSProp; InProp; InSet; InType; InQSort]

module QVar = struct
  type t =
    | Unif of string * int

  let make s i = Unif (s, i)

  let repr (Unif (s,i)) = s, i

  let equal (Unif (s1,i1)) (Unif (s2,i2)) =
    Int.equal i1 i2 && CString.equal s1 s2

  let compare (Unif (s1,i1)) (Unif (s2,i2)) =
    let c = Int.compare i1 i2 in
    if c <> 0 then c
    else CString.compare s1 s2

  let to_string (Unif (s,i)) =
    let i = "α"^string_of_int i in
    if CString.is_empty s then i
    else s^ "." ^ i

  let hash (Unif (s,i)) = Hashset.Combine.combine (CString.hash s) i

  let pr x = Pp.str (to_string x)
end

type t =
  | SProp
  | Prop
  | Set
  | Type of Universe.t
  | QSort of QVar.t * Universe.t

let sprop = SProp
let prop = Prop
let set = Set
let type1 = Type Universe.type1
let qsort q u = QSort (q, u)

let sort_of_univ u =
  if Universe.is_type0 u then set else Type u

let compare s1 s2 =
  if s1 == s2 then 0 else
    match s1, s2 with
    | SProp, SProp -> 0
    | SProp, (Prop | Set | Type _ | QSort _) -> -1
    | (Prop | Set | Type _ | QSort _), SProp -> 1
    | Prop, Prop -> 0
    | Prop, (Set | Type _ | QSort _) -> -1
    | Set, Prop -> 1
    | Set, Set -> 0
    | Set, (Type _ | QSort _) -> -1
    | Type _, QSort _ -> -1
    | Type u1, Type u2 -> Universe.compare u1 u2
    | Type _, (Prop | Set) -> 1
    | QSort (q1, u1), QSort (q2, u2) ->
      let c = QVar.compare q1 q2 in
      if Int.equal c 0 then Universe.compare u1 u2 else c
    | QSort _, (Prop | Set | Type _) -> 1

let equal s1 s2 = Int.equal (compare s1 s2) 0

let super = function
  | SProp | Prop | Set -> Type (Universe.type1)
  | Type u | QSort (_, u) -> Type (Universe.super u)

let is_sprop = function
  | SProp -> true
  | Prop | Set | Type _ | QSort _ -> false

let is_prop = function
  | Prop -> true
  | SProp | Set | Type _ | QSort _-> false

let is_set = function
  | Set -> true
  | SProp | Prop | Type _ | QSort _ -> false

let is_small = function
  | SProp | Prop | Set -> true
  | Type _ | QSort _ -> false

let levels s = match s with
| SProp | Prop -> Level.Set.empty
| Set -> Level.Set.singleton Level.set
| Type u | QSort (_, u) -> Universe.levels u

let family = function
  | SProp -> InSProp
  | Prop -> InProp
  | Set -> InSet
  | Type _ -> InType
  | QSort _ -> InQSort

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
  | InType, _ -> -1
  | _, InType -> 1
  | InQSort, InQSort -> 0

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
  | QSort (q, u) ->
    let h = Univ.Universe.hash u in
    let h' = QVar.hash q in
    combinesmall 3 (combine h h')

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
        | QSort (q, u) as c ->
          let u' = huniv u in
          if u' == u then c else QSort (q, u)
        | SProp | Prop | Set as s -> s
      let eq s1 s2 = match (s1,s2) with
        | SProp, SProp | Prop, Prop | Set, Set -> true
        | (Type u1, Type u2) -> u1 == u2
        | QSort (q1, u1), QSort (q2, u2) -> q1 == q2 && u1 == u2
        | (SProp | Prop | Set | Type _ | QSort _), _ -> false

      let hash = hash
    end)

let hcons = Hashcons.simple_hcons Hsorts.generate Hsorts.hcons hcons_univ

(** On binders: is this variable proof relevant *)
type relevance = Relevant | Irrelevant | RelevanceVar of QVar.t

let relevance_equal r1 r2 = match r1,r2 with
  | Relevant, Relevant | Irrelevant, Irrelevant -> true
  | RelevanceVar q1, RelevanceVar q2 -> QVar.equal q1 q2
  | (Relevant | Irrelevant | RelevanceVar _), _ -> false

let relevance_of_sort_family = function
  | InSProp -> Irrelevant
  | _ -> Relevant

let relevance_hash = function
  | Relevant -> 0
  | Irrelevant -> 1
  | RelevanceVar q -> Hashset.Combine.combinesmall 2 (QVar.hash q)

let relevance_of_sort = function
  | SProp -> Irrelevant
  | Prop | Set | Type _ -> Relevant
  | QSort (q, _) -> RelevanceVar q

let debug_print = function
  | SProp -> Pp.(str "SProp")
  | Prop -> Pp.(str "Prop")
  | Set -> Pp.(str "Set")
  | Type u -> Pp.(str "Type(" ++ Univ.Universe.raw_pr u ++ str ")")
  | QSort (q, u) -> Pp.(str "QSort(" ++ QVar.pr q ++ str ","
                        ++ spc() ++ Univ.Universe.raw_pr u ++ str ")")

let pr_sort_family = function
  | InSProp -> Pp.(str "SProp")
  | InProp -> Pp.(str "Prop")
  | InSet -> Pp.(str "Set")
  | InType -> Pp.(str "Type")
  | InQSort -> Pp.(str "Type") (* FIXME? *)

let subst_instance_sort u = function
  | SProp | Prop | Set as s -> s
  | Type v -> sort_of_univ (UVars.subst_instance_universe u v)
  | QSort (q, v) -> QSort (q, UVars.subst_instance_universe u v)
