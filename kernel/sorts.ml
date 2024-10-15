(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
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

module QVar =
struct
  type repr =
    | Var of int
    | Unif of string * int

  type t = repr

  let make_var n = Var n

  let make_unif s n = Unif (s,n)

  let var_index = function
    | Var q -> Some q
    | Unif _ -> None

  let hash = function
    | Var q -> Hashset.Combine.combinesmall 1 q
    | Unif (s,q) -> Hashset.Combine.(combinesmall 2 (combine (CString.hash s) q))

  module Hstruct = struct
    type nonrec t = t
    type u = unit

    let hashcons () = function
      | Var _ as q -> q
      | Unif (s,i) as q ->
        let s' = CString.hcons s in
        if s == s' then q else Unif (s',i)

    let eq a b =
      match a, b with
      | Var a, Var b -> Int.equal a b
      | Unif (sa, ia), Unif (sb, ib) -> sa == sb && Int.equal ia ib
      | (Var _ | Unif _), _ -> false

    let hash = hash
  end

  module Hasher = Hashcons.Make(Hstruct)

  let hcons = Hashcons.simple_hcons Hasher.generate Hasher.hcons ()

  let compare a b = match a, b with
    | Var a, Var b -> Int.compare a b
    | Unif (s1,i1), Unif (s2,i2) ->
      let c = Int.compare i1 i2 in
      if c <> 0 then c
      else CString.compare s1 s2
    | Var _, Unif _ -> -1
    | Unif _, Var _ -> 1

  let equal a b = match a, b with
    | Var a, Var b ->  Int.equal a b
    | Unif (s1,i1), Unif (s2,i2) ->
      Int.equal i1 i2 && CString.equal s1 s2
    | Var _, Unif _ | Unif _, Var _ -> false

  let to_string = function
    | Var q -> Printf.sprintf "β%d" q
    | Unif (s,q) ->
      let s = if CString.is_empty s then "" else s^"." in
      Printf.sprintf "%sα%d" s q

  let raw_pr q = Pp.str (to_string q)

  let repr x = x
  let of_repr x = x

  module Self = struct type nonrec t = t let compare = compare end
  module Set = CSet.Make(Self)
  module Map = CMap.Make(Self)
end

module Quality = struct
  type constant = QProp | QSProp | QType
  type t = QVar of QVar.t | QConstant of constant

  let var i = QVar (QVar.make_var i)

  let var_index = function
    | QVar q -> QVar.var_index q
    | QConstant _ -> None

  module Constants = struct
    let equal a b = match a, b with
    | QProp, QProp | QSProp, QSProp | QType, QType -> true
    | (QProp | QSProp | QType), _ -> false

    let compare a b = match a, b with
      | QProp, QProp -> 0
      | QProp, _ -> -1
      | _, QProp -> 1
      | QSProp, QSProp -> 0
      | QSProp, _ -> -1
      | _, QSProp -> 1
      | QType, QType -> 0

    let pr = function
      | QProp -> Pp.str "Prop"
      | QSProp -> Pp.str "SProp"
      | QType -> Pp.str "Type"

    let hash = function
      | QSProp -> 0
      | QProp -> 1
      | QType -> 2

  end

  let equal a b = match a, b with
    | QVar a, QVar b -> QVar.equal a b
    | QConstant a, QConstant b -> Constants.equal a b
    | (QVar _ | QConstant _), _ -> false

  let compare a b = match a, b with
    | QVar a, QVar b -> QVar.compare a b
    | QVar _, _ -> -1
    | _, QVar _ -> 1
    | QConstant a, QConstant b -> Constants.compare a b

  let pr prv = function
    | QVar v -> prv v
    | QConstant q -> Constants.pr q

  let raw_pr q = pr QVar.raw_pr q

  let hash = let open Hashset.Combine in function
    | QConstant q -> Constants.hash q
    | QVar q -> combinesmall 3 (QVar.hash q)

  let subst f = function
    | QConstant _ as q -> q
    | QVar qv as q ->
      match f qv with
      | QConstant _ as q -> q
      | QVar qv' as q' ->
        if qv == qv' then q else q'

  let subst_fn m v =
    match QVar.Map.find_opt v m with
    | Some v -> v
    | None -> QVar v

  module Hstruct = struct
    type nonrec t = t
    type u = QVar.t -> QVar.t

    let hashcons hv = function
      | QConstant _ as q -> q
      | QVar qv as q ->
        let qv' = hv qv in
        if qv == qv' then q else QVar qv'

    let eq a b =
      match a, b with
      | QVar a, QVar b -> a == b
      | QVar _, _ -> false
      | (QConstant _), _ -> equal a b

    let hash = hash
  end

  module Hasher = Hashcons.Make(Hstruct)

  let hcons = Hashcons.simple_hcons Hasher.generate Hasher.hcons QVar.hcons

  let qsprop = hcons (QConstant QSProp)
  let qprop = hcons (QConstant QProp)
  let qtype = hcons (QConstant QType)

  module Self = struct type nonrec t = t let compare = compare end
  module Set = CSet.Make(Self)
  module Map = CMap.Make(Self)

  type pattern =
    | PQVar of int option | PQConstant of constant

  let pattern_match ps s qusubst =
    match ps, s with
    | PQConstant qc, QConstant qc' -> if Constants.equal qc qc' then Some qusubst else None
    | PQVar qio, q -> Some (Partial_subst.maybe_add_quality qio q qusubst)
    | PQConstant _, QVar _ -> None
end

module QConstraint = struct
  type kind = Equal | Leq

  let eq_kind : kind -> kind -> bool = (=)
  let compare_kind : kind -> kind -> int = compare

  let pr_kind = function
    | Equal -> Pp.str "="
    | Leq -> Pp.str "<="

  type t = Quality.t * kind * Quality.t

  let equal (a,k,b) (a',k',b') =
    eq_kind k k' && Quality.equal a a' && Quality.equal b b'

  let compare (a,k,b) (a',k',b') =
    let c = compare_kind k k' in
    if c <> 0 then c
    else
      let c = Quality.compare a a' in
      if c <> 0 then c
      else Quality.compare b b'

  let trivial (a,(Equal|Leq),b) = Quality.equal a b

  let pr prq (a,k,b) =
    let open Pp in
    hov 1 (Quality.pr prq a ++ spc() ++ pr_kind k ++ spc() ++ Quality.pr prq b)

  let raw_pr x = pr QVar.raw_pr x

end

module QConstraints = struct include CSet.Make(QConstraint)
  let trivial = for_all QConstraint.trivial

  let pr prq c =
    let open Pp in
    v 0 (prlist_with_sep spc (fun (u1,op,u2) ->
      hov 0 (Quality.pr prq u1 ++ QConstraint.pr_kind op ++ Quality.pr prq u2))
       (elements c))

end

let enforce_eq_quality a b csts =
  if Quality.equal a b then csts
  else QConstraints.add (a,QConstraint.Equal,b) csts

let enforce_leq_quality a b csts =
  if Quality.equal a b then csts
  else match a, b with
    | Quality.(QConstant QProp), Quality.(QConstant QType) -> csts
    | _ -> QConstraints.add (a,QConstraint.Leq,b) csts

module QUConstraints = struct

  type t = QConstraints.t * Univ.Constraints.t

  let empty = QConstraints.empty, Univ.Constraints.empty

  let union (qcsts,ucsts) (qcsts',ucsts') =
    QConstraints.union qcsts qcsts', Constraints.union ucsts ucsts'
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

let make q u =
  let open Quality in
  match q with
  | QVar q -> qsort q u
  | QConstant QSProp -> sprop
  | QConstant QProp -> prop
  | QConstant QType -> sort_of_univ u

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

let subst_fn (fq,fu) = function
  | SProp | Prop | Set as s -> s
  | Type v as s ->
    let v' = fu v in
    if v' == v then s else sort_of_univ v'
  | QSort (q, v) as s ->
    let open Quality in
    match fq q with
    | QVar q' ->
      let v' = fu v in
      if q' == q && v' == v then s
      else qsort q' v'
    | QConstant QSProp -> sprop
    | QConstant QProp -> prop
    | QConstant QType -> sort_of_univ (fu v)

let family = function
  | SProp -> InSProp
  | Prop -> InProp
  | Set -> InSet
  | Type _ -> InType
  | QSort _ -> InQSort

let quality = let open Quality in function
| Set | Type _ -> QConstant QType
| Prop -> QConstant QProp
| SProp -> QConstant QSProp
| QSort (q, _) -> QVar q

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

let family_equal a b =  match a, b with
  | InSProp, InSProp | InProp, InProp | InSet, InSet | InType, InType -> true
  | InQSort, InQSort -> true
  | (InSProp | InProp | InSet | InType | InQSort), _ -> false

let family_leq a b =
  family_equal a b
  || match a, b with
  | InSProp, _ -> true
  | InProp, InSet -> true
  | _, InType -> true
  | _ -> false

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

let relevance_subst_fn f = function
  | Relevant | Irrelevant as r -> r
  | RelevanceVar qv as r ->
    let open Quality in
    match f qv with
    | QConstant QSProp -> Irrelevant
    | QConstant (QProp | QType) -> Relevant
    | QVar qv' ->
      if qv' == qv then r else RelevanceVar qv'

let relevance_of_sort = function
  | SProp -> Irrelevant
  | Prop | Set | Type _ -> Relevant
  | QSort (q, _) -> RelevanceVar q

let debug_print = function
  | SProp -> Pp.(str "SProp")
  | Prop -> Pp.(str "Prop")
  | Set -> Pp.(str "Set")
  | Type u -> Pp.(str "Type(" ++ Univ.Universe.raw_pr u ++ str ")")
  | QSort (q, u) -> Pp.(str "QSort(" ++ QVar.raw_pr q ++ str ","
                        ++ spc() ++ Univ.Universe.raw_pr u ++ str ")")

let pr_sort_family = function
  | InSProp -> Pp.(str "SProp")
  | InProp -> Pp.(str "Prop")
  | InSet -> Pp.(str "Set")
  | InType -> Pp.(str "Type")
  | InQSort -> Pp.(str "Type") (* FIXME? *)

type pattern =
  | PSProp | PSSProp | PSSet | PSType of int option | PSQSort of int option * int option

let extract_level u =
  match Universe.level u with
  | Some l -> l
  | None -> CErrors.anomaly Pp.(str "Tried to extract level of an algebraic universe")

let extract_sort_level = function
  | Type u
  | QSort (_, u) -> extract_level u
  | Prop | SProp | Set -> Univ.Level.set

let pattern_match ps s qusubst =
  match ps, s with
  | PSProp, Prop -> Some qusubst
  | PSSProp, SProp -> Some qusubst
  | PSSet, Set -> Some qusubst
  | PSType uio, Set -> Some (Partial_subst.maybe_add_univ uio Univ.Level.set qusubst)
  | PSType uio, Type u -> Some (Partial_subst.maybe_add_univ uio (extract_level u) qusubst)
  | PSQSort (qio, uio), s -> Some (qusubst |> Partial_subst.maybe_add_quality qio (quality s) |> Partial_subst.maybe_add_univ uio (extract_sort_level s))
  | (PSProp | PSSProp | PSSet | PSType _), _ -> None
