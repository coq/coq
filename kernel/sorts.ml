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

module QGlobal = struct
  open Names

  type t = {
    library : DirPath.t;
    (* uid is unique for the library *)
    uid : int;
  }

  let make library uid = { library; uid }

  let repr x = (x.library, x.uid)

  let equal u1 u2 =
    Int.equal u1.uid u2.uid &&
    DirPath.equal u1.library u2.library

  let hash u = Hashset.Combine.combine (Int.hash u.uid) (DirPath.hash u.library)

  let compare u1 u2 =
    let c = Int.compare u1.uid u2.uid in
    if c <> 0 then c
    else
      DirPath.compare u1.library u2.library

  let to_string { library = d; uid } =
    Printf.sprintf "%s.%d" (DirPath.to_string d) uid

  let raw_pr id = Pp.str @@ Printf.sprintf "γ%s" (to_string id)

  module Hstruct = struct
    type nonrec t = t

    let hashcons ({ library; uid } as v) =
      let hl, l' = DirPath.hcons library in
      let v = if l' == library then v else { library = l'; uid } in
      Hashset.Combine.combine hl uid, v

    let eq a b = a.library == b.library && a.uid == b.uid
  end

  module Hasher = Hashcons.Make(Hstruct)

  let hcons = Hashcons.simple_hcons Hasher.generate Hasher.hcons ()

  module Self = struct type nonrec t = t let compare = compare end
  module Set =
  struct
    include CSet.Make(Self)
    let pr prl s =
      let open Pp in
      hov 1 (str"{" ++ prlist_with_sep spc prl (elements s) ++ str"}")
  end

end

module QVar =
struct
  type repr =
    | Var of int
    | Secvar of int
    | Unif of string * int
  type t = repr

  let make_var n = Var n

  let make_secvar n = Secvar n

  let make_unif s n = Unif (s,n)

  let var_index = function
    | Var q -> Some q
    | Secvar _ | Unif _ -> None

  let hash = function
    | Var q -> Hashset.Combine.combinesmall 1 q
    | Secvar q -> Hashset.Combine.combinesmall 2 q
    | Unif (s,q) -> Hashset.Combine.(combinesmall 3 (combine (CString.hash s) q))

  module Hstruct = struct
    type nonrec t = t

    open Hashset.Combine

    let hashcons = function
      | Var qv as q -> combinesmall 1 qv, q
      | Secvar qv as q -> combinesmall 2 qv, q
      | Unif (s,i) as q ->
        let hs, s' = CString.hcons s in
        combinesmall 3 (combine hs i), if s == s' then q else Unif (s',i)

    let eq a b =
      match a, b with
      | Var a, Var b -> Int.equal a b
      | Secvar a, Secvar b -> Int.equal a b
      | Unif (sa, ia), Unif (sb, ib) -> sa == sb && Int.equal ia ib
      | (Var _ | Secvar _ | Unif _), _ -> false
  end

  module Hasher = Hashcons.Make(Hstruct)

  let hcons = Hashcons.simple_hcons Hasher.generate Hasher.hcons ()

  let compare a b = match a, b with
    | Var a, Var b -> Int.compare a b
    | Var _, _ -> -1
    | _, Var _ -> 1
    | Secvar a, Secvar b -> Int.compare a b
    | Secvar _, _ -> -1
    | _, Secvar _ -> 1
    | Unif (s1,i1), Unif (s2,i2) ->
      let c = Int.compare i1 i2 in
      if c <> 0 then c
      else CString.compare s1 s2

  let equal a b = match a, b with
    | Var a, Var b ->  Int.equal a b
    | Secvar a, Secvar b -> Int.equal a b
    | Unif (s1,i1), Unif (s2,i2) ->
      Int.equal i1 i2 && CString.equal s1 s2
    | (Var _| Secvar _ | Unif _), _ -> false

  let to_string = function
    | Var q -> Printf.sprintf "β%d" q
    | Secvar q -> Printf.sprintf "βsec%d" q
    | Unif (s,q) ->
      let s = if CString.is_empty s then "" else s^"." in
      Printf.sprintf "%sα%d" s q

  let raw_pr q = Pp.str (to_string q)

  let repr x = x
  let of_repr x = x

  let is_secvar = function
    | Secvar _ -> true
    | Unif _ | Var _ -> false

  let is_unif = function
    | Unif _ -> true
    | Secvar _ | Var _ -> false

  module Self = struct type nonrec t = t let compare = compare end
  module Set =
  struct
    include CSet.Make(Self)
    let pr prl s =
      let open Pp in
      hov 1 (str"{" ++ prlist_with_sep spc prl (elements s) ++ str"}")
  end
  module Map = CMap.Make(Self)
end

module Quality = struct
  type constant = QProp | QSProp | QType
  type t = QVar of QVar.t | QConstant of constant | QGlobal of QGlobal.t

  let var i = QVar (QVar.make_var i)
  let global sg = QGlobal sg

  let var_index = function
    | QVar q -> QVar.var_index q
    | QConstant _ | QGlobal _ -> None

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

    let all = [QSProp; QProp; QType]
  end

  let equal a b = match a, b with
    | QVar a, QVar b -> QVar.equal a b
    | QConstant a, QConstant b -> Constants.equal a b
    | QGlobal ida, QGlobal idb -> QGlobal.equal ida idb
    | (QVar _ | QConstant _ | QGlobal _), _ -> false

  let compare a b = match a, b with
    | QVar a, QVar b -> QVar.compare a b
    | QVar _, _ -> -1
    | _, QVar _ -> 1
    | QConstant a, QConstant b -> Constants.compare a b
    | QConstant _, _ -> -1
    | _, QConstant _ -> 1
    | QGlobal a, QGlobal b -> QGlobal.compare a b

  type printer = {
    prvar : QVar.t -> Pp.t;
    prglobal : QGlobal.t -> Pp.t;
  }

  let pr prv = function
    | QVar v -> prv.prvar v
    | QConstant q -> Constants.pr q
    | QGlobal id -> prv.prglobal id

  let raw_printer = {
    prvar = QVar.raw_pr;
    prglobal = QGlobal.raw_pr;
  }

  let raw_pr q = pr raw_printer q

  let all_constants = List.map (fun q -> QConstant q) Constants.all

  let hash = let open Hashset.Combine in function
    | QConstant q -> Constants.hash q
    (* combinesmall 3 because constants.hash in [0;2] *)
    | QVar q -> combinesmall 3 (QVar.hash q)
    | QGlobal q -> combinesmall 4 (QGlobal.hash q)

  let subst f = function
    | QConstant _ | QGlobal _ as q -> q
    | QVar qv as q ->
      match f qv with
      | QConstant _ | QGlobal _ as q -> q
      | QVar qv' as q' ->
        if qv == qv' then q else q'

  let subst_fn m v =
    match QVar.Map.find_opt v m with
    | Some v -> v
    | None -> QVar v

  module Hstruct = struct
    type nonrec t = t

    let hashcons = function
      | QConstant c as q -> Constants.hash c, q
      | QVar qv as q ->
        let hqv, qv' = QVar.hcons qv in
        Hashset.Combine.combinesmall 3 hqv, if qv == qv' then q else QVar qv'
      | QGlobal qv as q ->
        (* XXX hashcons qglobals *)
        Hashset.Combine.combinesmall 4 (QGlobal.hash qv), q

    let eq a b =
      match a, b with
      | QVar a, QVar b -> a == b
      | QVar _, _ -> false
      | (QConstant _ | QGlobal _), _ -> equal a b
  end

  module Hasher = Hashcons.Make(Hstruct)

  let hcons = Hashcons.simple_hcons Hasher.generate Hasher.hcons ()

  let qsprop = snd @@ hcons (QConstant QSProp)
  let qprop = snd @@ hcons (QConstant QProp)
  let qtype = snd @@ hcons (QConstant QType)

  let is_qsprop = equal qsprop
  let is_qprop = equal qprop
  let is_qtype = equal qtype
  let is_qvar q = match q with QVar _ -> true | _ -> false
  let is_qconst q = match q with QConstant _ -> true | _ -> false
  let is_qglobal q = match q with QGlobal _ -> true | _ -> false
  let is_impredicative q = is_qsprop q || is_qprop q

  module Self = struct type nonrec t = t let compare = compare end
  module Set = struct
    include CSet.Make(Self)
    let of_qvars qs =
      QVar.Set.fold (fun qv acc -> add (QVar qv) acc) qs empty
    let of_qglobals qs =
      QGlobal.Set.fold (fun qv acc -> add (QGlobal qv) acc) qs empty
  end
  module Map = CMap.Make(Self)

  type 'q pattern =
    | PQVar of 'q | PQConstant of constant | PQGlobal of QGlobal.t

  let pattern_match ps s qusubst =
    match ps, s with
    | PQConstant qc, QConstant qc' -> if Constants.equal qc qc' then Some qusubst else None
    | PQGlobal qg, QGlobal qg' -> if QGlobal.equal qg qg' then Some qusubst else None
    | PQVar qio, q -> Some (Partial_subst.maybe_add_quality qio q qusubst)
    | (PQConstant _ | PQGlobal _), _ -> None
end

module ElimConstraint = struct
  type kind = ElimTo

  let eq_kind : kind -> kind -> bool = (=)
  let compare_kind : kind -> kind -> int = compare

  let hash_kind = function
  | ElimTo -> 0

  let pr_kind = function
  | ElimTo -> Pp.str "->"

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

  let pr prq (a,k,b) =
    let open Pp in
    hov 1 (Quality.pr prq a ++ spc() ++ pr_kind k ++ spc() ++ Quality.pr prq b)

  let raw_pr x = pr Quality.raw_printer x

  module Hstruct = struct
    type nonrec t = t

    let hashcons (q1,k,q2) =
      let hq1, q1 = Quality.hcons q1 in
      let hq2, q2 = Quality.hcons q2 in
      Hashset.Combine.(combinesmall (hash_kind k) (combine hq1 hq2)), (q1,k,q2)

    let eq (q1,k,q2) (q1',k',q2') =
      eq_kind k k' && q1 == q1' && q2 == q2'
  end

  module Hasher = Hashcons.Make(Hstruct)

  let hcons = Hashcons.simple_hcons Hasher.generate Hasher.hcons ()
end

module ElimConstraints = struct include CSet.Make(ElimConstraint)
  let pr prq c =
    let open Pp in
    v 0 (prlist_with_sep spc (fun (u1,op,u2) ->
      hov 0 (Quality.pr prq u1 ++ spc() ++ ElimConstraint.pr_kind op ++ spc() ++ Quality.pr prq u2))
       (elements c))

  module HConstraints = CSet.Hashcons(ElimConstraint)(struct
      type t = ElimConstraint.t
      let hcons = ElimConstraint.hcons
    end)

  let hcons = Hashcons.simple_hcons HConstraints.generate HConstraints.hcons ()
end

module QContextSet =
struct
  type t = QVar.Set.t * ElimConstraints.t
  let empty = (QVar.Set.empty, ElimConstraints.empty)
  let is_empty (q,c) = QVar.Set.is_empty q && ElimConstraints.is_empty c
  let union (q1, c1) (q2, c2) = (QVar.Set.union q1 q2, ElimConstraints.union c1 c2)
end

(* XXX simplify this type to quality * universe
   with invariant that if quality is impredicative then universe=0? *)
type t =
  | SProp
  | Prop
  | Set
  | Type of Universe.t
  | GSort of QGlobal.t * Universe.t
  | VSort of QVar.t * Universe.t

let sprop = SProp
let prop = Prop
let set = Set
let type1 = Type Universe.type1
let gsort q u = GSort (q, u)
let vsort q u = VSort (q, u)

let sort_of_univ u =
  if Universe.is_type0 u then set else Type u

let univ_of_sort s =
  match s with
  | SProp | Prop | Set -> Universe.type0
  | Type u | GSort (_, u) | VSort (_, u) -> u

let make q u =
  let open Quality in
  match q with
  | QVar q -> vsort q u
  | QGlobal q -> gsort q u
  | QConstant QSProp -> sprop
  | QConstant QProp -> prop
  | QConstant QType -> sort_of_univ u

let compare s1 s2 =
  if s1 == s2 then 0 else
    match s1, s2 with
    | SProp, SProp -> 0
    | SProp, _ -> -1
    | _, SProp -> 1
    | Prop, Prop -> 0
    | Prop, _ -> -1
    | _, Prop -> 1
    | Set, Set -> 0
    | Set, _ -> -1
    | _, Set -> 1
    | Type u1, Type u2 -> Universe.compare u1 u2
    | Type _, _ -> -1
    | _, Type _ -> 1
    | GSort (q1, u1), GSort (q2, u2) ->
      let c = QGlobal.compare q1 q2 in
      if Int.equal c 0 then Universe.compare u1 u2 else c
    | GSort _, _ -> -1
    | _, GSort _ -> 1
    | VSort (q1, u1), VSort (q2, u2) ->
      let c = QVar.compare q1 q2 in
      if Int.equal c 0 then Universe.compare u1 u2 else c

let equal s1 s2 = Int.equal (compare s1 s2) 0

let super = function
  | SProp | Prop | Set -> Type (Universe.type1)
  | Type u | GSort (_, u) | VSort (_, u) -> Type (Universe.super u)

let is_sprop = function
  | SProp -> true
  | _ -> false

let is_prop = function
  | Prop -> true
  |  _-> false

let is_set = function
  | Set -> true
  | _ -> false

let levels s = match s with
| SProp | Prop -> Level.Set.empty
| Set -> Level.Set.singleton Level.set
| Type u | GSort (_, u) | VSort (_, u) -> Universe.levels u

let subst_fn (fq,fu) = function
  | SProp | Prop | Set as s -> s
  | Type v as s ->
    let v' = fu v in
    if v' == v then s else sort_of_univ v'
  | GSort (q, v) as s ->
    let v' = fu v in
    if v' == v then s else gsort q v'
  | VSort (q, v) as s ->
    let open Quality in
    match fq q with
    | QVar q' ->
      let v' = fu v in
      if q' == q && v' == v then s
      else vsort q' v'
    | QConstant QSProp -> sprop
    | QConstant QProp -> prop
    | q' -> make q' (fu v)

let quality = let open Quality in function
| Set | Type _ -> qtype
| Prop -> qprop
| SProp -> qsprop
| GSort (q, _) -> QGlobal q
| VSort (q, _) -> QVar q

open Hashset.Combine

let hash = function
  | SProp -> combinesmall 1 0
  | Prop -> combinesmall 1 1
  | Set -> combinesmall 1 2
  | Type u ->
    let h = Univ.Universe.hash u in
    combinesmall 2 h
  | GSort (q, u) ->
    let h = Univ.Universe.hash u in
    let h' = QGlobal.hash q in
    combinesmall 3 (combine h h')
  | VSort (q, u) ->
    let h = Univ.Universe.hash u in
    let h' = QVar.hash q in
    combinesmall 4 (combine h h')

module HSorts =
  Hashcons.Make(
    struct
      type nonrec t = t

      let hashcons = function
        | Type u as c ->
          let hu, u' = Universe.hcons u in
          combinesmall 2 hu, if u' == u then c else Type u'
        | GSort (q, u) as c ->
          let hq, q' = QGlobal.hcons q in
          let hu, u' = Universe.hcons u in
          combinesmall 3 (combine hu hq), if u' == u && q' == q then c else GSort (q', u')
        | VSort (q, u) as c ->
          let hq, q' = QVar.hcons q in
          let hu, u' = Universe.hcons u in
          combinesmall 4 (combine hu hq), if u' == u && q' == q then c else VSort (q', u')
        | SProp | Prop | Set as s -> hash s, s

      let eq s1 s2 = match (s1,s2) with
        | SProp, SProp | Prop, Prop | Set, Set -> true
        | (Type u1, Type u2) -> u1 == u2
        | GSort (q1, u1), GSort (q2, u2) -> q1 == q2 && u1 == u2
        | VSort (q1, u1), VSort (q2, u2) -> q1 == q2 && u1 == u2
        | (SProp | Prop | Set | Type _ | GSort _ | VSort _), _ -> false
    end)

let hcons = Hashcons.simple_hcons HSorts.generate HSorts.hcons ()

(** On binders: is this variable proof relevant *)
type relevance = Relevant | Irrelevant | RelevanceVar of QVar.t

let relevance_equal r1 r2 = match r1,r2 with
  | Relevant, Relevant | Irrelevant, Irrelevant -> true
  | RelevanceVar q1, RelevanceVar q2 -> QVar.equal q1 q2
  | (Relevant | Irrelevant | RelevanceVar _), _ -> false

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
    | QConstant (QProp | QType) | QGlobal _ -> Relevant
    | QVar qv' ->
      if qv' == qv then r else RelevanceVar qv'

let relevance_of_sort = function
  | SProp -> Irrelevant
  | Prop | Set | Type _ | GSort _ -> Relevant
  | VSort (q, _) -> RelevanceVar q

let is_relevant = function
  | Relevant -> true
  | Irrelevant | RelevanceVar _ -> false

let debug_print = function
  | SProp -> Pp.(str "SProp")
  | Prop -> Pp.(str "Prop")
  | Set -> Pp.(str "Set")
  | Type u -> Pp.(str "Type(" ++ Univ.Universe.raw_pr u ++ str ")")
  | GSort (q, u) -> Pp.(str "QSort(" ++ QGlobal.raw_pr q ++ str ","
                        ++ spc() ++ Univ.Universe.raw_pr u ++ str ")")
  | VSort (q, u) -> Pp.(str "VSort(" ++ QVar.raw_pr q ++ str ","
                        ++ spc() ++ Univ.Universe.raw_pr u ++ str ")")

type printer = {
  prq : Quality.printer;
  pru : Level.t -> Pp.t;
}

let pr printer = function
  | SProp -> Pp.(str "SProp")
  | Prop -> Pp.(str "Prop")
  | Set -> Pp.(str "Set")
  | Type u -> Pp.(str "Type@{" ++ Universe.pr printer.pru u ++ str "}")
  | GSort (q, u) ->
    Pp.(hov 0 (str "Type@{" ++ printer.prq.prglobal q ++ str ";"
               ++ spc() ++ Universe.pr printer.pru u ++ str "}"))
  | VSort (q, u) ->
    Pp.(hov 0 (str "Type@{" ++ printer.prq.prvar q ++ str ";"
               ++ spc() ++ Universe.pr printer.pru u ++ str "}"))

let raw_printer = {
  prq = Quality.raw_printer;
  pru = Level.raw_pr;
}

let raw_pr = pr raw_printer

type ('q, 'u) pattern =
  | PSProp | PSSProp | PSSet | PSType of 'u | PSGlobal of QGlobal.t * 'u | PSQSort of 'q * 'u

let make_pattern q u =
  let open Quality in
  match q with
  | PQConstant QSProp -> PSSProp
  | PQConstant QProp -> PSProp
  | PQConstant QType -> PSType u
  | PQGlobal g -> PSGlobal (g, u)
  | PQVar q -> PSQSort (q, u)

let extract_level u =
  match Universe.level u with
  | Some l -> l
  | None -> CErrors.anomaly Pp.(str "Tried to extract level of an algebraic universe")

let extract_sort_level = function
  | Type u | GSort (_, u) | VSort (_, u) -> extract_level u
  | Prop | SProp | Set -> Univ.Level.set

let pattern_match ps s qusubst =
  match ps, s with
  | PSProp, Prop -> Some qusubst
  | PSSProp, SProp -> Some qusubst
  | PSSet, Set -> Some qusubst
  | PSType uio, Set -> Some (Partial_subst.maybe_add_univ uio Univ.Level.set qusubst)
  | PSType uio, Type u -> Some (Partial_subst.maybe_add_univ uio (extract_level u) qusubst)
  | PSGlobal (qg, uio), GSort (qg', u) -> if QGlobal.equal qg qg' then Some (Partial_subst.maybe_add_univ uio (extract_level u) qusubst) else None
  | PSQSort (qio, uio), s -> Some (qusubst |> Partial_subst.maybe_add_quality qio (quality s) |> Partial_subst.maybe_add_univ uio (extract_sort_level s))
  | (PSProp | PSSProp | PSSet | PSType _ | PSGlobal _), _ -> None
