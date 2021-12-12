(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Constr
open Mod_subst

type global_reference = GlobRef.t =
  | VarRef of variable     [@ocaml.deprecated "Use Names.GlobRef.VarRef"]
  | ConstRef of Constant.t [@ocaml.deprecated "Use Names.GlobRef.ConstRef"]
  | IndRef of inductive    [@ocaml.deprecated "Use Names.GlobRef.IndRef"]
  | ConstructRef of constructor [@ocaml.deprecated "Use Names.GlobRef.ConstructRef"]
[@@ocaml.deprecated "Use Names.GlobRef.t"]

open GlobRef

let isVarRef = function VarRef _ -> true | _ -> false
let isConstRef = function ConstRef _ -> true | _ -> false
let isIndRef = function IndRef _ -> true | _ -> false
let isConstructRef = function ConstructRef _ -> true | _ -> false

let destVarRef = function VarRef ind -> ind | _ -> failwith "destVarRef"
let destConstRef = function ConstRef ind -> ind | _ -> failwith "destConstRef"
let destIndRef = function IndRef ind -> ind | _ -> failwith "destIndRef"
let destConstructRef = function ConstructRef ind -> ind | _ -> failwith "destConstructRef"


let subst_global_reference subst ref = match ref with
  | VarRef var -> ref
  | ConstRef kn ->
    let kn' = subst_constant subst kn in
      if kn==kn' then ref else ConstRef kn'
  | IndRef ind ->
    let ind' = subst_ind subst ind in
      if ind==ind' then ref else IndRef ind'
  | ConstructRef ((kn,i),j as c) ->
    let c' = subst_constructor subst c in
    if c'==c then ref else ConstructRef c'

let subst_global subst ref = match ref with
  | VarRef var -> ref, None
  | ConstRef kn ->
     let kn',t = subst_con subst kn in
      if kn==kn' then ref, None else ConstRef kn', t
  | IndRef ind ->
      let ind' = subst_ind subst ind in
      if ind==ind' then ref, None else IndRef ind', None
  | ConstructRef ((kn,i),j as c) ->
      let c' = subst_constructor subst c in
      if c'==c then ref,None else ConstructRef c', None

let canonical_gr = function
  | ConstRef con -> ConstRef(Constant.make1 (Constant.canonical con))
  | IndRef (kn,i) -> IndRef(MutInd.make1(MutInd.canonical kn),i)
  | ConstructRef ((kn,i),j )-> ConstructRef((MutInd.make1(MutInd.canonical kn),i),j)
  | VarRef id -> VarRef id

let global_of_constr c = match kind c with
  | Const (sp,u) -> ConstRef sp
  | Ind (ind_sp,u) -> IndRef ind_sp
  | Construct (cstr_cp,u) -> ConstructRef cstr_cp
  | Var id -> VarRef id
  |  _ -> raise Not_found

let is_global = Constr.isRefX

let printable_constr_of_global = function
  | VarRef id -> mkVar id
  | ConstRef sp -> mkConst sp
  | ConstructRef sp -> mkConstruct sp
  | IndRef sp -> mkInd sp

(* Extended global references *)

type abbreviation = KerName.t

type extended_global_reference =
  | TrueGlobal of GlobRef.t
  | Abbrev of abbreviation

(* We order [extended_global_reference] via their user part
   (cf. pretty printer) *)

module ExtRefOrdered = struct
  type t = extended_global_reference

  let equal x y =
    x == y ||
    match x, y with
    | TrueGlobal rx, TrueGlobal ry -> GlobRef.UserOrd.equal rx ry
    | Abbrev knx, Abbrev kny -> KerName.equal knx kny
    | (TrueGlobal _ | Abbrev _), _ -> false

  let compare x y =
    if x == y then 0
    else match x, y with
      | TrueGlobal rx, TrueGlobal ry -> GlobRef.UserOrd.compare rx ry
      | Abbrev knx, Abbrev kny -> KerName.compare knx kny
      | TrueGlobal _, Abbrev _ -> -1
      | Abbrev _, TrueGlobal _ -> 1

  open Hashset.Combine

  let hash = function
  | TrueGlobal gr -> combinesmall 1 (GlobRef.UserOrd.hash gr)
  | Abbrev kn -> combinesmall 2 (KerName.hash kn)

end

module ExtRefMap = HMap.Make(ExtRefOrdered)
module ExtRefSet = ExtRefMap.Set

let subst_extended_reference sub = function
  | Abbrev kn -> Abbrev (subst_kn sub kn)
  | TrueGlobal gr -> TrueGlobal (subst_global_reference sub gr)
