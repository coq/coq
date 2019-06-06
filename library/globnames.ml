(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Constr
open Mod_subst

(*s Global reference is a kernel side type for all references together *)
type global_reference = GlobRef.t =
  | VarRef of variable           (** A reference to the section-context. *)
  | ConstRef of Constant.t       (** A reference to the environment. *)
  | IndRef of inductive          (** A reference to an inductive type. *)
  | ConstructRef of constructor  (** A reference to a constructor of an inductive type. *)

let isVarRef = function VarRef _ -> true | _ -> false
let isConstRef = function ConstRef _ -> true | _ -> false
let isIndRef = function IndRef _ -> true | _ -> false
let isConstructRef = function ConstructRef _ -> true | _ -> false

let destVarRef = function VarRef ind -> ind | _ -> failwith "destVarRef"
let destConstRef = function ConstRef ind -> ind | _ -> failwith "destConstRef"
let destIndRef = function IndRef ind -> ind | _ -> failwith "destIndRef"
let destConstructRef = function ConstructRef ind -> ind | _ -> failwith "destConstructRef"

let subst_constructor subst (ind,j as ref) =
  let ind' = subst_ind subst ind in
  if ind==ind' then ref
  else (ind',j)

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

let is_global c t =
  match c, kind t with
  | ConstRef c, Const (c', _) -> Constant.equal c c'
  | IndRef i, Ind (i', _) -> eq_ind i i'
  | ConstructRef i, Construct (i', _) -> eq_constructor i i'
  | VarRef id, Var id' -> Id.equal id id'
  | _ -> false

let printable_constr_of_global = function
  | VarRef id -> mkVar id
  | ConstRef sp -> mkConst sp
  | ConstructRef sp -> mkConstruct sp
  | IndRef sp -> mkInd sp

(* Extended global references *)

type syndef_name = KerName.t

type extended_global_reference =
  | TrueGlobal of global_reference
  | SynDef of syndef_name

(* We order [extended_global_reference] via their user part
   (cf. pretty printer) *)

module ExtRefOrdered = struct
  type t = extended_global_reference

  let equal x y =
    x == y ||
    match x, y with
    | TrueGlobal rx, TrueGlobal ry -> GlobRef.Ordered_env.equal rx ry
    | SynDef knx, SynDef kny -> KerName.equal knx kny
    | (TrueGlobal _ | SynDef _), _ -> false

  let compare x y =
    if x == y then 0
    else match x, y with
      | TrueGlobal rx, TrueGlobal ry -> GlobRef.Ordered_env.compare rx ry
      | SynDef knx, SynDef kny -> KerName.compare knx kny
      | TrueGlobal _, SynDef _ -> -1
      | SynDef _, TrueGlobal _ -> 1

  open Hashset.Combine

  let hash = function
  | TrueGlobal gr -> combinesmall 1 (GlobRef.Ordered_env.hash gr)
  | SynDef kn -> combinesmall 2 (KerName.hash kn)

end

type global_reference_or_constr = 
  | IsGlobal of global_reference
  | IsConstr of constr
