(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CErrors
open Names
open Constr
open Mod_subst
open Libnames

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
    if ind==ind' then ref, mkConstruct ref
    else (ind',j), mkConstruct (ind',j)

let subst_global_reference subst ref = match ref with
  | VarRef var -> ref
  | ConstRef kn ->
    let kn' = subst_constant subst kn in
      if kn==kn' then ref else ConstRef kn'
  | IndRef ind ->
    let ind' = subst_ind subst ind in
      if ind==ind' then ref else IndRef ind'
  | ConstructRef ((kn,i),j as c) ->
    let c',t = subst_constructor subst c in
      if c'==c then ref else ConstructRef c'

let subst_global subst ref = match ref with
  | VarRef var -> ref, mkVar var
  | ConstRef kn ->
     let kn',t = subst_con_kn subst kn in
      if kn==kn' then ref, mkConst kn else ConstRef kn', t
  | IndRef ind ->
      let ind' = subst_ind subst ind in
      if ind==ind' then ref, mkInd ind else IndRef ind', mkInd ind'
  | ConstructRef ((kn,i),j as c) ->
      let c',t = subst_constructor subst c in
	if c'==c then ref,t else ConstructRef c', t

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

let global_eq_gen eq_cst eq_ind eq_cons x y =
  x == y ||
  match x, y with
  | ConstRef cx, ConstRef cy -> eq_cst cx cy
  | IndRef indx, IndRef indy -> eq_ind indx indy
  | ConstructRef consx, ConstructRef consy -> eq_cons consx consy
  | VarRef v1, VarRef v2 -> Id.equal v1 v2
  | (VarRef _ | ConstRef _ | IndRef _ | ConstructRef _), _ -> false

let global_ord_gen ord_cst ord_ind ord_cons x y =
  if x == y then 0
  else match x, y with
  | VarRef v1, VarRef v2 -> Id.compare v1 v2
  | VarRef _, _ -> -1
  | _, VarRef _ -> 1
  | ConstRef cx, ConstRef cy -> ord_cst cx cy
  | ConstRef _, _ -> -1
  | _, ConstRef _ -> 1
  | IndRef indx, IndRef indy -> ord_ind indx indy
  | IndRef _, _ -> -1
  | _ , IndRef _ -> 1
  | ConstructRef consx, ConstructRef consy -> ord_cons consx consy

let global_hash_gen hash_cst hash_ind hash_cons gr =
  let open Hashset.Combine in
  match gr with
  | ConstRef c -> combinesmall 1 (hash_cst c)
  | IndRef i -> combinesmall 2 (hash_ind i)
  | ConstructRef c -> combinesmall 3 (hash_cons c)
  | VarRef id -> combinesmall 4 (Id.hash id)

(* By default, [global_reference] are ordered on their canonical part *)

module RefOrdered = struct
  open Constant.CanOrd
  type t = global_reference
  let compare gr1 gr2 =
    global_ord_gen compare ind_ord constructor_ord gr1 gr2
  let equal gr1 gr2 = global_eq_gen equal eq_ind eq_constructor gr1 gr2
  let hash gr = global_hash_gen hash ind_hash constructor_hash gr
end

module RefOrdered_env = struct
  open Constant.UserOrd
  type t = global_reference
  let compare gr1 gr2 =
    global_ord_gen compare ind_user_ord constructor_user_ord gr1 gr2
  let equal gr1 gr2 =
    global_eq_gen equal eq_user_ind eq_user_constructor gr1 gr2
  let hash gr = global_hash_gen hash ind_user_hash constructor_user_hash gr
end

module Refmap = HMap.Make(RefOrdered)
module Refset = Refmap.Set

(* Alternative sets and maps indexed by the user part of the kernel names *)

module Refmap_env = HMap.Make(RefOrdered_env)
module Refset_env = Refmap_env.Set

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
    | TrueGlobal rx, TrueGlobal ry -> RefOrdered_env.equal rx ry
    | SynDef knx, SynDef kny -> KerName.equal knx kny
    | (TrueGlobal _ | SynDef _), _ -> false

  let compare x y =
    if x == y then 0
    else match x, y with
      | TrueGlobal rx, TrueGlobal ry -> RefOrdered_env.compare rx ry
      | SynDef knx, SynDef kny -> KerName.compare knx kny
      | TrueGlobal _, SynDef _ -> -1
      | SynDef _, TrueGlobal _ -> 1

  open Hashset.Combine

  let hash = function
  | TrueGlobal gr -> combinesmall 1 (RefOrdered_env.hash gr)
  | SynDef kn -> combinesmall 2 (KerName.hash kn)

end

type global_reference_or_constr = 
  | IsGlobal of global_reference
  | IsConstr of constr

(** {6 Temporary function to brutally form kernel names from section paths } *)

let encode_mind dir id = MutInd.make2 (MPfile dir) (Label.of_id id)

let encode_con dir id = Constant.make2 (MPfile dir) (Label.of_id id)

let check_empty_section dp =
  if not (DirPath.is_empty dp) then
    anomaly (Pp.str "Section part should be empty!")

let decode_mind kn =
  let rec dir_of_mp = function
    | MPfile dir -> DirPath.repr dir
    | MPbound mbid ->
	let _,_,dp = MBId.repr mbid in
	let id = MBId.to_id mbid in
	  id::(DirPath.repr dp)
    | MPdot(mp,l) -> (Label.to_id l)::(dir_of_mp mp)
  in
  let mp,sec_dir,l = MutInd.repr3 kn in
  check_empty_section sec_dir;
  (DirPath.make (dir_of_mp mp)),Label.to_id l

let decode_con kn =
  let mp,sec_dir,l = Constant.repr3 kn in
  check_empty_section sec_dir;
  match mp with
    | MPfile dir -> (dir,Label.to_id l)
    | _ -> anomaly (Pp.str "MPfile expected!")

(** Popping one level of section in global names.
    These functions are meant to be used during discharge:
    user and canonical kernel names must be equal. *)

let pop_con con =
  let (mp,dir,l) = Constant.repr3 con in
  Constant.make3 mp (pop_dirpath dir) l

let pop_kn kn =
  let (mp,dir,l) = MutInd.repr3 kn in
  MutInd.make3 mp (pop_dirpath dir) l

let pop_global_reference = function
  | ConstRef con -> ConstRef (pop_con con)
  | IndRef (kn,i) -> IndRef (pop_kn kn,i)
  | ConstructRef ((kn,i),j) -> ConstructRef ((pop_kn kn,i),j)
  | VarRef id -> anomaly (Pp.str "VarRef not poppable.")

(* Deprecated *)
let eq_gr = GlobRef.equal
