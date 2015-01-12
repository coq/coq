(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Errors
open Names
open Term
open Mod_subst
open Libnames

(*s Global reference is a kernel side type for all references together *)
type global_reference =
  | VarRef of variable
  | ConstRef of constant
  | IndRef of inductive
  | ConstructRef of constructor

let isVarRef = function VarRef _ -> true | _ -> false
let isConstRef = function ConstRef _ -> true | _ -> false
let isIndRef = function IndRef _ -> true | _ -> false
let isConstructRef = function ConstructRef _ -> true | _ -> false

let eq_gr gr1 gr2 =
  gr1 == gr2 || match gr1,gr2 with
    | ConstRef con1, ConstRef con2 -> eq_constant con1 con2
    | IndRef kn1, IndRef kn2 -> eq_ind kn1 kn2
    | ConstructRef kn1, ConstructRef kn2 -> eq_constructor kn1 kn2
    | VarRef v1, VarRef v2 -> Id.equal v1 v2
    | _ -> false

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
  | ConstRef con -> ConstRef(constant_of_kn(canonical_con con))
  | IndRef (kn,i) -> IndRef(mind_of_kn(canonical_mind kn),i)
  | ConstructRef ((kn,i),j )-> ConstructRef((mind_of_kn(canonical_mind kn),i),j)
  | VarRef id -> VarRef id

let global_of_constr c = match kind_of_term c with
  | Const (sp,u) -> ConstRef sp
  | Ind (ind_sp,u) -> IndRef ind_sp
  | Construct (cstr_cp,u) -> ConstructRef cstr_cp
  | Var id -> VarRef id
  |  _ -> raise Not_found

let is_global c t =
  match c, kind_of_term t with
  | ConstRef c, Const (c', _) -> eq_constant c c'
  | IndRef i, Ind (i', _) -> eq_ind i i'
  | ConstructRef i, Construct (i', _) -> eq_constructor i i'
  | VarRef id, Var id' -> id_eq id id'
  | _ -> false

let printable_constr_of_global = function
  | VarRef id -> mkVar id
  | ConstRef sp -> mkConst sp
  | ConstructRef sp -> mkConstruct sp
  | IndRef sp -> mkInd sp

let reference_of_constr = global_of_constr

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
  | ConstRef cx, ConstRef cy -> ord_cst cx cy
  | IndRef indx, IndRef indy -> ord_ind indx indy
  | ConstructRef consx, ConstructRef consy -> ord_cons consx consy
  | VarRef v1, VarRef v2 -> Id.compare v1 v2

  | VarRef _, (ConstRef _ | IndRef _ | ConstructRef _) -> -1
  | ConstRef _, VarRef _ -> 1
  | ConstRef _, (IndRef _ | ConstructRef _) -> -1
  | IndRef _, (VarRef _ | ConstRef _) -> 1
  | IndRef _, ConstructRef _ -> -1
  | ConstructRef _, (VarRef _ | ConstRef _ | IndRef _) -> 1

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

type syndef_name = kernel_name

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
      | SynDef knx, SynDef kny -> kn_ord knx kny
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
  let mp,sec_dir,l = repr_mind kn in
  check_empty_section sec_dir;
  (DirPath.make (dir_of_mp mp)),Label.to_id l

let decode_con kn =
  let mp,sec_dir,l = repr_con kn in
  check_empty_section sec_dir;
  match mp with
    | MPfile dir -> (dir,Label.to_id l)
    | _ -> anomaly (Pp.str "MPfile expected!")

(** Popping one level of section in global names.
    These functions are meant to be used during discharge:
    user and canonical kernel names must be equal. *)

let pop_con con =
  let (mp,dir,l) = repr_con con in
  Names.make_con mp (pop_dirpath dir) l

let pop_kn kn =
  let (mp,dir,l) = repr_mind kn in
  Names.make_mind mp (pop_dirpath dir) l

let pop_global_reference = function
  | ConstRef con -> ConstRef (pop_con con)
  | IndRef (kn,i) -> IndRef (pop_kn kn,i)
  | ConstructRef ((kn,i),j) -> ConstructRef ((pop_kn kn,i),j)
  | VarRef id -> anomaly (Pp.str "VarRef not poppable")
