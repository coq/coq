(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

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
  match gr1,gr2 with
    | ConstRef con1, ConstRef con2 -> eq_constant con1 con2
    | IndRef kn1,IndRef kn2 -> eq_ind kn1 kn2
    | ConstructRef kn1,ConstructRef kn2 -> eq_constructor kn1 kn2
    | _,_ -> gr1=gr2

let destVarRef = function VarRef ind -> ind | _ -> failwith "destVarRef"
let destConstRef = function ConstRef ind -> ind | _ -> failwith "destConstRef"
let destIndRef = function IndRef ind -> ind | _ -> failwith "destIndRef"
let destConstructRef = function ConstructRef ind -> ind | _ -> failwith "destConstructRef"

let subst_constructor subst ((kn,i),j as ref) =
  let kn' = subst_ind subst kn in
    if kn==kn' then ref, mkConstruct ref
    else ((kn',i),j), mkConstruct ((kn',i),j)

let subst_global subst ref = match ref with
  | VarRef var -> ref, mkVar var
  | ConstRef kn ->
     let kn',t = subst_con subst kn in
      if kn==kn' then ref, mkConst kn else ConstRef kn', t
  | IndRef (kn,i) ->
      let kn' = subst_ind subst kn in
      if kn==kn' then ref, mkInd (kn,i) else IndRef(kn',i), mkInd (kn',i)
  | ConstructRef ((kn,i),j as c) ->
      let c',t = subst_constructor subst c in
	if c'==c then ref,t else ConstructRef c', t

let canonical_gr = function
  | ConstRef con -> ConstRef(constant_of_kn(canonical_con con))
  | IndRef (kn,i) -> IndRef(mind_of_kn(canonical_mind kn),i)
  | ConstructRef ((kn,i),j )-> ConstructRef((mind_of_kn(canonical_mind kn),i),j)
  | VarRef id -> VarRef id

let global_of_constr c = match kind_of_term c with
  | Const sp -> ConstRef sp
  | Ind ind_sp -> IndRef ind_sp
  | Construct cstr_cp -> ConstructRef cstr_cp
  | Var id -> VarRef id
  |  _ -> raise Not_found

let constr_of_global = function
  | VarRef id -> mkVar id
  | ConstRef sp -> mkConst sp
  | ConstructRef sp -> mkConstruct sp
  | IndRef sp -> mkInd sp

let constr_of_reference = constr_of_global
let reference_of_constr = global_of_constr

let global_ord_gen fc fmi x y =
  let ind_ord (indx,ix) (indy,iy) =
    let c = Pervasives.compare ix iy in
    if c = 0 then kn_ord (fmi indx) (fmi indy) else c
  in
  match x, y with
    | ConstRef cx, ConstRef cy -> kn_ord (fc cx) (fc cy)
    | IndRef indx, IndRef indy -> ind_ord indx indy
    | ConstructRef (indx,jx), ConstructRef (indy,jy) ->
      let c = Pervasives.compare jx jy in
      if c = 0 then ind_ord indx indy else c
    | _, _ -> Pervasives.compare x y

let global_ord_can = global_ord_gen canonical_con canonical_mind
let global_ord_user = global_ord_gen user_con user_mind

(* By default, [global_reference] are ordered on their canonical part *)

module RefOrdered = struct
  type t = global_reference
  let compare = global_ord_can
end

module RefOrdered_env = struct
  type t = global_reference
  let compare = global_ord_user
end

module Refset = Set.Make(RefOrdered)
module Refmap = Map.Make(RefOrdered)

(* Extended global references *)

type syndef_name = kernel_name

type extended_global_reference =
  | TrueGlobal of global_reference
  | SynDef of syndef_name

(* We order [extended_global_reference] via their user part
   (cf. pretty printer) *)

module ExtRefOrdered = struct
  type t = extended_global_reference
  let compare x y =
    match x, y with
      | TrueGlobal rx, TrueGlobal ry -> global_ord_user rx ry
      | SynDef knx, SynDef kny -> kn_ord knx kny
      | _, _ -> Pervasives.compare x y
end

(** {6 Temporary function to brutally form kernel names from section paths } *)

let encode_mind dir id = make_mind (MPfile dir) empty_dirpath (label_of_id id)

let encode_con dir id = make_con (MPfile dir) empty_dirpath (label_of_id id)

let decode_mind kn =
  let rec dir_of_mp = function
    | MPfile dir -> repr_dirpath dir
    | MPbound mbid ->
	let _,_,dp = repr_mbid mbid in
	let id = id_of_mbid mbid in
	  id::(repr_dirpath dp)
    | MPdot(mp,l) -> (id_of_label l)::(dir_of_mp mp)
  in
  let mp,sec_dir,l = repr_mind kn in
    if (repr_dirpath sec_dir) = [] then
     (make_dirpath (dir_of_mp mp)),id_of_label l
    else
      anomaly "Section part should be empty!"

let decode_con kn =
  let mp,sec_dir,l = repr_con kn in
    match mp,(repr_dirpath sec_dir) with
	MPfile dir,[] -> (dir,id_of_label l)
      | _ , [] -> anomaly "MPfile expected!"
      | _ -> anomaly "Section part should be empty!"

(* popping one level of section in global names *)

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
  | VarRef id -> anomaly "VarRef not poppable"
