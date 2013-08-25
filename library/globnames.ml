(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
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
  match gr1,gr2 with
    | ConstRef con1, ConstRef con2 -> eq_constant con1 con2
    | IndRef kn1, IndRef kn2 -> eq_ind kn1 kn2
    | ConstructRef kn1, ConstructRef kn2 -> eq_constructor kn1 kn2
    | VarRef v1, VarRef v2 -> Id.equal v1 v2
    | _ -> false

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

let global_ord_gen ord_cst ord_ind ord_cons x y = match x, y with
  | ConstRef cx, ConstRef cy -> ord_cst cx cy
  | IndRef indx, IndRef indy -> ord_ind indx indy
  | ConstructRef consx, ConstructRef consy -> ord_cons consx consy
  | VarRef v1, VarRef v2 -> Id.compare v1 v2
  | _, _ -> Pervasives.compare x y

let global_ord_can =
  global_ord_gen con_ord ind_ord constructor_ord
let global_ord_user =
  global_ord_gen con_user_ord ind_user_ord constructor_user_ord

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

(* Alternative sets and maps indexed by the user part of the kernel names *)

module Refset_env = Set.Make(RefOrdered_env)
module Refmap_env = Map.Make(RefOrdered_env)

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

type global_reference_or_constr = 
  | IsGlobal of global_reference
  | IsConstr of constr

let constr_of_global_or_constr = function
  | IsConstr c -> c
  | IsGlobal gr -> constr_of_global gr

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
