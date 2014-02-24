(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Created by Jean-Christophe Filliâtre out of V6.3 file constants.ml
   as part of the rebuilding of Coq around a purely functional
   abstract type-checker, Nov 1999 *)

(* This module implements kernel-level discharching of local
   declarations over global constants and inductive types *)

open Errors
open Util
open Names
open Term
open Context
open Declarations
open Environ

(*s Cooking the constants. *)

let pop_dirpath p = match DirPath.repr p with
  | [] -> anomaly ~label:"dirpath_prefix" (Pp.str "empty dirpath")
  | _::l -> DirPath.make l

let pop_mind kn =
  let (mp,dir,l) = Names.repr_mind kn in
  Names.make_mind mp (pop_dirpath dir) l

let pop_con con =
  let (mp,dir,l) = Names.repr_con con in
  Names.make_con mp (pop_dirpath dir) l

type my_global_reference =
  | ConstRef of constant
  | IndRef of inductive
  | ConstructRef of constructor

let share cache r (cstl,knl) =
  try Hashtbl.find cache r
  with Not_found ->
  let f,l =
    match r with
    | IndRef (kn,i) ->
	mkInd (pop_mind kn,i), Mindmap.find kn knl
    | ConstructRef ((kn,i),j) ->
	mkConstruct ((pop_mind kn,i),j), Mindmap.find kn knl
    | ConstRef cst ->
	mkConst (pop_con cst), Cmap.find cst cstl in
  let c = mkApp (f, Array.map mkVar l) in
  Hashtbl.add cache r c;
  c

let update_case_info cache ci modlist =
  try
    let ind, n =
      match kind_of_term (share cache (IndRef ci.ci_ind) modlist) with
      | App (f,l) -> (destInd f, Array.length l)
      | Ind ind -> ind, 0
      | _ -> assert false in
    { ci with ci_ind = ind; ci_npar = ci.ci_npar + n }
  with Not_found ->
    ci

let empty_modlist = (Cmap.empty, Mindmap.empty)

let is_empty_modlist (cm, mm) =
  Cmap.is_empty cm && Mindmap.is_empty mm

let expmod_constr cache modlist c =
  let share = share cache in
  let update_case_info = update_case_info cache in
  let rec substrec c =
    match kind_of_term c with
      | Case (ci,p,t,br) ->
	  map_constr substrec (mkCase (update_case_info ci modlist,p,t,br))

      | Ind ind ->
	  (try
	    share (IndRef ind) modlist
	   with
	    | Not_found -> map_constr substrec c)

      | Construct cstr ->
	  (try
	    share (ConstructRef cstr) modlist
	   with
	    | Not_found -> map_constr substrec c)

      | Const cst ->
	  (try
	    share (ConstRef cst) modlist
	   with
	    | Not_found -> map_constr substrec c)

  | _ -> map_constr substrec c

  in
  if is_empty_modlist modlist then c
  else substrec c

let abstract_constant_type =
   List.fold_left (fun c d -> mkNamedProd_wo_LetIn d c)

let abstract_constant_body =
  List.fold_left (fun c d -> mkNamedLambda_or_LetIn d c)

type recipe = { from : constant_body; info : Opaqueproof.cooking_info }
type inline = bool

type result =
  constant_def * constant_type * Univ.constraints * inline
    * Context.section_context option

let on_body ml hy f = function
  | Undef _ as x -> x
  | Def cs -> Def (Mod_subst.from_val (f (Mod_subst.force_constr cs)))
  | OpaqueDef o ->
    OpaqueDef (Opaqueproof.discharge_direct_opaque ~cook_constr:f
                 { Opaqueproof.modlist = ml; abstract = hy } o)

let constr_of_def = function
  | Undef _ -> assert false
  | Def cs -> Mod_subst.force_constr cs
  | OpaqueDef lc -> Opaqueproof.force_proof lc

let cook_constr { Opaqueproof.modlist ; abstract } c =
  let cache = Hashtbl.create 13 in
  let hyps = Context.map_named_context (expmod_constr cache modlist) abstract in
  abstract_constant_body (expmod_constr cache modlist c) hyps

let cook_constant env { from = cb; info = { Opaqueproof.modlist; abstract } } =
  let cache = Hashtbl.create 13 in
  let hyps = Context.map_named_context (expmod_constr cache modlist) abstract in
  let body = on_body modlist hyps
    (fun c -> abstract_constant_body (expmod_constr cache modlist c) hyps)
    cb.const_body
  in
  let const_hyps =
    Context.fold_named_context (fun (h,_,_) hyps ->
      List.filter (fun (id,_,_) -> not (Id.equal id h)) hyps)
      hyps ~init:cb.const_hyps in
  let typ = match cb.const_type with
    | NonPolymorphicType t ->
	let typ =
          abstract_constant_type (expmod_constr cache modlist t) hyps in
	NonPolymorphicType typ
    | PolymorphicArity (ctx,s) ->
	let t = mkArity (ctx,Type s.poly_level) in
	let typ =
          abstract_constant_type (expmod_constr cache modlist t) hyps in
	let j = make_judge (constr_of_def body) typ in
	Typeops.make_polymorphic_if_constant_for_ind env j
  in
  (body, typ, cb.const_constraints, cb.const_inline_code, Some const_hyps)

let expmod_constr modlist c = expmod_constr (Hashtbl.create 13) modlist c
