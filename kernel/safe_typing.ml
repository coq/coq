(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Util
open Names
open Univ
open Term
open Reduction
open Sign
open Declarations
open Inductive
open Environ
open Type_errors
open Indtypes

type judgment = unsafe_judgment
let j_val = j_val
let j_type = j_type

(* Exported machines. *)

let safe_infer = Typeops.infer
let safe_infer_type = Typeops.infer_type

(*s Safe environments. *)

type safe_environment = env

let empty_environment = empty_env

(* Insertion of variables (named and de Bruijn'ed). They are now typed before
   being added to the environment. *)

let push_rel_or_named_def push (id,b) env =
  let (j,cst) = safe_infer env b in
  let env' = add_constraints cst env in
  let env'' = push (id,Some j.uj_val,j.uj_type) env' in
  (cst,env'')

let push_named_def = push_rel_or_named_def push_named_decl
let push_rel_def = push_rel_or_named_def push_rel

let push_rel_or_named_assum push (id,t) env =
  let (j,cst) = safe_infer env t in
  let t = Typeops.assumption_of_judgment env j in
  let env' = add_constraints cst env in
  let env'' = push (id,None,t) env' in
  (cst,env'')

let push_named_assum = push_rel_or_named_assum push_named_decl
let push_rel_assum d env = snd (push_rel_or_named_assum push_rel d env)

let push_rels_with_univ vars env =
  List.fold_left (fun env nvar -> push_rel_assum nvar env) env vars

(* Insertion of constants and parameters in environment. *)
type global_declaration = Def of constr * bool | Assum of constr

(* Definition always declared transparent *)
let safe_infer_declaration env dcl =
  match dcl with
  | Def (c,op) ->
      let (j,cst) = safe_infer env c in
      Some j.uj_val, j.uj_type, cst, op
  | Assum t ->
      let (j,cst) = safe_infer env t in
      None, Typeops.assumption_of_judgment env j, cst, false

let add_global_declaration sp env (body,typ,cst,op) =
  let env' = add_constraints cst env in
  let ids = match body with 
    | None -> global_vars_set env typ
    | Some b ->
        Idset.union (global_vars_set env b) (global_vars_set env typ) in
  let hyps = keep_hyps env ids in
  let cb = {
    const_body = body;
    const_type = typ;
    const_hyps = hyps;
    const_constraints = cst;
    const_opaque = op } in
  Environ.add_constant sp cb env'

let add_parameter sp t env =
  add_global_declaration sp env (safe_infer_declaration env (Assum t))

(*s Global and local constant declaration. *)

type constant_entry = {
  const_entry_body   : constr;
  const_entry_type   : types option;
  const_entry_opaque : bool }

let add_constant sp ce env =
  let body =
    match ce.const_entry_type with
      | None -> ce.const_entry_body
      | Some ty -> mkCast (ce.const_entry_body, ty) in
  add_global_declaration sp env
    (safe_infer_declaration env (Def (body, ce.const_entry_opaque)))

let add_discharged_constant sp r env =
  let (body,typ,cst,op) = Cooking.cook_constant env r in
  match body with
    | None -> 
	add_parameter sp typ (* Bricolage avant poubelle *) env
    | Some c -> 
	(* let c = hcons1_constr c in *)
	let ids = 
	  Idset.union (global_vars_set env c) 
	    (global_vars_set env (body_of_type typ))
	in
	let hyps = keep_hyps env ids in
	let env' = Environ.add_constraints cst env in
	let cb =
	  { const_body = Some c;
	    const_type = typ;
	    const_hyps = hyps;
	    const_constraints = cst;
	    const_opaque = op } in
	Environ.add_constant sp cb env'


(* Insertion of inductive types. *)

let add_mind sp mie env =
  let mib = check_inductive env mie in
  let cst = mib.mind_constraints in
  Environ.add_mind sp mib (add_constraints cst env)

let add_constraints = Environ.add_constraints

let rec pop_named_decls idl env =
  match idl with 
    | [] -> env
    | id::l -> pop_named_decls l (Environ.pop_named_decl id env)

let export = export
let import = import

let env_of_safe_env e = e

(* Exported typing functions *)

let typing env c = 
  let (j,cst) = safe_infer env c in
  let _ = add_constraints cst env in
  j
