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

let constrain_type env j cst1 = function
  | None -> j.uj_type, cst1
  | Some t -> 
      let (tj,cst2) = safe_infer_type env t in
      let cst3 =
	try conv_leq env j.uj_type tj.utj_val
	with NotConvertible -> error_actual_type env j tj.utj_val in
      tj.utj_val, Constraint.union (Constraint.union cst1 cst2) cst3

let push_rel_or_named_def push (id,b,topt) env =
  let (j,cst) = safe_infer env b in
  let (typ,cst) = constrain_type env j cst topt in
  let env' = add_constraints cst env in
  let env'' = push (id,Some j.uj_val,typ) env' in
  (cst,env'')

let push_named_def = push_rel_or_named_def push_named
let push_rel_def = push_rel_or_named_def push_rel

let push_rel_or_named_assum push (id,t) env =
  let (j,cst) = safe_infer env t in
  let t = Typeops.assumption_of_judgment env j in
  let env' = add_constraints cst env in
  let env'' = push (id,None,t) env' in
  (cst,env'')

let push_named_assum = push_rel_or_named_assum push_named
let push_rel_assum d env = snd (push_rel_or_named_assum push_rel d env)

let push_rels_with_univ vars env =
  List.fold_left (fun env nvar -> push_rel_assum nvar env) env vars

(* Insertion of constants and parameters in environment. *)
type constant_entry = {
  const_entry_body   : constr;
  const_entry_type   : types option;
  const_entry_opaque : bool }

type global_declaration = 
  | ConstantEntry of constant_entry
  | ParameterEntry of types
  | GlobalRecipe of Cooking.recipe

(* Definition always declared transparent *)
let safe_infer_declaration env dcl =
  match dcl with
  | ConstantEntry c ->
      let (j,cst) = safe_infer env c.const_entry_body in
      let (typ,cst) = constrain_type env j cst c.const_entry_type in
      Some j.uj_val, typ, cst, c.const_entry_opaque
  | ParameterEntry t ->
      let (j,cst) = safe_infer env t in
      None, Typeops.assumption_of_judgment env j, cst, false
  | GlobalRecipe r ->
      Cooking.cook_constant env r

let add_global_declaration kn env (body,typ,cst,op) =
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
  Environ.add_constant kn cb env'

(*s Global and local constant declaration. *)

let add_constant kn ce env =
  add_global_declaration kn env (safe_infer_declaration env ce)

(* Insertion of inductive types. *)

let add_mind kn mie env =
  let mib = check_inductive env mie in
  let cst = mib.mind_constraints in
  Environ.add_mind kn mib (add_constraints cst env)

let add_constraints = Environ.add_constraints

let export = export
let import = import

let env_of_safe_env e = e

(* Exported typing functions *)

let typing env c = 
  let (j,cst) = safe_infer env c in
  let _ = add_constraints cst env in
  j
