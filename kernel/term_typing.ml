(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

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
open Entries
open Type_errors
open Indtypes
open Typeops

let constrain_type env j cst1 = function
  | None ->
(* To have definitions in Type polymorphic
      make_polymorphic_if_arity env j.uj_type, cst1
*) 
      NonPolymorphicType j.uj_type, cst1
  | Some t -> 
      let (tj,cst2) = infer_type env t in
      let (_,cst3) = judge_of_cast env j DEFAULTcast tj in
      assert (t = tj.utj_val);
      NonPolymorphicType t, Constraint.union (Constraint.union cst1 cst2) cst3

let local_constrain_type env j cst1 = function
  | None ->
      j.uj_type, cst1
  | Some t -> 
      let (tj,cst2) = infer_type env t in
      let (_,cst3) = judge_of_cast env j DEFAULTcast tj in
      assert (t = tj.utj_val);
      t, Constraint.union (Constraint.union cst1 cst2) cst3

let translate_local_def env (b,topt) =
  let (j,cst) = infer env b in
  let (typ,cst) = local_constrain_type env j cst topt in
    (j.uj_val,typ,cst)

let translate_local_assum env t =
  let (j,cst) = infer env t in
  let t = Typeops.assumption_of_judgment env j in
    (t,cst)

(*

(* Same as push_named, but check that the variable is not already
   there. Should *not* be done in Environ because tactics add temporary
   hypothesis many many times, and the check performed here would
   cost too much. *)
let safe_push_named (id,_,_ as d) env =
  let _ =
    try
      let _ = lookup_named id env in 
      error ("identifier "^string_of_id id^" already defined")
    with Not_found -> () in
  push_named d env

let push_named_def = push_rel_or_named_def safe_push_named
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
*)


(* Insertion of constants and parameters in environment. *)

let infer_declaration env dcl =
  match dcl with
  | DefinitionEntry c ->
      let (j,cst) = infer env c.const_entry_body in
      let (typ,cst) = constrain_type env j cst c.const_entry_type in
      Some (Declarations.from_val j.uj_val), typ, cst,
        c.const_entry_opaque, c.const_entry_boxed
  | ParameterEntry t ->
      let (j,cst) = infer env t in
      None, NonPolymorphicType (Typeops.assumption_of_judgment env j), cst,
        false, false

let global_vars_set_constant_type env = function
  | NonPolymorphicType t -> global_vars_set env t
  | PolymorphicArity (ctx,_) ->
      Sign.fold_rel_context 
        (fold_rel_declaration
	  (fun t c -> Idset.union (global_vars_set env t) c))
      ctx ~init:Idset.empty

let build_constant_declaration env kn (body,typ,cst,op,boxed) =
  let ids =
    match body with 
    | None -> global_vars_set_constant_type env typ
    | Some b ->
        Idset.union 
	  (global_vars_set env (Declarations.force b)) 
	  (global_vars_set_constant_type env typ)
  in
  let tps = Cemitcodes.from_val (compile_constant_body env body op boxed) in
  let hyps = keep_hyps env ids in
    { const_hyps = hyps;
      const_body = body;
      const_type = typ;
      const_body_code = tps;
     (* const_type_code = to_patch env typ;*)
      const_constraints = cst;
      const_opaque = op }

(*s Global and local constant declaration. *)

let translate_constant env kn ce =
  build_constant_declaration env kn (infer_declaration env ce)

let translate_recipe env kn r = 
  build_constant_declaration env kn (Cooking.cook_constant env r)

(* Insertion of inductive types. *)

let translate_mind env mie = check_inductive env mie 
