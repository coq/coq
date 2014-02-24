(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Created by Jacek Chrzaszcz, Aug 2002 as part of the implementation of
   the Coq module system *)

(* This module provides the main entry points for type-checking basic
   declarations *)

open Errors
open Util
open Names
open Univ
open Term
open Context
open Declarations
open Environ
open Entries
open Typeops

let debug = false
let prerr_endline =
  if debug then prerr_endline else fun _ -> ()

let constrain_type env j cst1 = function
  | `None ->
      make_polymorphic_if_constant_for_ind env j, cst1
  | `Some t ->
      let (tj,cst2) = infer_type env t in
      let (_,cst3) = judge_of_cast env j DEFAULTcast tj in
      assert (eq_constr t tj.utj_val);
      let cstrs = union_constraints (union_constraints cst1 cst2) cst3 in
      NonPolymorphicType t, cstrs
  | `SomeWJ (t, tj, cst2) ->
      let (_,cst3) = judge_of_cast env j DEFAULTcast tj in
      assert (eq_constr t tj.utj_val);
      let cstrs = union_constraints (union_constraints cst1 cst2) cst3 in
      NonPolymorphicType t, cstrs

let map_option_typ = function None -> `None | Some x -> `Some x

let translate_local_assum env t =
  let (j,cst) = infer env t in
  let t = Typeops.assumption_of_judgment env j in
    (t,cst)


(* Insertion of constants and parameters in environment. *)

let handle_side_effects env body side_eff =
  let handle_sideff t se =
    let cbl = match se with
      | SEsubproof (c,cb) -> [c,cb]
      | SEscheme (cl,_) -> List.map (fun (_,c,cb) -> c,cb) cl in
    let cname c = 
      let name = string_of_con c in
      for i = 0 to String.length name - 1 do
        if name.[i] == '.' || name.[i] == '#' then name.[i] <- '_' done;
      Name (id_of_string name) in
    let rec sub c i x = match kind_of_term x with
      | Const c' when eq_constant c c' -> mkRel i
      | _ -> map_constr_with_binders ((+) 1) (fun i x -> sub c i x) i x in
    let fix_body (c,cb) t =
      match cb.const_body with
      | Undef _ -> assert false
      | Def b ->
          let b = Mod_subst.force_constr b in
          let b_ty = Typeops.type_of_constant_type env cb.const_type in
          let t = sub c 1 (Vars.lift 1 t) in
          mkLetIn (cname c, b, b_ty, t)
      | OpaqueDef b -> 
          let b = Opaqueproof.force_proof b in
          let b_ty = Typeops.type_of_constant_type env cb.const_type in
          let t = sub c 1 (Vars.lift 1 t) in
          mkApp (mkLambda (cname c, b_ty, t), [|b|]) in
    List.fold_right fix_body cbl t
  in
  (* CAVEAT: we assure a proper order *)
  Declareops.fold_side_effects handle_sideff body
    (Declareops.uniquize_side_effects side_eff)

let hcons_j j =
  { uj_val = hcons_constr j.uj_val; uj_type = hcons_constr j.uj_type} 

let feedback_completion_typecheck =
  Option.iter (fun state_id -> Pp.feedback ~state_id Interface.Complete)
  
let infer_declaration env dcl =
  match dcl with
  | ParameterEntry (ctx,t,nl) ->
      let j, cst = infer env t in
      let t = hcons_constr (Typeops.assumption_of_judgment env j) in
      Undef nl, NonPolymorphicType t, cst, false, ctx
  | DefinitionEntry ({ const_entry_type = Some typ;
                       const_entry_opaque = true } as c) ->
      let { const_entry_body = body; const_entry_feedback = feedback_id } = c in
      let tyj, tycst = infer_type env typ in
      let proofterm =
        Future.chain ~greedy:true ~pure:true body (fun (body, side_eff) ->
          let body = handle_side_effects env body side_eff in
          let j, cst = infer env body in
          let j = hcons_j j in
          let _typ, cst = constrain_type env j cst (`SomeWJ (typ,tyj,tycst)) in
          feedback_completion_typecheck feedback_id;
          j.uj_val, cst) in
      let def = OpaqueDef (Opaqueproof.create proofterm) in
      let typ = NonPolymorphicType typ in
      def, typ, tycst, c.const_entry_inline_code, c.const_entry_secctx
  | DefinitionEntry c ->
      let { const_entry_type = typ; const_entry_opaque = opaque } = c in
      let { const_entry_body = body; const_entry_feedback = feedback_id } = c in
      let body, side_eff = Future.join body in
      let body = handle_side_effects env body side_eff in
      let j, cst = infer env body in
      let j = hcons_j j in
      let typ, cst = constrain_type env j cst (map_option_typ typ) in
      feedback_completion_typecheck feedback_id;
      let def = Def (Mod_subst.from_val j.uj_val) in
      def, typ, cst, c.const_entry_inline_code, c.const_entry_secctx

let global_vars_set_constant_type env = function
  | NonPolymorphicType t -> global_vars_set env t
  | PolymorphicArity (ctx,_) ->
      Context.fold_rel_context
        (fold_rel_declaration
	  (fun t c -> Id.Set.union (global_vars_set env t) c))
      ctx ~init:Id.Set.empty

let record_aux env s1 s2 =
  let v =
    String.concat " "
      (List.map (fun (id, _,_) -> Id.to_string id)
        (keep_hyps env (Id.Set.union s1 s2))) in
  Aux_file.record_in_aux "context_used" v

let suggest_proof_using = ref (fun _ _ _ _ _ -> ())
let set_suggest_proof_using f = suggest_proof_using := f

let build_constant_declaration kn env (def,typ,cst,inline_code,ctx) =
  let check declared inferred =
    let mk_set l = List.fold_right Id.Set.add (List.map pi1 l) Id.Set.empty in
    let inferred_set, declared_set = mk_set inferred, mk_set declared in
    if not (Id.Set.subset inferred_set declared_set) then
      error ("The following section variable are used but not declared:\n"^
        (String.concat ", " (List.map Id.to_string
          (Id.Set.elements (Idset.diff inferred_set declared_set))))) in
  (* We try to postpone the computation of used section variables *)
  let hyps, def =
    let context_ids = List.map pi1 (named_context env) in
    match ctx with
    | None when not (List.is_empty context_ids) -> 
        (* No declared section vars, and non-empty section context:
           we must look at the body NOW, if any *)
        let ids_typ = global_vars_set_constant_type env typ in
        let ids_def = match def with
        | Undef _ -> Idset.empty
        | Def cs -> global_vars_set env (Mod_subst.force_constr cs)
        | OpaqueDef lc ->
            let vars = global_vars_set env (Opaqueproof.force_proof lc) in
            !suggest_proof_using kn env vars ids_typ context_ids;
            if !Flags.compilation_mode = Flags.BuildVo then
              record_aux env ids_typ vars;
            vars
        in
        keep_hyps env (Idset.union ids_typ ids_def), def
    | None ->
        if !Flags.compilation_mode = Flags.BuildVo then
          record_aux env Id.Set.empty Id.Set.empty;
        [], def (* Empty section context: no need to check *)
    | Some declared ->
        (* We use the declared set and chain a check of correctness *)
        declared,
        match def with
        | Undef _ as x -> x (* nothing to check *)
        | Def cs as x ->
            let ids_typ = global_vars_set_constant_type env typ in
            let ids_def = global_vars_set env (Mod_subst.force_constr cs) in
            let inferred = keep_hyps env (Idset.union ids_typ ids_def) in
            check declared inferred;
            x
        | OpaqueDef lc -> (* In this case we can postpone the check *)
            OpaqueDef (Opaqueproof.iter_direct_opaque (fun c ->
              let ids_typ = global_vars_set_constant_type env typ in
              let ids_def = global_vars_set env c in
              let inferred = keep_hyps env (Idset.union ids_typ ids_def) in
              check declared inferred) lc) in
  { const_hyps = hyps;
    const_body = def;
    const_type = typ;
    const_body_code = Cemitcodes.from_val (compile_constant_body env def);
    const_constraints = cst;
    const_inline_code = inline_code }

(*s Global and local constant declaration. *)

let translate_constant env kn ce =
  build_constant_declaration kn env (infer_declaration env ce)

let translate_recipe env kn r =
  let def,typ,cst,inline_code,hyps = Cooking.cook_constant env r in
  build_constant_declaration kn env (def,typ,cst,inline_code,hyps)

let translate_local_def env id centry =
  let def,typ,cst,inline_code,ctx =
    infer_declaration env (DefinitionEntry centry) in
  let typ = type_of_constant_type env typ in
  def, typ, cst

(* Insertion of inductive types. *)

let translate_mind env kn mie = Indtypes.check_inductive env kn mie

let handle_side_effects env ce = { ce with
  const_entry_body = Future.chain ~greedy:true ~pure:true
    ce.const_entry_body (fun (body, side_eff) ->
       handle_side_effects env body side_eff, Declareops.no_seff);
}
