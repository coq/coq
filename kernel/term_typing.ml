(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
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
open Fast_typeops

let constrain_type env j poly subst = function
  | `None -> 
    if not poly then (* Old-style polymorphism *)
      make_polymorphic_if_constant_for_ind env j
    else RegularArity (Vars.subst_univs_level_constr subst j.uj_type)
  | `Some t ->
      let tj = infer_type env t in
      let _ = judge_of_cast env j DEFAULTcast tj in
	assert (eq_constr t tj.utj_val);
	RegularArity (Vars.subst_univs_level_constr subst t)
  | `SomeWJ (t, tj) ->
      let tj = infer_type env t in
      let _ = judge_of_cast env j DEFAULTcast tj in
	assert (eq_constr t tj.utj_val);
	RegularArity (Vars.subst_univs_level_constr subst t)

let map_option_typ = function None -> `None | Some x -> `Some x

(* Insertion of constants and parameters in environment. *)

let mk_pure_proof c = (c, Univ.ContextSet.empty), Declareops.no_seff

let handle_side_effects env body side_eff =
  let handle_sideff t se =
    let cbl = match se with
      | SEsubproof (c,cb,b) -> [c,cb,b]
      | SEscheme (cl,_) -> List.map (fun (_,c,cb,b) -> c,cb,b) cl in
    let not_exists (c,_,_) =
      try ignore(Environ.lookup_constant c env); false
      with Not_found -> true in 
    let cbl = List.filter not_exists cbl in
    let cname c = 
      let name = string_of_con c in
      for i = 0 to String.length name - 1 do
        if name.[i] == '.' || name.[i] == '#' then name.[i] <- '_' done;
      Name (id_of_string name) in
    let rec sub c i x = match kind_of_term x with
      | Const (c', _) when eq_constant c c' -> mkRel i
      | _ -> map_constr_with_binders ((+) 1) (fun i x -> sub c i x) i x in
    let rec sub_body c u b i x = match kind_of_term x with
      | Const (c',u') when eq_constant c c' -> 
	Vars.subst_instance_constr u' b
      | _ -> map_constr_with_binders ((+) 1) (fun i x -> sub_body c u b i x) i x in
    let fix_body (c,cb,b) t =
      match cb.const_body, b with
      | Def b, _ ->
          let b = Mod_subst.force_constr b in
	  let poly = cb.const_polymorphic in
	    if not poly then
              let b_ty = Typeops.type_of_constant_type env cb.const_type in
              let t = sub c 1 (Vars.lift 1 t) in
		mkLetIn (cname c, b, b_ty, t)
	    else 
	      let univs = cb.const_universes in
		sub_body c (Univ.UContext.instance univs) b 1 (Vars.lift 1 t)
      | OpaqueDef _, `Opaque (b,_) -> 
	  let poly = cb.const_polymorphic in
	    if not poly then
              let b_ty = Typeops.type_of_constant_type env cb.const_type in
              let t = sub c 1 (Vars.lift 1 t) in
		mkApp (mkLambda (cname c, b_ty, t), [|b|]) 
	    else
	      let univs = cb.const_universes in
		sub_body c (Univ.UContext.instance univs) b 1 (Vars.lift 1 t)
      | _ -> assert false
    in
      List.fold_right fix_body cbl t
  in
  (* CAVEAT: we assure a proper order *)
  Declareops.fold_side_effects handle_sideff body
    (Declareops.uniquize_side_effects side_eff)

let hcons_j j =
  { uj_val = hcons_constr j.uj_val; uj_type = hcons_constr j.uj_type} 

let feedback_completion_typecheck =
  Option.iter (fun state_id -> Pp.feedback ~state_id Feedback.Complete)
  
let subst_instance_j s j =
  { uj_val = Vars.subst_univs_level_constr s j.uj_val;
    uj_type = Vars.subst_univs_level_constr s j.uj_type }

let infer_declaration env kn dcl =
  match dcl with
  | ParameterEntry (ctx,poly,(t,uctx),nl) ->
      let env = push_context uctx env in
      let j = infer env t in
      let abstract = poly && not (Option.is_empty kn) in
      let usubst, univs = Univ.abstract_universes abstract uctx in
      let c = Typeops.assumption_of_judgment env j in
      let t = hcons_constr (Vars.subst_univs_level_constr usubst c) in
	Undef nl, RegularArity t, None, poly, univs, false, ctx

  | DefinitionEntry ({ const_entry_type = Some typ;
                       const_entry_opaque = true;
		       const_entry_polymorphic = false} as c) ->
      let env = push_context c.const_entry_universes env in
      let { const_entry_body = body; const_entry_feedback = feedback_id } = c in
      let tyj = infer_type env typ in
      let proofterm =
        Future.chain ~greedy:true ~pure:true body (fun ((body, ctx),side_eff) ->
          let body = handle_side_effects env body side_eff in
	  let env' = push_context_set ctx env in
          let j = infer env' body in
          let j = hcons_j j in
	  let subst = Univ.LMap.empty in
          let _typ = constrain_type env' j c.const_entry_polymorphic subst
	    (`SomeWJ (typ,tyj)) in
          feedback_completion_typecheck feedback_id;
          j.uj_val, ctx) in
      let def = OpaqueDef (Opaqueproof.create proofterm) in
      def, RegularArity typ, None, c.const_entry_polymorphic, 
	c.const_entry_universes,
	c.const_entry_inline_code, c.const_entry_secctx

  | DefinitionEntry c ->
      let env = push_context c.const_entry_universes env in
      let { const_entry_type = typ; const_entry_opaque = opaque } = c in
      let { const_entry_body = body; const_entry_feedback = feedback_id } = c in
      let (body, ctx), side_eff = Future.join body in
      assert(Univ.ContextSet.is_empty ctx);
      let body = handle_side_effects env body side_eff in
      let abstract = c.const_entry_polymorphic && not (Option.is_empty kn) in
      let usubst, univs = Univ.abstract_universes abstract c.const_entry_universes in
      let j = infer env body in
      let typ = constrain_type env j c.const_entry_polymorphic usubst (map_option_typ typ) in
      let def = hcons_constr (Vars.subst_univs_level_constr usubst j.uj_val) in
      let def = 
	if opaque then OpaqueDef (Opaqueproof.create (Future.from_val (def, Univ.ContextSet.empty)))
	else Def (Mod_subst.from_val def) 
      in
	feedback_completion_typecheck feedback_id;
	def, typ, None, c.const_entry_polymorphic,
        univs, c.const_entry_inline_code, c.const_entry_secctx

  | ProjectionEntry {proj_entry_ind = ind; proj_entry_arg = i} ->
    let mib, _ = Inductive.lookup_mind_specif env (ind,0) in
    let kn, pb = 
      match mib.mind_record with
      | Some (Some (id, kns, pbs)) -> 
	if i < Array.length pbs then
	  kns.(i), pbs.(i)
	else assert false
      | _ -> assert false
    in
    let term, typ = pb.proj_eta in
      Def (Mod_subst.from_val (hcons_constr term)), RegularArity typ, Some pb,
      mib.mind_polymorphic, mib.mind_universes, false, None

let global_vars_set_constant_type env = function
  | RegularArity t -> global_vars_set env t
  | TemplateArity (ctx,_) ->
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

let build_constant_declaration kn env (def,typ,proj,poly,univs,inline_code,ctx) =
  let check declared inferred =
    let mk_set l = List.fold_right Id.Set.add (List.map pi1 l) Id.Set.empty in
    let inferred_set, declared_set = mk_set inferred, mk_set declared in
    if not (Id.Set.subset inferred_set declared_set) then
      let l = Id.Set.elements (Idset.diff inferred_set declared_set) in
      let n = List.length l in
      errorlabstrm "" (Pp.(str "The following section " ++
        str (String.plural n "variable") ++
        str " " ++ str (String.conjugate_verb_to_be n) ++
        str " used but not declared:" ++
        fnl () ++ pr_sequence Id.print (List.rev l) ++ str ".")) in
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
            let vars =
              global_vars_set env
                (Opaqueproof.force_proof (opaque_tables env) lc) in
            (* we force so that cst are added to the env immediately after *)
            ignore(Opaqueproof.force_constraints (opaque_tables env) lc);
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
  let tps = 
    (* FIXME: incompleteness of the bytecode vm: we compile polymorphic 
       constants like opaque definitions. *)
    if poly then Cemitcodes.from_val Cemitcodes.BCconstant
    else
      match proj with
      | None -> Cemitcodes.from_val (compile_constant_body env def)
      | Some pb ->
	Cemitcodes.from_val (compile_constant_body env (Def (Mod_subst.from_val pb.proj_body)))
  in
  { const_hyps = hyps;
    const_body = def;
    const_type = typ;
    const_proj = proj;
    const_body_code = tps;
    const_polymorphic = poly;
    const_universes = univs;
    const_inline_code = inline_code }


(*s Global and local constant declaration. *)

let translate_constant env kn ce =
  build_constant_declaration kn env (infer_declaration env (Some kn) ce)

let translate_local_assum env t =
  let j = infer env t in
  let t = Typeops.assumption_of_judgment env j in
    t

let translate_recipe env kn r =
  build_constant_declaration kn env (Cooking.cook_constant env r)

let translate_local_def env id centry =
  let def,typ,proj,poly,univs,inline_code,ctx =
    infer_declaration env None (DefinitionEntry centry) in
  let typ = type_of_constant_type env typ in
  def, typ, univs

(* Insertion of inductive types. *)

let translate_mind env kn mie = Indtypes.check_inductive env kn mie

let handle_entry_side_effects env ce = { ce with
  const_entry_body = Future.chain ~greedy:true ~pure:true
    ce.const_entry_body (fun ((body, ctx), side_eff) ->
      (handle_side_effects env body side_eff, ctx), Declareops.no_seff);
}
