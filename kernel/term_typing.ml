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
open Fast_typeops

let debug = true
let prerr_endline =
  if debug then prerr_endline else fun _ -> ()

let constrain_type env j poly = function
  | `None -> 
    if not poly then (* Old-style polymorphism *)
      make_polymorphic_if_constant_for_ind env j
    else RegularArity j.uj_type
  | `Some t ->
      let tj = infer_type env t in
      let _ = judge_of_cast env j DEFAULTcast tj in
	assert (eq_constr t tj.utj_val);
	RegularArity t
  | `SomeWJ (t, tj) ->
      let tj = infer_type env t in
      let _ = judge_of_cast env j DEFAULTcast tj in
	assert (eq_constr t tj.utj_val);
	RegularArity t

let map_option_typ = function None -> `None | Some x -> `Some x

let local_constrain_type env j = function
  | None ->
      j.uj_type
  | Some t ->
      let tj = infer_type env t in
      let _ = judge_of_cast env j DEFAULTcast tj in
      assert (eq_constr t tj.utj_val);
      t

(* Insertion of constants and parameters in environment. *)

let mk_pure_proof c = (c, Univ.ContextSet.empty), Declareops.no_seff

let handle_side_effects env body side_eff =
  let handle_sideff t se =
    let cbl = match se with
      | SEsubproof (c,cb) -> [c,cb]
      | SEscheme (cl,_) -> List.map (fun (_,c,cb) -> c,cb) cl in
    let not_exists (c,_) =
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
	let subst = 
	  Array.fold_left2 (fun subst l l' -> Univ.LMap.add l l' subst)
	    Univ.LMap.empty (Instance.to_array u) (Instance.to_array u')
	in 
	  Vars.subst_univs_level_constr subst b
      | _ -> map_constr_with_binders ((+) 1) (fun i x -> sub_body c u b i x) i x in
    let fix_body (c,cb) t =
      match cb.const_body with
      | Undef _ -> assert false
      | Def b ->
          let b = Mod_subst.force_constr b in
	  let poly = cb.const_polymorphic in
	    if not poly then
              let b_ty = Typeops.type_of_constant_type env cb.const_type in
              let t = sub c 1 (Vars.lift 1 t) in
		mkLetIn (cname c, b, b_ty, t)
	    else 
	      let univs = cb.const_universes in
		sub_body c (Univ.UContext.instance univs) b 1 (Vars.lift 1 t)
      | OpaqueDef b -> 
          let b = Opaqueproof.force_proof b in
	  let poly = cb.const_polymorphic in
	    if not poly then
              let b_ty = Typeops.type_of_constant_type env cb.const_type in
              let t = sub c 1 (Vars.lift 1 t) in
		mkApp (mkLambda (cname c, b_ty, t), [|b|]) 
	    else
	      let univs = cb.const_universes in
		sub_body c (Univ.UContext.instance univs) b 1 (Vars.lift 1 t)
    in
      List.fold_right fix_body cbl t
  in
  (* CAVEAT: we assure a proper order *)
  Declareops.fold_side_effects handle_sideff body
    (Declareops.uniquize_side_effects side_eff)

let hcons_j j =
  { uj_val = hcons_constr j.uj_val; uj_type = hcons_constr j.uj_type} 

let feedback_completion_typecheck =
  Option.iter (fun state_id -> Pp.feedback ~state_id Interface.Complete)

let check_projection env kn inst body =
  let cannot_recognize () = error ("Cannot recognize a projection") in
  let ctx, m = decompose_lam_assum body in
  let () = if not (isCase m) then cannot_recognize () in
  let ci, p, c, b = destCase m in
  let (mib, oib as specif) = Inductive.lookup_mind_specif env ci.ci_ind in
  let recinfo = match mib.mind_record with
    | None -> 
      error ("Trying to declare a primitive projection for a non-record inductive type")
    | Some (_, r) -> r
  in
  let n = mib.mind_nparams in
  let () = 
    if n + 1 != List.length ctx ||
      not (isRel c) || destRel c != 1 || Array.length b != 1 ||
      not (isLambda p)
    then cannot_recognize ()
  in
  let (na, t, ty) = destLambda p in 
  let argctx, p = decompose_lam_assum b.(0) in
  (* No need to check the lambdas as the case is well-formed *)
  let () = if not (isRel p) then cannot_recognize () in
  let arg = destRel p - 1 in
  let () = if not (arg < Array.length recinfo) then cannot_recognize () in
  let () = if not (eq_con_chk recinfo.(Array.length recinfo - (arg + 1)) kn) then cannot_recognize () in
  let pb = { proj_ind = fst ci.ci_ind;
	     proj_npars = n;
	     proj_arg = arg;
	     proj_type = ty;
	     proj_body = body }
  in pb
  
let infer_declaration env kn dcl =
  match dcl with
  | ParameterEntry (ctx,poly,(t,uctx),nl) ->
      let env = push_context uctx env in
      let j = infer env t in
      let t = hcons_constr (Typeops.assumption_of_judgment env j) in
      Undef nl, RegularArity t, None, poly, uctx, false, ctx
  | DefinitionEntry ({ const_entry_type = Some typ;
                       const_entry_opaque = true } as c) ->
      let env = push_context c.const_entry_universes env in
      let { const_entry_body = body; const_entry_feedback = feedback_id } = c in
      let tyj = infer_type env typ in
      let proofterm =
        Future.chain ~greedy:true ~pure:true body (fun ((body, ctx), side_eff) ->
          let body = handle_side_effects env body side_eff in
	  let env' = push_context_set ctx env in
          let j = infer env' body in
          let j = hcons_j j in
          let _typ = constrain_type env' j c.const_entry_polymorphic (`SomeWJ (typ,tyj)) in
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
      let def, typ, proj = 
	if c.const_entry_proj then
	  (** This should be the projection defined as a match. *)
	  let j = infer env body in
	  let typ = constrain_type env j c.const_entry_polymorphic (map_option_typ typ) in
	  (** We check it does indeed have the shape of a projection. *)
	  let inst = Univ.UContext.instance c.const_entry_universes in
	  let pb = check_projection env (Option.get kn) inst body in
	  (** We build the eta-expanded form. *)
	  let context, m = decompose_lam_n_assum (pb.proj_npars + 1) body in 
	  let body' = mkProj (Option.get kn, mkRel 1) in
	  let body = it_mkLambda_or_LetIn body' context in
	    Def (Mod_subst.from_val (hcons_constr body)),
	    typ, Some pb
	else
	  let j = infer env body in
	  let j = hcons_j j in
	  let typ = constrain_type env j c.const_entry_polymorphic (map_option_typ typ) in
	  let def = Def (Mod_subst.from_val j.uj_val) in
	    def, typ, None
      in
      let univs = c.const_entry_universes in
	feedback_completion_typecheck feedback_id;
	def, typ, proj, c.const_entry_polymorphic,
        univs, c.const_entry_inline_code, c.const_entry_secctx

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
            (* we force so that cst are added to the env immediately after *)
            ignore(Opaqueproof.force_constraints lc);
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

let handle_side_effects env ce = { ce with
  const_entry_body = Future.chain ~greedy:true ~pure:true
    ce.const_entry_body (fun ((body, ctx), side_eff) ->
      (handle_side_effects env body side_eff, ctx), Declareops.no_seff);
}
