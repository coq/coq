(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Created by Jacek Chrzaszcz, Aug 2002 as part of the implementation of
   the Coq module system *)

(* This module provides the main entry points for type-checking basic
   declarations *)

open CErrors
open Util
open Names
open Term
open Declarations
open Environ
open Entries
open Typeops
open Fast_typeops

(* Insertion of constants and parameters in environment. *)

let mk_pure_proof c = (c, Univ.ContextSet.empty), []

let equal_eff e1 e2 =
  let open Entries in
  match e1, e2 with
  | { eff = SEsubproof (c1,_,_) }, { eff = SEsubproof (c2,_,_) } ->
        Names.Constant.equal c1 c2
  | { eff = SEscheme (cl1,_) }, { eff = SEscheme (cl2,_) } ->
        CList.for_all2eq
          (fun (_,c1,_,_) (_,c2,_,_) -> Names.Constant.equal c1 c2)
          cl1 cl2
  | _ -> false

let rec uniq_seff = function
  | [] -> []
  | x :: xs -> x :: uniq_seff (List.filter (fun y -> not (equal_eff x y)) xs)
(* The list of side effects is in reverse order (most recent first).
 * To keep the "topological" order between effects we have to uniq-ize from
 * the tail *)
let uniq_seff l = List.rev (uniq_seff (List.rev l))

let inline_side_effects env body ctx side_eff =
  let handle_sideff (t,ctx,sl) { eff = se; from_env = mb } =
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
      | _ -> map_constr_with_binders ((+) 1) (sub_body c u b) i x in
    let fix_body (c,cb,b) (t,ctx) =
      match cb.const_body, b with
      | Def b, _ ->
          let b = Mod_subst.force_constr b in
	  let poly = cb.const_polymorphic in
	    if not poly then
              let b_ty = Typeops.type_of_constant_type env cb.const_type in
              let t = sub c 1 (Vars.lift 1 t) in
	        mkLetIn (cname c, b, b_ty, t),
		Univ.ContextSet.union ctx
		  (Univ.ContextSet.of_context cb.const_universes)
	    else 
	      let univs = cb.const_universes in
		sub_body c (Univ.UContext.instance univs) b 1 (Vars.lift 1 t), ctx
      | OpaqueDef _, `Opaque (b,_) -> 
	  let poly = cb.const_polymorphic in
	    if not poly then
              let b_ty = Typeops.type_of_constant_type env cb.const_type in
              let t = sub c 1 (Vars.lift 1 t) in
	        mkApp (mkLambda (cname c, b_ty, t), [|b|]),
		Univ.ContextSet.union ctx
		  (Univ.ContextSet.of_context cb.const_universes)
	    else
	      let univs = cb.const_universes in
		sub_body c (Univ.UContext.instance univs) b 1 (Vars.lift 1 t), ctx
      | _ -> assert false
    in
    let t, ctx = List.fold_right fix_body cbl (t,ctx) in
    t, ctx, (mb,List.length cbl) :: sl
  in
  (* CAVEAT: we assure a proper order *)
  List.fold_left handle_sideff (body,ctx,[]) (uniq_seff side_eff)

(* Given the list of signatures of side effects, checks if they match.
 * I.e. if they are ordered descendants of the current revstruct *)
let check_signatures curmb sl =
  let is_direct_ancestor (sl, curmb) (mb, how_many) =
    match curmb with
    | None -> None, None
    | Some curmb ->
        try
          let mb = CEphemeron.get mb in
          match sl with
          | None -> sl, None
          | Some n ->
              if List.length mb >= how_many && CList.skipn how_many mb == curmb
              then Some (n + how_many), Some mb
              else None, None
        with CEphemeron.InvalidKey -> None, None in
  let sl, _ = List.fold_left is_direct_ancestor (Some 0,Some curmb) sl in
  sl

let skip_trusted_seff sl b e =
  let rec aux sl b e acc =
    let open Context.Rel.Declaration in
    match sl, kind_of_term b with
    | (None|Some 0), _ -> b, e, acc
    | Some sl, LetIn (n,c,ty,bo) ->
       aux (Some (sl-1)) bo
         (Environ.push_rel (LocalDef (n,c,ty)) e) (`Let(n,c,ty)::acc)
    | Some sl, App(hd,arg) ->
       begin match kind_of_term hd with
       | Lambda (n,ty,bo) ->
           aux (Some (sl-1)) bo
             (Environ.push_rel (LocalAssum (n,ty)) e) (`Cut(n,ty,arg)::acc)
       | _ -> assert false
       end
    | _ -> assert false
    in
  aux sl b e []

let rec unzip ctx j =
  match ctx with
  | [] -> j
  | `Let (n,c,ty) :: ctx ->
      unzip ctx { j with uj_val = mkLetIn (n,c,ty,j.uj_val) }
  | `Cut (n,ty,arg) :: ctx ->
      unzip ctx { j with uj_val = mkApp (mkLambda (n,ty,j.uj_val),arg) }

let hcons_j j =
  { uj_val = hcons_constr j.uj_val; uj_type = hcons_constr j.uj_type} 

let feedback_completion_typecheck =
  let open Feedback in
  Option.iter (fun state_id ->
      feedback ~id:(State state_id) Feedback.Complete)

let infer_declaration ~trust env kn dcl =
  match dcl with
  | ParameterEntry (ctx,poly,(t,uctx),nl) ->
      let env = push_context ~strict:(not poly) uctx env in
      let j = infer env t in
      let abstract = poly && not (Option.is_empty kn) in
      let usubst, univs = Univ.abstract_universes abstract uctx in
      let c = Typeops.assumption_of_judgment env j in
      let t = hcons_constr (Vars.subst_univs_level_constr usubst c) in
	Undef nl, RegularArity t, None, poly, univs, false, ctx

  | DefinitionEntry ({ const_entry_type = Some typ;
                       const_entry_opaque = true;
		       const_entry_polymorphic = false} as c) ->
      let env = push_context ~strict:true c.const_entry_universes env in
      let { const_entry_body = body; const_entry_feedback = feedback_id } = c in
      let tyj = infer_type env typ in
      let proofterm =
        Future.chain ~greedy:true ~pure:true body (fun ((body,uctx),side_eff) ->
          let body, uctx, signatures =
            inline_side_effects env body uctx side_eff in
          let valid_signatures = check_signatures trust signatures in
	  let env = push_context_set uctx env in
          let j =
            let body,env,ectx = skip_trusted_seff valid_signatures body env in
            let j = infer env body in
            unzip ectx j in
          let j = hcons_j j in
	  let subst = Univ.LMap.empty in
          let _ = judge_of_cast env j DEFAULTcast tyj in
          assert (eq_constr typ tyj.utj_val);
          let _typ = RegularArity (Vars.subst_univs_level_constr subst typ) in
          feedback_completion_typecheck feedback_id;
          j.uj_val, uctx) in
      let def = OpaqueDef (Opaqueproof.create proofterm) in
      def, RegularArity typ, None, c.const_entry_polymorphic, 
	c.const_entry_universes,
	c.const_entry_inline_code, c.const_entry_secctx

  | DefinitionEntry c ->
      let { const_entry_type = typ; const_entry_opaque = opaque } = c in
      let { const_entry_body = body; const_entry_feedback = feedback_id } = c in
      let (body, ctx), side_eff = Future.join body in
      let univsctx = Univ.ContextSet.of_context c.const_entry_universes in
      let body, ctx, _ = inline_side_effects env body
        (Univ.ContextSet.union univsctx ctx) side_eff in
      let env = push_context_set ~strict:(not c.const_entry_polymorphic) ctx env in
      let abstract = c.const_entry_polymorphic && not (Option.is_empty kn) in
      let usubst, univs =
	Univ.abstract_universes abstract (Univ.ContextSet.to_context ctx) in      
      let j = infer env body in
      let typ = match typ with
        | None ->
           if not c.const_entry_polymorphic then (* Old-style polymorphism *)
             make_polymorphic_if_constant_for_ind env j
           else RegularArity (Vars.subst_univs_level_constr usubst j.uj_type)
        | Some t ->
           let tj = infer_type env t in
           let _ = judge_of_cast env j DEFAULTcast tj in
           assert (eq_constr t tj.utj_val);
           RegularArity (Vars.subst_univs_level_constr usubst t)
      in
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
      Context.Rel.fold_outside
        (Context.Rel.Declaration.fold
	  (fun t c -> Id.Set.union (global_vars_set env t) c))
      ctx ~init:Id.Set.empty

let record_aux env s_ty s_bo suggested_expr =
  let open Context.Named.Declaration in
  let in_ty = keep_hyps env s_ty in
  let v =
    String.concat " "
      (CList.map_filter (fun decl ->
          let id = get_id decl in
          if List.exists (Id.equal id % get_id) in_ty then None
          else Some (Id.to_string id))
        (keep_hyps env s_bo)) in
  Aux_file.record_in_aux "context_used" (v ^ ";" ^ suggested_expr)

let suggest_proof_using = ref (fun _ _ _ _ _ -> "")
let set_suggest_proof_using f = suggest_proof_using := f

let build_constant_declaration kn env (def,typ,proj,poly,univs,inline_code,ctx) =
  let open Context.Named.Declaration in
  let check declared inferred =
    let mk_set l = List.fold_right Id.Set.add (List.map get_id l) Id.Set.empty in
    let inferred_set, declared_set = mk_set inferred, mk_set declared in
    if not (Id.Set.subset inferred_set declared_set) then
      let l = Id.Set.elements (Idset.diff inferred_set declared_set) in
      let n = List.length l in
      errorlabstrm "" (Pp.(str "The following section " ++
        str (String.plural n "variable") ++
        str " " ++ str (String.conjugate_verb_to_be n) ++
        str " used but not declared:" ++
        fnl () ++ pr_sequence Id.print (List.rev l) ++ str ".")) in
  let sort evn l =
    List.filter (fun decl ->
      let id = get_id decl in
      List.exists (Names.Id.equal id % get_id) l)
    (named_context env) in
  (* We try to postpone the computation of used section variables *)
  let hyps, def =
    let context_ids = List.map get_id (named_context env) in
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
            let expr =
              !suggest_proof_using (Constant.to_string kn)
                env vars ids_typ context_ids in
            if !Flags.compilation_mode = Flags.BuildVo then
              record_aux env ids_typ vars expr;
            vars
        in
        keep_hyps env (Idset.union ids_typ ids_def), def
    | None ->
        if !Flags.compilation_mode = Flags.BuildVo then
          record_aux env Id.Set.empty Id.Set.empty "";
        [], def (* Empty section context: no need to check *)
    | Some declared ->
        (* We use the declared set and chain a check of correctness *)
        sort env declared,
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
    let res =
      let comp_univs = if poly then Some univs else None in
      match proj with
      | None -> compile_constant_body env comp_univs def
      | Some pb ->
	(* The compilation of primitive projections is a bit tricky, because
           they refer to themselves (the body of p looks like fun c =>
           Proj(p,c)). We break the cycle by building an ad-hoc compilation
           environment. A cleaner solution would be that kernel projections are
           simply Proj(i,c) with i an int and c a constr, but we would have to
           get rid of the compatibility layer. *)
	let cb =
	  { const_hyps = hyps;
	    const_body = def;
	    const_type = typ;
	    const_proj = proj;
	    const_body_code = None;
	    const_polymorphic = poly;
	    const_universes = univs;
	    const_inline_code = inline_code;
	    const_typing_flags = Environ.typing_flags env;
	    }
	in
	let env = add_constant kn cb env in
	compile_constant_body env comp_univs def
    in Option.map Cemitcodes.from_val res
  in
  { const_hyps = hyps;
    const_body = def;
    const_type = typ;
    const_proj = proj;
    const_body_code = tps;
    const_polymorphic = poly;
    const_universes = univs;
    const_inline_code = inline_code;
    const_typing_flags = Environ.typing_flags env }

(*s Global and local constant declaration. *)

let translate_constant mb env kn ce =
  build_constant_declaration kn env
    (infer_declaration ~trust:mb env (Some kn) ce)

let constant_entry_of_side_effect cb u =
  let pt =
    match cb.const_body, u with
    | OpaqueDef _, `Opaque (b, c) -> b, c
    | Def b, `Nothing -> Mod_subst.force_constr b, Univ.ContextSet.empty
    | _ -> assert false in
  DefinitionEntry {
    const_entry_body = Future.from_val (pt, []);
    const_entry_secctx = None;
    const_entry_feedback = None;
    const_entry_type =
      (match cb.const_type with RegularArity t -> Some t | _ -> None);
    const_entry_polymorphic = cb.const_polymorphic;
    const_entry_universes = cb.const_universes;
    const_entry_opaque = Declareops.is_opaque cb;
    const_entry_inline_code = cb.const_inline_code }
;;

let turn_direct (kn,cb,u,r as orig) =
  match cb.const_body, u with
  | OpaqueDef _, `Opaque (b,c) ->
      let pt = Future.from_val (b,c) in
      kn, { cb with const_body = OpaqueDef (Opaqueproof.create pt) }, u, r
   | _ -> orig
;;

type side_effect_role =
  | Subproof
  | Schema of inductive * string

type exported_side_effect = 
  constant * constant_body * side_effects constant_entry * side_effect_role

let export_side_effects mb env ce =
  match ce with
  | ParameterEntry _ | ProjectionEntry _ -> [], ce
  | DefinitionEntry c ->
      let { const_entry_body = body } = c in
      let _, eff = Future.force body in
      let ce = DefinitionEntry { c with
        const_entry_body = Future.chain ~greedy:true ~pure:true body
          (fun (b_ctx, _) -> b_ctx, []) } in
      let not_exists (c,_,_,_) =
        try ignore(Environ.lookup_constant c env); false
        with Not_found -> true in 
      let aux (acc,sl) { eff = se; from_env = mb } =
        let cbl = match se with
          | SEsubproof (c,cb,b) -> [c,cb,b,Subproof]
          | SEscheme (cl,k) ->
              List.map (fun (i,c,cb,b) -> c,cb,b,Schema(i,k)) cl in
        let cbl = List.filter not_exists cbl in
        if cbl = [] then acc, sl
        else cbl :: acc, (mb,List.length cbl) :: sl in
      let seff, signatures = List.fold_left aux ([],[]) (uniq_seff eff) in
      let trusted = check_signatures mb signatures in
      let push_seff env = function
        | kn, cb, `Nothing, _ ->
           let env = Environ.add_constant kn cb env in
	   if not cb.const_polymorphic then
	     Environ.push_context ~strict:true cb.const_universes env
	   else env
        | kn, cb, `Opaque(_, ctx), _ -> 
           let env = Environ.add_constant kn cb env in
	   if not cb.const_polymorphic then
	     let env = Environ.push_context ~strict:true cb.const_universes env in
             Environ.push_context_set ~strict:true ctx env
	   else env in
      let rec translate_seff sl seff acc env =
        match sl, seff with
        | _, [] -> List.rev acc, ce
        | (None | Some 0), cbs :: rest ->
           let env, cbs =
             List.fold_left (fun (env,cbs) (kn, ocb, u, r) ->
               let ce = constant_entry_of_side_effect ocb u in
               let cb = translate_constant mb env kn ce in
               (push_seff env (kn, cb,`Nothing, Subproof),(kn,cb,ce,r) :: cbs)) 
             (env,[]) cbs in
           translate_seff sl rest (cbs @ acc) env
        | Some sl, cbs :: rest ->
           let cbs_len = List.length cbs in
           let cbs = List.map turn_direct cbs in
           let env = List.fold_left push_seff env cbs in
           let ecbs = List.map (fun (kn,cb,u,r) ->
             kn, cb, constant_entry_of_side_effect cb u, r) cbs in
           translate_seff (Some (sl-cbs_len)) rest (ecbs @ acc) env
     in
       translate_seff trusted seff [] env
;;

let translate_local_assum env t =
  let j = infer env t in
  let t = Typeops.assumption_of_judgment env j in
    t

let translate_recipe env kn r =
  build_constant_declaration kn env (Cooking.cook_constant env r)

let translate_local_def mb env id centry =
  let def,typ,proj,poly,univs,inline_code,ctx =
    infer_declaration ~trust:mb env None (DefinitionEntry centry) in
  let typ = type_of_constant_type env typ in
  if ctx = None && !Flags.compilation_mode = Flags.BuildVo then begin
    match def with
    | Undef _ -> ()
    | Def _ -> ()
    | OpaqueDef lc ->
       let open Context.Named.Declaration in
       let context_ids = List.map get_id (named_context env) in
       let ids_typ = global_vars_set env typ in
       let ids_def = global_vars_set env
         (Opaqueproof.force_proof (opaque_tables env) lc) in
       let expr =
         !suggest_proof_using (Id.to_string id)
           env ids_def ids_typ context_ids in
       record_aux env ids_typ ids_def expr
  end;
  def, typ, univs

(* Insertion of inductive types. *)

let translate_mind env kn mie = Indtypes.check_inductive env kn mie

let inline_entry_side_effects env ce = { ce with
  const_entry_body = Future.chain ~greedy:true ~pure:true
    ce.const_entry_body (fun ((body, ctx), side_eff) ->
      let body, ctx',_ = inline_side_effects env body ctx side_eff in
      (body, ctx'), []);
}

let inline_side_effects env body side_eff =
  pi1 (inline_side_effects env body Univ.ContextSet.empty side_eff)
