(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Created by Jacek Chrzaszcz, Aug 2002 as part of the implementation of
   the Coq module system *)

(* This module provides the main entry points for type-checking basic
   declarations *)

open CErrors
open Util
open Names
open Constr
open Declarations
open Environ
open Entries
open Typeops

module NamedDecl = Context.Named.Declaration

(* Insertion of constants and parameters in environment. *)

type 'a effect_handler =
  env -> Constr.t -> 'a -> (Constr.t * Univ.ContextSet.t * int)

type _ trust =
| Pure : unit trust
| SideEffects : 'a effect_handler -> 'a trust

let skip_trusted_seff sl b e =
  let rec aux sl b e acc =
    let open Context.Rel.Declaration in
    if Int.equal sl 0 then b, e, acc
    else match kind b with
    | LetIn (n,c,ty,bo) ->
       aux (sl - 1) bo
         (Environ.push_rel (LocalDef (n,c,ty)) e) (`Let(n,c,ty)::acc)
    | App(hd,arg) ->
       begin match kind hd with
       | Lambda (n,ty,bo) ->
           aux (sl - 1) bo
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

let feedback_completion_typecheck =
  Option.iter (fun state_id ->
      Feedback.feedback ~id:state_id Feedback.Complete)

let abstract_constant_universes = function
  | Monomorphic_const_entry uctx ->
    Univ.empty_level_subst, Monomorphic_const uctx
  | Polymorphic_const_entry (nas, uctx) ->
    let sbst, auctx = Univ.abstract_universes nas uctx in
    let sbst = Univ.make_instance_subst sbst in
    sbst, Polymorphic_const auctx

let infer_declaration (type a) ~(trust : a trust) env (dcl : a constant_entry) =
  match dcl with
    | ParameterEntry (ctx,(t,uctx),nl) ->
      let env = match uctx with
        | Monomorphic_const_entry uctx -> push_context_set ~strict:true uctx env
        | Polymorphic_const_entry (_, uctx) -> push_context ~strict:false uctx env
      in
      let j = infer env t in
      let usubst, univs = abstract_constant_universes uctx in
      let c = Typeops.assumption_of_judgment env j in
      let t = Constr.hcons (Vars.subst_univs_level_constr usubst c) in
      {
        Cooking.cook_body = Undef nl;
        cook_type = t;
        cook_universes = univs;
        cook_private_univs = None;
        cook_inline = false;
        cook_context = ctx;
      }

    (** Primitives cannot be universe polymorphic *)
    | PrimitiveEntry ({ prim_entry_type = otyp;
                        prim_entry_univs = uctxt;
                        prim_entry_content = op_t;
                      }) ->
      let env = push_context_set ~strict:true uctxt env in
      let ty = match otyp with
      | Some typ ->
        let tyj = infer_type env typ in
        check_primitive_type env op_t tyj.utj_val;
        Constr.hcons tyj.utj_val
      | None ->
        match op_t with
        | CPrimitives.OT_op op -> type_of_prim env op
        | CPrimitives.OT_type _ -> mkSet
      in
      let cd =
        match op_t with
        | CPrimitives.OT_op op -> Declarations.Primitive op
        | CPrimitives.OT_type _ -> Undef None in
      { Cooking.cook_body = cd;
        cook_type = ty;
        cook_universes = Monomorphic_const uctxt;
        cook_private_univs = None;
        cook_inline = false;
        cook_context = None
      }

  (** Definition [c] is opaque (Qed), non polymorphic and with a specified type,
      so we delay the typing and hash consing of its body.
      Remark: when the universe quantification is given explicitly, we could
      delay even in the polymorphic case.  *)

(** Definition is opaque (Qed) and non polymorphic with known type, so we delay
the typing and hash consing of its body.

TODO: if the universe quantification is given explicitly, we could delay even in
the polymorphic case
  *)
  | DefinitionEntry ({ const_entry_type = Some typ;
                       const_entry_opaque = true;
                       const_entry_universes = Monomorphic_const_entry univs; _ } as c) ->
      let env = push_context_set ~strict:true univs env in
      let { const_entry_body = body; const_entry_feedback = feedback_id ; _ } = c in
      let tyj = infer_type env typ in
      let proofterm =
        Future.chain body (fun ((body,uctx),side_eff) ->
          (* don't redeclare universes which are declared for the type *)
          let uctx = Univ.ContextSet.diff uctx univs in
          let j, uctx = match trust with
          | Pure ->
            let env = push_context_set uctx env in
            let j = infer env body in
            let _ = judge_of_cast env j DEFAULTcast tyj in
            j, uctx
          | SideEffects handle ->
            let (body, uctx', valid_signatures) = handle env body side_eff in
            let uctx = Univ.ContextSet.union uctx uctx' in
            let env = push_context_set uctx env in
            let body,env,ectx = skip_trusted_seff valid_signatures body env in
            let j = infer env body in
            let j = unzip ectx j in
            let _ = judge_of_cast env j DEFAULTcast tyj in
            j, uctx
          in
          let c = Constr.hcons j.uj_val in
          feedback_completion_typecheck feedback_id;
          c, uctx) in
      let def = OpaqueDef (Opaqueproof.create proofterm) in
      {
        Cooking.cook_body = def;
        cook_type = typ;
        cook_universes = Monomorphic_const univs;
        cook_private_univs = None;
        cook_inline = c.const_entry_inline_code;
        cook_context = c.const_entry_secctx;
      }

  (** Other definitions have to be processed immediately. *)
  | DefinitionEntry c ->
      let { const_entry_type = typ; const_entry_opaque = opaque ; _ } = c in
      let { const_entry_body = body; const_entry_feedback = feedback_id; _ } = c in
      let (body, ctx), side_eff = Future.join body in
      let body, ctx = match trust with
      | Pure -> body, ctx
      | SideEffects handle ->
        let body, ctx', _ = handle env body side_eff in
        body, Univ.ContextSet.union ctx ctx'
      in
      let env, usubst, univs, private_univs = match c.const_entry_universes with
      | Monomorphic_const_entry univs ->
        let ctx = Univ.ContextSet.union univs ctx in
        let env = push_context_set ~strict:true ctx env in
        env, Univ.empty_level_subst, Monomorphic_const ctx, None
      | Polymorphic_const_entry (nas, uctx) ->
        (** [ctx] must contain local universes, such that it has no impact
            on the rest of the graph (up to transitivity). *)
        let env = push_context ~strict:false uctx env in
        let sbst, auctx = Univ.abstract_universes nas uctx in
        let sbst = Univ.make_instance_subst sbst in
        let env, local =
          if opaque then
            push_subgraph ctx env, Some (on_snd (Univ.subst_univs_level_constraints sbst) ctx)
          else
          if Univ.ContextSet.is_empty ctx then env, None
          else CErrors.anomaly Pp.(str "Local universes in non-opaque polymorphic definition.")
        in
        env, sbst, Polymorphic_const auctx, local
      in
      let j = infer env body in
      let typ = match typ with
        | None ->
          Vars.subst_univs_level_constr usubst j.uj_type
        | Some t ->
           let tj = infer_type env t in
           let _ = judge_of_cast env j DEFAULTcast tj in
           Vars.subst_univs_level_constr usubst t
      in
      let def = Constr.hcons (Vars.subst_univs_level_constr usubst j.uj_val) in
      let def = 
	if opaque then OpaqueDef (Opaqueproof.create (Future.from_val (def, Univ.ContextSet.empty)))
	else Def (Mod_subst.from_val def) 
      in
	feedback_completion_typecheck feedback_id;
      {
        Cooking.cook_body = def;
        cook_type = typ;
        cook_universes = univs;
        cook_private_univs = private_univs;
        cook_inline = c.const_entry_inline_code;
        cook_context = c.const_entry_secctx;
      }

let record_aux env s_ty s_bo =
  let in_ty = keep_hyps env s_ty in
  let v =
    String.concat " "
      (CList.map_filter (fun decl ->
          let id = NamedDecl.get_id decl in
          if List.exists (NamedDecl.get_id %> Id.equal id) in_ty then None
          else Some (Id.to_string id))
        (keep_hyps env s_bo)) in
  Aux_file.record_in_aux "context_used" v

let build_constant_declaration _kn env result =
  let open Cooking in
  let typ = result.cook_type in
  let check declared inferred =
    let mk_set l = List.fold_right Id.Set.add (List.map NamedDecl.get_id l) Id.Set.empty in
    let inferred_set, declared_set = mk_set inferred, mk_set declared in
    if not (Id.Set.subset inferred_set declared_set) then
      let l = Id.Set.elements (Id.Set.diff inferred_set declared_set) in
      let n = List.length l in
      let declared_vars = Pp.pr_sequence Id.print (Id.Set.elements declared_set) in
      let inferred_vars = Pp.pr_sequence Id.print (Id.Set.elements inferred_set) in
      let missing_vars  = Pp.pr_sequence Id.print (List.rev l) in
      user_err Pp.(prlist str
         ["The following section "; (String.plural n "variable"); " ";
          (String.conjugate_verb_to_be n); " used but not declared:"] ++ fnl () ++
         missing_vars ++ str "." ++ fnl () ++ fnl () ++
         str "You can either update your proof to not depend on " ++ missing_vars ++
         str ", or you can update your Proof line from" ++ fnl () ++
         str "Proof using " ++ declared_vars ++ fnl () ++
         str "to" ++ fnl () ++
         str "Proof using " ++ inferred_vars) in
  let sort l =
    List.filter (fun decl ->
      let id = NamedDecl.get_id decl in
      List.exists (NamedDecl.get_id %> Names.Id.equal id) l)
    (named_context env) in
  (* We try to postpone the computation of used section variables *)
  let hyps, def =
    let context_ids = List.map NamedDecl.get_id (named_context env) in
    let def = result.cook_body in
    match result.cook_context with
    | None when not (List.is_empty context_ids) -> 
        (* No declared section vars, and non-empty section context:
           we must look at the body NOW, if any *)
        let ids_typ = global_vars_set env typ in
        let ids_def = match def with
        | Undef _ | Primitive _ -> Id.Set.empty
        | Def cs -> global_vars_set env (Mod_subst.force_constr cs)
        | OpaqueDef lc ->
            let vars =
              global_vars_set env
                (Opaqueproof.force_proof (opaque_tables env) lc) in
            (* we force so that cst are added to the env immediately after *)
            ignore(Opaqueproof.force_constraints (opaque_tables env) lc);
            if !Flags.record_aux_file then record_aux env ids_typ vars;
            vars
        in
        keep_hyps env (Id.Set.union ids_typ ids_def), def
    | None ->
        if !Flags.record_aux_file then
          record_aux env Id.Set.empty Id.Set.empty;
        [], def (* Empty section context: no need to check *)
    | Some declared ->
        (* We use the declared set and chain a check of correctness *)
        sort declared,
        match def with
        | Undef _ | Primitive _ as x -> x (* nothing to check *)
        | Def cs as x ->
            let ids_typ = global_vars_set env typ in
            let ids_def = global_vars_set env (Mod_subst.force_constr cs) in
            let inferred = keep_hyps env (Id.Set.union ids_typ ids_def) in
            check declared inferred;
            x
        | OpaqueDef lc -> (* In this case we can postpone the check *)
            OpaqueDef (Opaqueproof.iter_direct_opaque (fun c ->
              let ids_typ = global_vars_set env typ in
              let ids_def = global_vars_set env c in
              let inferred = keep_hyps env (Id.Set.union ids_typ ids_def) in
              check declared inferred) lc) in
  let univs = result.cook_universes in
  let tps = 
    let res = Cbytegen.compile_constant_body ~fail_on_error:false env univs def in
    Option.map Cemitcodes.from_val res
  in
  { const_hyps = hyps;
    const_body = def;
    const_type = typ;
    const_body_code = tps;
    const_universes = univs;
    const_private_poly_univs = result.cook_private_univs;
    const_inline_code = result.cook_inline;
    const_typing_flags = Environ.typing_flags env }

(*s Global and local constant declaration. *)

let translate_constant mb env kn ce =
  build_constant_declaration kn env
    (infer_declaration ~trust:mb env ce)

let translate_local_assum env t =
  let j = infer env t in
  let t = Typeops.assumption_of_judgment env j in
    t

let translate_recipe ~hcons env kn r =
  build_constant_declaration kn env (Cooking.cook_constant ~hcons r)

let translate_local_def env _id centry =
  let open Cooking in
  let body = Future.from_val ((centry.secdef_body, Univ.ContextSet.empty), ()) in
  let centry = {
    const_entry_body = body;
    const_entry_secctx = centry.secdef_secctx;
    const_entry_feedback = centry.secdef_feedback;
    const_entry_type = centry.secdef_type;
    const_entry_universes = Monomorphic_const_entry Univ.ContextSet.empty;
    const_entry_opaque = false;
    const_entry_inline_code = false;
  } in
  let decl = infer_declaration ~trust:Pure env (DefinitionEntry centry) in
  let typ = decl.cook_type in
  if Option.is_empty decl.cook_context && !Flags.record_aux_file then begin
    match decl.cook_body with
    | Undef _ -> ()
    | Primitive _ -> ()
    | Def _ -> ()
    | OpaqueDef lc ->
       let ids_typ = global_vars_set env typ in
       let ids_def = global_vars_set env
         (Opaqueproof.force_proof (opaque_tables env) lc) in
       record_aux env ids_typ ids_def
  end;
  let () = match decl.cook_universes with
  | Monomorphic_const ctx -> assert (Univ.ContextSet.is_empty ctx)
  | Polymorphic_const _ -> assert false
  in
  let c = match decl.cook_body with
  | Def c -> Mod_subst.force_constr c
  | OpaqueDef o ->
    let p = Opaqueproof.force_proof (Environ.opaque_tables env) o in
    let cst = Opaqueproof.force_constraints (Environ.opaque_tables env) o in
    (** Let definitions are ensured to have no extra constraints coming from
        the body by virtue of the typing of [Entries.section_def_entry]. *)
    let () = assert (Univ.ContextSet.is_empty cst) in
    p
  | Undef _ | Primitive _ -> assert false
  in
  c, typ

(* Insertion of inductive types. *)

let translate_mind env kn mie = Indtypes.check_inductive env kn mie
