(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
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

let infer_declaration (type a) ~(trust : a trust) env (dcl : a constant_entry) =
  match dcl with
    | ParameterEntry (ctx,(t,uctx),nl) ->
      let env = match uctx with
        | Monomorphic_entry uctx -> push_context_set ~strict:true uctx env
        | Polymorphic_entry (_, uctx) -> push_context ~strict:false uctx env
      in
      let j = Typeops.infer env t in
      let usubst, univs = Declareops.abstract_universes uctx in
      let r = Typeops.assumption_of_judgment env j in
      let t = Vars.subst_univs_level_constr usubst j.uj_val in
      {
        Cooking.cook_body = Undef nl;
        cook_type = t;
        cook_universes = univs;
        cook_relevance = r;
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
        let typ = Typeops.infer_type env typ in
        Typeops.check_primitive_type env op_t typ.utj_val;
        typ.utj_val
      | None ->
        match op_t with
        | CPrimitives.OT_op op -> Typeops.type_of_prim env op
        | CPrimitives.OT_type _ -> mkSet
      in
      let cd =
        match op_t with
        | CPrimitives.OT_op op -> Declarations.Primitive op
        | CPrimitives.OT_type _ -> Undef None in
      { Cooking.cook_body = cd;
        cook_type = ty;
        cook_universes = Monomorphic uctxt;
        cook_inline = false;
        cook_context = None;
        cook_relevance = Sorts.Relevant;
      }

  (** Definition [c] is opaque (Qed), non polymorphic and with a specified type,
      so we delay the typing and hash consing of its body. *)

  | OpaqueEntry ({ opaque_entry_type = typ;
                       opaque_entry_universes = Monomorphic_entry univs; _ } as c) ->
      let env = push_context_set ~strict:true univs env in
      let { opaque_entry_body = body; opaque_entry_feedback = feedback_id; _ } = c in
      let tyj = Typeops.infer_type env typ in
      let proofterm =
        Future.chain body begin fun ((body,uctx),side_eff) ->
          (* don't redeclare universes which are declared for the type *)
          let uctx = Univ.ContextSet.diff uctx univs in
          let j, uctx = match trust with
          | Pure ->
            let env = push_context_set uctx env in
            let j = Typeops.infer env body in
            let _ = Typeops.judge_of_cast env j DEFAULTcast tyj in
            j, uctx
          | SideEffects handle ->
            let (body, uctx', valid_signatures) = handle env body side_eff in
            let uctx = Univ.ContextSet.union uctx uctx' in
            let env = push_context_set uctx env in
            let body,env,ectx = skip_trusted_seff valid_signatures body env in
            let j = Typeops.infer env body in
            let j = unzip ectx j in
            let _ = Typeops.judge_of_cast env j DEFAULTcast tyj in
            j, uctx
          in
          let c = j.uj_val in
          feedback_completion_typecheck feedback_id;
          c, Opaqueproof.PrivateMonomorphic uctx
      end in
      let def = OpaqueDef proofterm in
      {
        Cooking.cook_body = def;
        cook_type = tyj.utj_val;
        cook_universes = Monomorphic univs;
        cook_relevance = Sorts.relevance_of_sort tyj.utj_type;
        cook_inline = false;
        cook_context = Some c.opaque_entry_secctx;
      }

  (** Similar case for polymorphic entries. *)

  | OpaqueEntry ({ opaque_entry_type = typ;
                       opaque_entry_universes = Polymorphic_entry (nas, uctx); _ } as c) ->
      let { opaque_entry_body = body; opaque_entry_feedback = feedback_id; _ } = c in
      let env = push_context ~strict:false uctx env in
      let tj = Typeops.infer_type env typ in
      let sbst, auctx = Univ.abstract_universes nas uctx in
      let usubst = Univ.make_instance_subst sbst in
      let proofterm = Future.chain body begin fun ((body, ctx), side_eff) ->
        let body, ctx = match trust with
        | Pure -> body, ctx
        | SideEffects handle ->
          let body, ctx', _ = handle env body side_eff in
          body, Univ.ContextSet.union ctx ctx'
        in
        (** [ctx] must contain local universes, such that it has no impact
            on the rest of the graph (up to transitivity). *)
        let env = push_subgraph ctx env in
        let private_univs = on_snd (Univ.subst_univs_level_constraints usubst) ctx in
        let j = Typeops.infer env body in
        let _ = Typeops.judge_of_cast env j DEFAULTcast tj in
        let def = Vars.subst_univs_level_constr usubst j.uj_val in
        let () = feedback_completion_typecheck feedback_id in
        def, Opaqueproof.PrivatePolymorphic (Univ.AUContext.size auctx, private_univs)
      end in
      let def = OpaqueDef proofterm in
      let typ = Vars.subst_univs_level_constr usubst tj.utj_val in
      {
        Cooking.cook_body = def;
        cook_type = typ;
        cook_universes = Polymorphic auctx;
        cook_relevance = Sorts.relevance_of_sort tj.utj_type;
        cook_inline = false;
        cook_context = Some c.opaque_entry_secctx;
      }

  (** Other definitions have to be processed immediately. *)
  | DefinitionEntry c ->
      let { const_entry_type = typ; _ } = c in
      let { const_entry_body = body; const_entry_feedback = feedback_id; _ } = c in
      let () = match trust with
      | Pure -> ()
      | SideEffects _ -> assert false
      in
      let env, usubst, univs = match c.const_entry_universes with
      | Monomorphic_entry ctx ->
        let env = push_context_set ~strict:true ctx env in
        env, Univ.empty_level_subst, Monomorphic ctx
      | Polymorphic_entry (nas, uctx) ->
        (** [ctx] must contain local universes, such that it has no impact
            on the rest of the graph (up to transitivity). *)
        let env = push_context ~strict:false uctx env in
        let sbst, auctx = Univ.abstract_universes nas uctx in
        let sbst = Univ.make_instance_subst sbst in
        env, sbst, Polymorphic auctx
      in
      let j = Typeops.infer env body in
      let typ = match typ with
        | None ->
          Vars.subst_univs_level_constr usubst j.uj_type
        | Some t ->
           let tj = Typeops.infer_type env t in
           let _ = Typeops.judge_of_cast env j DEFAULTcast tj in
           Vars.subst_univs_level_constr usubst tj.utj_val
      in
      let def = Vars.subst_univs_level_constr usubst j.uj_val in
      let def = Def (Mod_subst.from_val def) in
	feedback_completion_typecheck feedback_id;
      {
        Cooking.cook_body = def;
        cook_type = typ;
        cook_universes = univs;
        cook_relevance = Retypeops.relevance_of_term env j.uj_val;
        cook_inline = c.const_entry_inline_code;
        cook_context = c.const_entry_secctx;
      }

let build_constant_declaration env result =
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
    | None ->
      if List.is_empty context_ids then
        (* Empty section context: no need to check *)
        [], def
      else
        (* No declared section vars, and non-empty section context:
           we must look at the body NOW, if any *)
        let ids_typ = global_vars_set env typ in
        let ids_def = match def with
        | Undef _ | Primitive _ -> Id.Set.empty
        | Def cs -> global_vars_set env (Mod_subst.force_constr cs)
        | OpaqueDef _ ->
          (* Opaque definitions always come with their section variables *)
          assert false
        in
        keep_hyps env (Id.Set.union ids_typ ids_def), def
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
          let iter k cu = Future.chain cu (fun (c, _ as p) -> k c; p) in
          let kont c =
            let ids_typ = global_vars_set env typ in
            let ids_def = global_vars_set env c in
            let inferred = keep_hyps env (Id.Set.union ids_typ ids_def) in
            check declared inferred
          in
          OpaqueDef (iter kont lc)
  in
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
    const_relevance = result.cook_relevance;
    const_inline_code = result.cook_inline;
    const_typing_flags = Environ.typing_flags env }

(*s Global and local constant declaration. *)

let translate_constant mb env _kn ce =
  build_constant_declaration env
    (infer_declaration ~trust:mb env ce)

let translate_local_assum env t =
  let j = Typeops.infer env t in
  let t = Typeops.assumption_of_judgment env j in
    j.uj_val, t

let translate_recipe env _kn r =
  let open Cooking in
  let result = Cooking.cook_constant r in
  let univs = result.cook_universes in
  let res = Cbytegen.compile_constant_body ~fail_on_error:false env univs result.cook_body in
  let tps = Option.map Cemitcodes.from_val res in
  { const_hyps = Option.get result.cook_context;
    const_body = result.cook_body;
    const_type = result.cook_type;
    const_body_code = tps;
    const_universes = univs;
    const_relevance = result.cook_relevance;
    const_inline_code = result.cook_inline;
    const_typing_flags = Environ.typing_flags env }

let translate_local_def env _id centry =
  let open Cooking in
  let centry = {
    const_entry_body = centry.secdef_body;
    const_entry_secctx = centry.secdef_secctx;
    const_entry_feedback = centry.secdef_feedback;
    const_entry_type = centry.secdef_type;
    const_entry_universes = Monomorphic_entry Univ.ContextSet.empty;
    const_entry_inline_code = false;
  } in
  let decl = infer_declaration ~trust:Pure env (DefinitionEntry centry) in
  let typ = decl.cook_type in
  let () = match decl.cook_universes with
  | Monomorphic ctx -> assert (Univ.ContextSet.is_empty ctx)
  | Polymorphic _ -> assert false
  in
  let c = match decl.cook_body with
  | Def c -> Mod_subst.force_constr c
  | Undef _ | Primitive _ | OpaqueDef _ -> assert false
  in
  c, decl.cook_relevance, typ
