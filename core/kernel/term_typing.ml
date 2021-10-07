(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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
open Univ

module NamedDecl = Context.Named.Declaration

(* Insertion of constants and parameters in environment. *)

type 'a effect_handler =
  env -> Constr.t -> 'a -> (Constr.t * ContextSet.t * int)

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

type typing_context =
| MonoTyCtx of Environ.env * unsafe_type_judgment * Id.Set.t * Stateid.t option
| PolyTyCtx of Environ.env * unsafe_type_judgment * universe_level_subst * AbstractContext.t * Id.Set.t * Stateid.t option

let check_primitive_type env op_t u t =
  let inft = Typeops.type_of_prim_or_type env u op_t in
  try Reduction.default_conv ~l2r:false Reduction.CONV env inft t
  with Reduction.NotConvertible ->
    Type_errors.error_incorrect_primitive env (make_judge op_t inft) t

let infer_primitive env { prim_entry_type = utyp; prim_entry_content = p; } =
  let open CPrimitives in
  let auctx = CPrimitives.op_or_type_univs p in
  let univs, typ =
    match utyp with
    | None ->
      let u = UContext.instance (AbstractContext.repr auctx) in
      let typ = Typeops.type_of_prim_or_type env u p in
      let univs = if AbstractContext.is_empty auctx then Monomorphic
        else Polymorphic auctx
      in
      univs, typ

    | Some (typ,Monomorphic_entry) ->
      assert (AbstractContext.is_empty auctx); (* ensured by ComPrimitive *)
      let u = Instance.empty in
      let typ =
        let typ = Typeops.infer_type env typ in
        check_primitive_type env p u typ.utj_val;
        typ.utj_val
      in
      Monomorphic, typ

    | Some (typ,Polymorphic_entry uctx) ->
      assert (not (AbstractContext.is_empty auctx)); (* ensured by ComPrimitive *)
      (* [push_context] will check that the universes aren't repeated in
         the instance so comparing the sizes works. No polymorphic
         primitive uses constraints currently. *)
      if not (AbstractContext.size auctx = UContext.size uctx
              && Constraints.is_empty (UContext.constraints uctx))
      then CErrors.user_err Pp.(str "Incorrect universes for primitive " ++
                                str (op_or_type_to_string p));
      let env = push_context ~strict:false uctx env in
      (* Now we know that uctx matches the auctx *)
      let typ = (Typeops.infer_type env typ).utj_val in
      let () = check_primitive_type env p (UContext.instance uctx) typ in
      let uctx = UContext.refine_names (AbstractContext.names auctx) uctx in
      let u, auctx = abstract_universes uctx in
      let typ = Vars.subst_univs_level_constr (make_instance_subst u) typ in
      Polymorphic auctx, typ
  in
  let body = match p with
    | OT_op op -> Declarations.Primitive op
    | OT_type _ -> Undef None
    | OT_const c -> Def (CPrimitives.body_of_prim_const c)
  in
  { Cooking.cook_body = body;
    cook_type = typ;
    cook_universes = univs;
    cook_inline = false;
    cook_context = None;
    cook_relevance = Sorts.Relevant;
    cook_flags = Environ.typing_flags env;
  }

let infer_declaration env (dcl : constant_entry) =
  match dcl with
  | ParameterEntry entry ->
    let env = match entry.parameter_entry_universes with
      | Monomorphic_entry -> env
      | Polymorphic_entry uctx -> push_context ~strict:false uctx env
    in
    let j = Typeops.infer env entry.parameter_entry_type in
    let usubst, univs = Declareops.abstract_universes entry.parameter_entry_universes in
    let r = Typeops.assumption_of_judgment env j in
    let t = Vars.subst_univs_level_constr usubst j.uj_val in
    {
      Cooking.cook_body = Undef entry.parameter_entry_inline_code;
      cook_type = t;
      cook_universes = univs;
      cook_relevance = r;
      cook_inline = false;
      cook_context = entry.parameter_entry_secctx;
      cook_flags = Environ.typing_flags env;
    }

  | PrimitiveEntry entry -> infer_primitive env entry

  | DefinitionEntry c ->
      let { const_entry_type = typ; _ } = c in
      let { const_entry_body = body; const_entry_feedback = feedback_id; _ } = c in
      let env, usubst, univs = match c.const_entry_universes with
      | Monomorphic_entry ->
        env, empty_level_subst, Monomorphic
      | Polymorphic_entry uctx ->
        (** [ctx] must contain local universes, such that it has no impact
            on the rest of the graph (up to transitivity). *)
        let env = push_context ~strict:false uctx env in
        let sbst, auctx = abstract_universes uctx in
        let sbst = make_instance_subst sbst in
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
      let def = Def def in
        feedback_completion_typecheck feedback_id;
      {
        Cooking.cook_body = def;
        cook_type = typ;
        cook_universes = univs;
        cook_relevance = Relevanceops.relevance_of_term env j.uj_val;
        cook_inline = c.const_entry_inline_code;
        cook_context = c.const_entry_secctx;
        cook_flags = Environ.typing_flags env;
      }

(** Definition is opaque (Qed), so we delay the typing of its body. *)
let infer_opaque env = function
  | ({ opaque_entry_type = typ;
                       opaque_entry_universes = Monomorphic_entry; _ } as c) ->
      let { opaque_entry_feedback = feedback_id; _ } = c in
      let tyj = Typeops.infer_type env typ in
      let context = MonoTyCtx (env, tyj, c.opaque_entry_secctx, feedback_id) in
      let def = OpaqueDef () in
      {
        Cooking.cook_body = def;
        cook_type = tyj.utj_val;
        cook_universes = Monomorphic;
        cook_relevance = Sorts.relevance_of_sort tyj.utj_type;
        cook_inline = false;
        cook_context = Some c.opaque_entry_secctx;
        cook_flags = Environ.typing_flags env;
      }, context

  | ({ opaque_entry_type = typ;
                       opaque_entry_universes = Polymorphic_entry uctx; _ } as c) ->
      let { opaque_entry_feedback = feedback_id; _ } = c in
      let env = push_context ~strict:false uctx env in
      let tj = Typeops.infer_type env typ in
      let sbst, auctx = abstract_universes uctx in
      let usubst = make_instance_subst sbst in
      let context = PolyTyCtx (env, tj, usubst, auctx, c.opaque_entry_secctx, feedback_id) in
      let def = OpaqueDef () in
      let typ = Vars.subst_univs_level_constr usubst tj.utj_val in
      {
        Cooking.cook_body = def;
        cook_type = typ;
        cook_universes = Polymorphic auctx;
        cook_relevance = Sorts.relevance_of_sort tj.utj_type;
        cook_inline = false;
        cook_context = Some c.opaque_entry_secctx;
        cook_flags = Environ.typing_flags env;
      }, context

let check_section_variables env declared_set typ body =
  let ids_typ = global_vars_set env typ in
  let ids_def = global_vars_set env body in
  let inferred_set = Environ.really_needed env (Id.Set.union ids_typ ids_def) in
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
        str "Proof using " ++ inferred_vars)

let build_constant_declaration env result =
  let open Cooking in
  let typ = result.cook_type in
  (* We try to postpone the computation of used section variables *)
  let hyps, def =
    let context_ids = List.map NamedDecl.get_id (named_context env) in
    let def = result.cook_body in
    match result.cook_context with
    | None ->
      if List.is_empty context_ids then
        (* Empty section context: no need to check *)
        Id.Set.empty, def
      else
        (* No declared section vars, and non-empty section context:
           we must look at the body NOW, if any *)
        let ids_typ = global_vars_set env typ in
        let ids_def = match def with
        | Undef _ | Primitive _ -> Id.Set.empty
        | Def cs -> global_vars_set env cs
        | OpaqueDef _ ->
          (* Opaque definitions always come with their section variables *)
          assert false
        in
        Environ.really_needed env (Id.Set.union ids_typ ids_def), def
    | Some declared ->
      let declared = Environ.really_needed env declared in
      (* We use the declared set and chain a check of correctness *)
      declared,
      match def with
      | Undef _ | Primitive _ | OpaqueDef _ as x -> x (* nothing to check *)
      | Def cs as x ->
        let () = check_section_variables env declared typ cs in
        x
  in
  let univs = result.cook_universes in
  let hyps = List.filter (fun d -> Id.Set.mem (NamedDecl.get_id d) hyps) (Environ.named_context env) in
  let tps = Vmbytegen.compile_constant_body ~fail_on_error:false env univs def in
  { const_hyps = hyps;
    const_body = def;
    const_type = typ;
    const_body_code = tps;
    const_universes = univs;
    const_relevance = result.cook_relevance;
    const_inline_code = result.cook_inline;
    const_typing_flags = result.cook_flags }

let check_delayed (type a) (handle : a effect_handler) tyenv (body : a proof_output) = match tyenv with
| MonoTyCtx (env, tyj, declared, feedback_id) ->
  let ((body, uctx), side_eff) = body in
  let (body, uctx', valid_signatures) = handle env body side_eff in
  let uctx = ContextSet.union uctx uctx' in
  let env = push_context_set uctx env in
  let body,env,ectx = skip_trusted_seff valid_signatures body env in
  let j = Typeops.infer env body in
  let j = unzip ectx j in
  let _ = Typeops.judge_of_cast env j DEFAULTcast tyj in
  let c = j.uj_val in
  let () = check_section_variables env declared tyj.utj_val body in
  feedback_completion_typecheck feedback_id;
  c, Opaqueproof.PrivateMonomorphic uctx
| PolyTyCtx (env, tj, usubst, auctx, declared, feedback_id) ->
  let ((body, ctx), side_eff) = body in
  let body, ctx', _ = handle env body side_eff in
  let ctx = ContextSet.union ctx ctx' in
  (** [ctx] must contain local universes, such that it has no impact
      on the rest of the graph (up to transitivity). *)
  let env = push_subgraph ctx env in
  let private_univs = on_snd (subst_univs_level_constraints usubst) ctx in
  let j = Typeops.infer env body in
  let _ = Typeops.judge_of_cast env j DEFAULTcast tj in
  let () = check_section_variables env declared tj.utj_val body in
  let def = Vars.subst_univs_level_constr usubst j.uj_val in
  let () = feedback_completion_typecheck feedback_id in
  def, Opaqueproof.PrivatePolymorphic (AbstractContext.size auctx, private_univs)

(*s Global and local constant declaration. *)

let translate_constant env _kn ce =
  build_constant_declaration env
    (infer_declaration env ce)

let translate_opaque env _kn ce =
  let def, ctx = infer_opaque env ce in
  build_constant_declaration env def, ctx

let translate_local_assum env t =
  let j = Typeops.infer env t in
  let t = Typeops.assumption_of_judgment env j in
    j.uj_val, t

let translate_recipe env _kn r =
  let open Cooking in
  let result = Cooking.cook_constant r in
  let univs = result.cook_universes in
  let tps = Vmbytegen.compile_constant_body ~fail_on_error:false env univs result.cook_body in
  let hyps = Option.get result.cook_context in
  (* Trust the set of section hypotheses generated by Cooking *)
  let hyps = List.filter (fun d -> Id.Set.mem (NamedDecl.get_id d) hyps) (Environ.named_context env) in
  { const_hyps = hyps;
    const_body = result.cook_body;
    const_type = result.cook_type;
    const_body_code = tps;
    const_universes = univs;
    const_relevance = result.cook_relevance;
    const_inline_code = result.cook_inline;
    const_typing_flags = result.cook_flags;
  }

let translate_local_def env _id centry =
  let open Cooking in
  let centry = {
    const_entry_body = centry.secdef_body;
    const_entry_secctx = centry.secdef_secctx;
    const_entry_feedback = centry.secdef_feedback;
    const_entry_type = centry.secdef_type;
    const_entry_universes = Monomorphic_entry;
    const_entry_inline_code = false;
  } in
  let decl = infer_declaration env (DefinitionEntry centry) in
  let typ = decl.cook_type in
  let () = match decl.cook_universes with
  | Monomorphic -> ()
  | Polymorphic _ -> assert false
  in
  let c = match decl.cook_body with
  | Def c -> c
  | Undef _ | Primitive _ | OpaqueDef _ -> assert false
  in
  c, decl.cook_relevance, typ
