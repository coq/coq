(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
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

open Util
open Names
open Constr
open Declarations
open Environ
open Entries
open Univ
open UVars

module NamedDecl = Context.Named.Declaration

(* Checks the section variables for the body.
   Returns the closure of the union with the variables in the type.
*)
let check_section_variables env declared_vars body typ =
  let env_ids = ids_of_named_context_val (named_context_val env) in
  Id.Set.iter (fun id -> if not (Id.Set.mem id env_ids) then Type_errors.error_unbound_var env id) declared_vars;
  if List.is_empty (named_context env) then begin
    assert (Id.Set.is_empty declared_vars);
    declared_vars
  end
  else
  let tyvars = global_vars_set env typ in
  let declared_vars = Environ.really_needed env (Id.Set.union declared_vars tyvars) in
  let () = match body with
  | None -> ()
  | Some body ->
    let ids_def = global_vars_set env body in
    let inferred_vars = Environ.really_needed env (Id.Set.union declared_vars ids_def) in
    if not (Id.Set.subset inferred_vars declared_vars) then
      Type_errors.error_undeclared_used_variables env ~declared_vars ~inferred_vars
  in
  declared_vars

let compute_section_variables env body typ =
  if List.is_empty (named_context env) then
    (* Empty section context: optimization *)
    Id.Set.empty
  else
    let ids =
      Option.fold_right
        (fun c -> Id.Set.union (global_vars_set env c))
        body (global_vars_set env typ) in
    Environ.really_needed env ids

let used_section_variables env declared_hyps body typ =
  let hyps =
    match declared_hyps with
    | None -> compute_section_variables env body typ
    | Some declared -> check_section_variables env declared body typ
  in
  (* Order the variables *)
  List.filter (fun d -> Id.Set.mem (NamedDecl.get_id d) hyps) (Environ.named_context env)

(* Insertion of constants and parameters in environment. *)

type 'a effect_handler =
  env -> Constr.t -> 'a -> (Constr.t * ContextSet.t * int)

let skip_trusted_seff sl b e =
  let rec aux sl b e =
    let open Context.Rel.Declaration in
    if Int.equal sl 0 then b, e
    else match HConstr.kind b with
    | LetIn (n,c,ty,bo) ->
      let c = HConstr.self c in
      let ty = HConstr.self ty in
      aux (sl - 1) bo (Environ.push_rel (LocalDef (n,c,ty)) e)
    | App (hd, args) ->
      let () = assert (Int.equal (Array.length args) 1) in
      begin match HConstr.kind hd with
      | Lambda (n,ty,bo) ->
        let ty = HConstr.self ty in
        aux (sl - 1) bo (Environ.push_rel (LocalAssum (n,ty)) e)
      | _ -> assert false
      end
    | _ -> assert false
    in
  aux sl b e

type typing_context =
  TyCtx of Environ.env * unsafe_type_judgment * Id.Set.t * UVars.sort_level_subst * universes

let process_universes env = function
  | Entries.Monomorphic_entry ->
    env, UVars.empty_sort_subst, UVars.Instance.empty, Monomorphic
  | Entries.Polymorphic_entry uctx ->
    (** [ctx] must contain local universes, such that it has no impact
        on the rest of the graph (up to transitivity). *)
    let env = Environ.push_context ~strict:false uctx env in
    let inst, auctx = UVars.abstract_universes uctx in
    let usubst = UVars.make_instance_subst inst in
    env, usubst, inst, Polymorphic auctx

let check_primitive_type env op_t u t =
  let inft = Typeops.type_of_prim_or_type env u op_t in
  match Conversion.default_conv Conversion.CONV env inft t with
  | Result.Ok () -> ()
  | Result.Error () ->
    Type_errors.error_incorrect_primitive env (make_judge op_t inft) t

let adjust_primitive_univ_entry p auctx = function
  | Monomorphic_entry ->
    assert (AbstractContext.is_empty auctx); (* ensured by ComPrimitive *)
    Monomorphic_entry
  | Polymorphic_entry uctx ->
    assert (not (AbstractContext.is_empty auctx)); (* ensured by ComPrimitive *)
    (* [push_context] will check that the universes aren't repeated in
       the instance so comparing the sizes works. No polymorphic
       primitive uses constraints currently. *)
    if not (AbstractContext.size auctx = UContext.size uctx
            && Constraints.is_empty (UContext.constraints uctx))
    then CErrors.user_err Pp.(str "Incorrect universes for primitive " ++
                                str (CPrimitives.op_or_type_to_string p));
    Polymorphic_entry (UContext.refine_names (AbstractContext.names auctx) uctx)

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

    | Some (typ,univ_entry) ->
      let univ_entry = adjust_primitive_univ_entry p auctx univ_entry in
      let env, usubst, u, univs = process_universes env univ_entry in
      let typ = (Typeops.infer_type env typ).utj_val in
      let () = check_primitive_type env p u typ in
      let typ = Vars.subst_univs_level_constr usubst typ in
      univs, typ
  in
  let body = match p with
    | OT_op op -> Declarations.Primitive op
    | OT_type _ -> Undef None
    | OT_const c -> Def (CPrimitives.body_of_prim_const c)
  in
  (* Primitives not allowed in sections (checked in safe_typing) *)
  assert (List.is_empty (named_context env));
  {
    const_hyps = [];
    const_univ_hyps = Instance.empty;
    const_body = body;
    const_type = typ;
    const_body_code = ();
    const_universes = univs;
    const_relevance = Sorts.Relevant;
    const_inline_code = false;
    const_typing_flags = Environ.typing_flags env;
  }

let infer_symbol env { symb_entry_universes; symb_entry_unfold_fix; symb_entry_type } =
  let env, usubst, _, univs = process_universes env symb_entry_universes in
  let j = Typeops.infer env symb_entry_type in
  let r = Typeops.assumption_of_judgment env j in
  let t = Vars.subst_univs_level_constr usubst j.uj_val in
  {
    const_hyps = [];
    const_univ_hyps = Instance.empty;
    const_body = Symbol symb_entry_unfold_fix;
    const_type = t;
    const_body_code = ();
    const_universes = univs;
    const_relevance = UVars.subst_sort_level_relevance usubst r;
    const_inline_code = false;
    const_typing_flags = Environ.typing_flags env;
  }


let make_univ_hyps = function
  | None -> Instance.empty
  | Some us -> us

let infer_parameter ~sec_univs env entry =
  let env, usubst, _, univs = process_universes env entry.parameter_entry_universes in
  let j = Typeops.infer env entry.parameter_entry_type in
  let r = Typeops.assumption_of_judgment env j in
  let typ = Vars.subst_univs_level_constr usubst j.uj_val in
  let undef = Undef entry.parameter_entry_inline_code in
  let hyps = used_section_variables env entry.parameter_entry_secctx None typ in
  {
    const_hyps = hyps;
    const_univ_hyps = make_univ_hyps sec_univs;
    const_body = undef;
    const_type = typ;
    const_body_code = ();
    const_universes = univs;
    const_relevance = UVars.subst_sort_level_relevance usubst r;
    const_inline_code = false;
    const_typing_flags = Environ.typing_flags env;
  }

let infer_definition ~sec_univs env entry =
  let env, usubst, _, univs = process_universes env entry.definition_entry_universes in
  let hbody = HConstr.of_constr env entry.definition_entry_body in
  let j = Typeops.infer_hconstr env hbody in
  let typ = match entry.definition_entry_type with
    | None ->
      Vars.subst_univs_level_constr usubst j.uj_type
    | Some t ->
      let tj = Typeops.infer_type env t in
      let () = Typeops.check_cast env j DEFAULTcast tj in
      Vars.subst_univs_level_constr usubst tj.utj_val
  in
  let body = Vars.subst_univs_level_constr usubst j.uj_val in
  let hbody = if body == j.uj_val then Some hbody else None in
  let def = Def body in
  let hyps = used_section_variables env entry.definition_entry_secctx (Some body) typ in
  hbody, {
    const_hyps = hyps;
    const_univ_hyps = make_univ_hyps sec_univs;
    const_body = def;
    const_type = typ;
    const_body_code = ();
    const_universes = univs;
    const_relevance = Relevanceops.relevance_of_term env body;
    const_inline_code = entry.definition_entry_inline_code;
    const_typing_flags = Environ.typing_flags env;
  }

(** Definition is opaque (Qed), so we delay the typing of its body. *)
let infer_opaque ~sec_univs env entry =
  let env, usubst, _, univs = process_universes env entry.opaque_entry_universes in
  let typj = Typeops.infer_type env entry.opaque_entry_type in
  let context = TyCtx (env, typj, entry.opaque_entry_secctx, usubst, univs) in
  let def = OpaqueDef () in
  let typ = Vars.subst_univs_level_constr usubst typj.utj_val in
  let hyps = used_section_variables env (Some entry.opaque_entry_secctx) None typ in
  {
    const_hyps = hyps;
    const_univ_hyps = make_univ_hyps sec_univs;
    const_body = def;
    const_type = typ;
    const_body_code = ();
    const_universes = univs;
    const_relevance = UVars.subst_sort_level_relevance usubst @@ Sorts.relevance_of_sort typj.utj_type;
    const_inline_code = false;
    const_typing_flags = Environ.typing_flags env;
  }, context

let check_delayed (type a) (handle : a effect_handler) tyenv (body : a proof_output) =
  let TyCtx (env, tyj, declared, usubst, univs) = tyenv in
  let ((body, uctx), side_eff) = body in
  let (body, uctx', valid_signatures) = handle env body side_eff in
  let uctx = ContextSet.union uctx uctx' in
  let env, univs = match univs with
    | Monomorphic ->
       assert (UVars.is_empty_sort_subst usubst);
       push_context_set uctx env, Opaqueproof.PrivateMonomorphic uctx
    | Polymorphic _ ->
       assert (Int.equal valid_signatures 0);
       push_subgraph uctx env,
       let private_univs = on_snd (subst_univs_level_constraints (snd usubst)) uctx in
       Opaqueproof.PrivatePolymorphic private_univs
  in
  (* Note: non-trivial trusted side-effects only in monomorphic case *)
  let hbody = HConstr.of_constr env body in
  let () =
    let eff_body, eff_env = skip_trusted_seff valid_signatures hbody env in
    let j = Typeops.infer_hconstr eff_env eff_body in
    let () = assert (HConstr.self eff_body == j.uj_val) in
    let j = { uj_val = HConstr.self hbody; uj_type = j.uj_type } in
    Typeops.check_cast eff_env j DEFAULTcast tyj
  in
  let declared =
    if List.is_empty (named_context env) then declared
    else Environ.really_needed env (Id.Set.union declared (global_vars_set env tyj.utj_val))
  in
  let declared' = check_section_variables env declared (Some body) tyj.utj_val in
  let () = assert (Id.Set.equal declared declared') in
  (* Note: non-trivial usubst only in polymorphic case *)
  let def = Vars.subst_univs_level_constr usubst (HConstr.self hbody) in
  let hbody = if def == HConstr.self hbody then Some hbody else None in
  hbody, def, univs

(*s Global and local constant declaration. *)

let infer_local_assum env t =
  let j = Typeops.infer env t in
  let t = Typeops.assumption_of_judgment env j in
    j.uj_val, t

let infer_local_def env _id { secdef_body; secdef_type; } =
  let j = Typeops.infer env secdef_body in
  let typ = match secdef_type with
    | None -> j.uj_type
    | Some typ ->
      let tj = Typeops.infer_type env typ in
      let () = Typeops.check_cast env j DEFAULTcast tj in
      tj.utj_val
  in
  let c = j.uj_val in
  let r = Relevanceops.relevance_of_term env c in
  c, r, typ
