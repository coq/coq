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
  let type_vars = global_vars_set env typ in
  let declared_vars = Environ.really_needed env (Id.Set.union declared_vars type_vars) in
  let () = match body with
  | None -> ()
  | Some body ->
    let ids_def = global_vars_set env body in
    let inferred_vars = Environ.really_needed env (Id.Set.union type_vars ids_def) in
    if not (Id.Set.subset inferred_vars declared_vars) then
      Type_errors.error_undeclared_used_variables env ~declared_vars ~type_vars ~inferred_vars
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
  env -> Constr.t -> 'a -> (Constr.t * Univ.ContextSet.t * int)

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

type typing_context_universes =
  | Monomorphic
  | Polymorphic of universes

type typing_context =
  TyCtx of Environ.env * unsafe_type_judgment * Id.Set.t * typing_context_universes

type pre_universes =
  | PreMonomorphic
  | PrePolymorphic of AbstractContext.t * InferCumulativity.pre_variances option

let compute_section_universes ctx body typ =
  let used = Vars.universes_of_constr typ in
  let used = Option.cata (Vars.universes_of_constr ~init:used) used body in
  let used = Vars.universes_of_named_context ~init:used ctx in
  used

let _used_section_universes sec_univs univs ctx body typ =
  match sec_univs with
  | None -> []
  | Some sec_univs -> (* sec_univs represents all universes quantified in enclosing sections *)
    match univs with
    | Entries.Monomorphic_entry -> []
    | Entries.Polymorphic_entry (uctx, _) ->
      let used = compute_section_universes ctx body typ in
      let _qcstrs, ucstrs = UContext.constraints uctx in
      let used = Univ.UnivConstraints.levels ~init:used ucstrs in
      UVars.restrict_contexts sec_univs used

let process_universes env ?sec_univs = function
  | Entries.Monomorphic_entry ->
    env, UVars.Instance.empty, PreMonomorphic
  | Entries.Polymorphic_entry (auctx, variances) ->
    if AbstractContext.is_empty auctx && Option.is_empty sec_univs then
      env, UVars.Instance.empty, PreMonomorphic
    else
    (** [ctx] must contain local universes, such that it has no impact
        on the rest of the graph (up to transitivity). *)
    let ctx = AbstractContext.repr auctx in
    let () = check_ucontext ctx env in
    let env = Environ.push_context ~strict:false ctx env in
    let variances =
      match variances with
      | None -> None
      | Some variances ->
          (* no variance for qualities *)
          let inst = UContext.instance (AbstractContext.repr auctx) in
          let _, inst = UVars.LevelInstance.to_array inst in
          let univs =
            match variances with
            | Check_variances variances ->
              Array.map2 (fun a b -> a,Some b) inst (UVars.Variances.repr variances)
            | Infer_variances -> Array.map (fun a -> a,None) inst
          in
          Some univs
    in
    env, UVars.make_abstract_instance auctx, PrePolymorphic (auctx, variances)

let check_primitive_type env op_t u t =
  let inft = Typeops.type_of_prim_or_type env u op_t in
  match Conversion.default_conv Conversion.CONV env inft t with
  | Result.Ok () -> ()
  | Result.Error () ->
    Type_errors.error_incorrect_primitive env (make_judge op_t inft) t

let compatible_variance_entry v e =
  match v, e with
  | None, None -> true
  | Some _, Some Infer_variances -> true
  | Some v, Some (Check_variances v') -> UVars.Variances.equal_cumul v v'
  | None, Some _ -> false
  | Some _, None -> false

let pr_infv = function
  | Infer_variances -> Pp.str "inferred variances"
  | Check_variances v -> Variances.pr v

let adjust_primitive_univ_entry p auctx variances = function
  | Monomorphic_entry ->
    assert (AbstractContext.is_empty auctx && Option.is_empty variances); (* ensured by ComPrimitive *)
    Monomorphic_entry
  | Polymorphic_entry (uctx, variances') ->
    assert (not (AbstractContext.is_empty auctx)); (* ensured by ComPrimitive *)
    (* [push_context] will check that the universes aren't repeated in
       the instance so comparing the sizes works. No polymorphic
       primitive uses constraints currently. *)
    if not (AbstractContext.size auctx = AbstractContext.size uctx
            && PConstraints.is_empty (AbstractContext.constraints uctx))
    then CErrors.user_err Pp.(str "Incorrect universes for primitive " ++
                                str (CPrimitives.op_or_type_to_string p));
    if not (compatible_variance_entry variances variances') then
      CErrors.user_err Pp.(str "Incorrect universe variances for primitive " ++
        str (CPrimitives.op_or_type_to_string p) ++ str", inferred: " ++
        (match variances' with None -> str" None" | Some e -> pr_infv e) ++ str " expected: " ++
        (match variances with None -> str" None" | Some e -> Variances.pr e));
    Polymorphic_entry (AbstractContext.refine_names (AbstractContext.names auctx) uctx, Option.map (fun x -> Check_variances x) variances)

let on_variances fn = function
  | PreMonomorphic -> Monomorphic, None
  | PrePolymorphic (uctx, None) -> Polymorphic (uctx, None), None
  | PrePolymorphic (uctx, Some variances) ->
    let variances, sec_variances = fn variances in
    Polymorphic (uctx, Some variances), sec_variances

let to_universes = function
  | Monomorphic -> (AbstractContext.empty, None)
  | Polymorphic univs -> univs

let infer_primitive env { prim_entry_type = utyp; prim_entry_content = p } =
  let open CPrimitives in
  let auctx, variances = CPrimitives.op_or_type_univs p in
  let univs, typ =
    match utyp with
    | None ->
      let u = Instance.of_level_instance (UContext.instance (AbstractContext.repr auctx)) in
      let typ = Typeops.type_of_prim_or_type env u p in
      let univs = (auctx, variances) in
      univs, typ

    | Some (typ, univ_entry) ->
      let univ_entry = adjust_primitive_univ_entry p auctx variances univ_entry in
      let env, u, univs = process_universes env univ_entry in
      let typ = (Typeops.infer_type env typ).utj_val in
      let () = check_primitive_type env p u typ in
      let univs, sec_variances =
        on_variances (InferCumulativity.infer_definition env ~in_ctx:None (* No section possible *)
          ~sec_univs:None
          ~evars:(CClosure.default_evar_handler env) ~infer_in_type:false
          ~typ ?body:None) univs
      in
      assert (Option.is_empty sec_variances);
      to_universes univs, typ
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
    const_univ_ctx = [];
    const_univ_hyps = UVars.LevelInstance.empty;
    const_body = body;
    const_type = typ;
    const_body_code = ();
    const_universes = univs;
    const_sec_variance = None;
    const_relevance = Sorts.Relevant;
    const_inline_code = false;
    const_typing_flags = Environ.typing_flags env;
    const_def_height = None
  }

let infer_symbol env { symb_entry_universes; symb_entry_unfold_fix; symb_entry_type } =
  let env, _, univs = process_universes env symb_entry_universes in
  let j = Typeops.infer env symb_entry_type in
  let r = Typeops.assumption_of_judgment env j in
  let univs, sec_variances =
    on_variances (InferCumulativity.infer_definition env ~in_ctx:None ~sec_univs:None
       ?evars:None ~infer_in_type:false ~typ:j.uj_val ?body:None) univs
  in
  assert (Option.is_empty sec_variances);
  {
    const_hyps = [];
    const_univ_ctx = [];
    const_univ_hyps = UVars.LevelInstance.empty;
    const_body = Symbol symb_entry_unfold_fix;
    const_type = j.uj_val;
    const_body_code = ();
    const_universes = to_universes univs;
    const_relevance = r;
    const_sec_variance = None;
    const_inline_code = false;
    const_typing_flags = Environ.typing_flags env;
    const_def_height = None;
  }

let sec_univs_instance secunivs =
  List.fold_right (fun uctx acc -> LevelInstance.append acc (UContext.instance uctx)) secunivs LevelInstance.empty

let infer_parameter ~sec_univs env entry =
  let env, _, univs = process_universes env ?sec_univs entry.parameter_entry_universes in
  let typ = entry.parameter_entry_type in
  let j = Typeops.infer env typ in
  let r = Typeops.assumption_of_judgment env j in
  let typ = j.uj_val in
  let undef = Undef entry.parameter_entry_inline_code in
  let hyps = used_section_variables env entry.parameter_entry_secctx None typ in
  let sec_univs = _used_section_universes sec_univs entry.parameter_entry_universes hyps None typ in
  let sec_univs_instance = sec_univs_instance sec_univs in
  let univs, sec_variances = on_variances (InferCumulativity.infer_definition env ?evars:None
    ~infer_in_type:false ~in_ctx:(Some hyps) ~sec_univs:(Some sec_univs_instance) ~typ ?body:None) univs in
  {
    const_hyps = hyps;
    const_univ_ctx = sec_univs;
    const_univ_hyps = sec_univs_instance;
    const_body = undef;
    const_type = typ;
    const_body_code = ();
    const_universes = to_universes univs;
    const_relevance = r;
    const_sec_variance = sec_variances;
    const_inline_code = false;
    const_typing_flags = Environ.typing_flags env;
    const_def_height = None;
  }

let _pr_pre_universes univs =
  let open Pp in
  match univs with
  | PreMonomorphic -> mt ()
  | PrePolymorphic (uctx, variances) ->
    let variances = Option.map (InferCumulativity.of_variance_occurrences ~infer_in_type:false) variances in
    let prv = pr_opt (InferCumulativity.pr_variances Univ.Level.raw_pr) variances in
    UVars.AbstractContext.pr Sorts.raw_printer uctx ++ str " variances: " ++ prv

let infer_definition ~sec_univs env entry =
  let env, _, univs = process_universes env ?sec_univs entry.definition_entry_universes in
  let body = entry.definition_entry_body in
  let hbody = HConstr.of_constr env body in
  let j = Typeops.infer_hconstr env hbody in
  let typ = match entry.definition_entry_type with
    | None ->
      j.uj_type
    | Some t ->
      let tj = Typeops.infer_type env t in
      let () = Typeops.check_cast env j DEFAULTcast tj in
      tj.utj_val
  in
  let body = j.uj_val in
  let hbody = Some hbody in
  let def = Def body in
  let def_h = Environ.constant_definitional_height env def in
  let hyps = used_section_variables env entry.definition_entry_secctx (Some body) typ in
  let sec_univs = _used_section_universes sec_univs entry.definition_entry_universes hyps (Some body) typ in
  let sec_univs_instance = sec_univs_instance sec_univs in
  let univs, sec_variance = on_variances (InferCumulativity.infer_definition env ?evars:None
    ~infer_in_type:(Option.is_empty entry.definition_entry_type) ~in_ctx:(Some hyps)
    ~sec_univs:(Some sec_univs_instance) ~typ ~body) univs in
  hbody, {
    const_hyps = hyps;
    const_univ_ctx = sec_univs;
    const_univ_hyps = sec_univs_instance;
    const_body = def;
    const_type = typ;
    const_body_code = ();
    const_universes = to_universes univs;
    const_sec_variance = sec_variance;
    const_relevance = Relevanceops.relevance_of_term env body;
    const_inline_code = entry.definition_entry_inline_code;
    const_typing_flags = Environ.typing_flags env;
    const_def_height = Some def_h
  }

(** Definition is opaque (Qed), so we delay the typing of its body. *)
let infer_opaque ~sec_univs env entry =
  let env, _, univs = process_universes env ?sec_univs entry.opaque_entry_universes in
  let typ = entry.opaque_entry_type in
  let typj = Typeops.infer_type env typ in
  let typ = typj.utj_val in
  let hyps = used_section_variables env (Some entry.opaque_entry_secctx) None typ in
  let sec_univs = _used_section_universes sec_univs entry.opaque_entry_universes hyps None typ in
  let sec_univs_instance = sec_univs_instance sec_univs in
  let univs, sec_variance = on_variances (InferCumulativity.infer_definition env ?evars:None ~infer_in_type:true
     ~in_ctx:(Some hyps) ~sec_univs:(Some sec_univs_instance) ~typ ?body:None) univs in
  let context = TyCtx (env, typj, entry.opaque_entry_secctx, univs) in
  let def = OpaqueDef () in
  {
    const_hyps = hyps;
    const_univ_ctx = sec_univs;
    const_univ_hyps = sec_univs_instance;
    const_body = def;
    const_type = typ;
    const_body_code = ();
    const_universes = to_universes univs;
    const_sec_variance = sec_variance;
    const_relevance = Sorts.relevance_of_sort typj.utj_type;
    const_inline_code = false;
    const_typing_flags = Environ.typing_flags env;
    const_def_height = None
  }, context

let check_delayed (type a) (handle : a effect_handler) tyenv (body : a proof_output) =
  let TyCtx (env, tyj, declared, univs) = tyenv in
  let ((body, uctx), side_eff) = body in
  let (body, uctx', valid_signatures) = handle env body side_eff in
  let uctx = Univ.ContextSet.union uctx uctx' in
  let env, univs = match univs with
    | Monomorphic ->
       push_context_set uctx env, Opaqueproof.PrivateMonomorphic uctx
    | Polymorphic _ ->
       let () = assert (Int.equal valid_signatures 0) in
       push_subgraph uctx env, Opaqueproof.PrivatePolymorphic uctx
  in
  let hbody = HConstr.of_constr env body in
  (* Note: non-trivial trusted side-effects only in monomorphic case *)
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
  let def = HConstr.self hbody in
  let hbody = Some hbody in
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
