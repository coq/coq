open Pp
open Util
open Names
open Reduction
open Typeops
open Declarations
open Environ

(** {6 Checking constants } *)

let check_constant_declaration env kn cb =
  Flags.if_verbose Feedback.msg_notice (str "  checking cst:" ++ Constant.print kn);
  (* Locally set the oracle for further typechecking *)
  let oracle = env.env_typing_flags.conv_oracle in
  let env = Environ.set_oracle env cb.const_typing_flags.conv_oracle in
  (* [env'] contains De Bruijn universe variables *)
  let poly, env' =
    match cb.const_universes with
    | Monomorphic_const ctx -> false, push_context_set ~strict:true ctx env
    | Polymorphic_const auctx ->
      let ctx = Univ.AUContext.repr auctx in
      let env = push_context ~strict:false ctx env in
      true, env
  in
  let env' = match cb.const_private_poly_univs, (cb.const_body, poly) with
    | None, _ -> env'
    | Some local, (OpaqueDef _, true) -> push_subgraph local env'
    | Some _, _ -> assert false
  in
  let ty = cb.const_type in
  let _ = infer_type env' ty in
  let () =
    match Environ.body_of_constant_body env cb with
    | Some bd ->
      let j = infer env' (fst bd) in
      conv_leq env' j.uj_type ty
    | None -> ()
  in
  let env =
    if poly then add_constant kn cb env
    else add_constant kn cb env'
  in
  (* Reset the value of the oracle *)
  Environ.set_oracle env oracle

(** {6 Checking modules } *)

(** We currently ignore the [mod_type_alg] and [typ_expr_alg] fields.
    The only delicate part is when [mod_expr] is an algebraic expression :
    we need to expand it before checking it is indeed a subtype of [mod_type].
    Fortunately, [mod_expr] cannot contain any [MEwith]. *)

let lookup_module mp env =
  try Environ.lookup_module mp env
  with Not_found ->
    failwith ("Unknown module: "^ModPath.to_string mp)

let mk_mtb mp sign delta =
  { mod_mp = mp;
    mod_expr = ();
    mod_type = sign;
    mod_type_alg = None;
    mod_constraints = Univ.ContextSet.empty;
    mod_delta = delta;
    mod_retroknowledge = ModTypeRK; }

let rec check_module env mp mb =
  Flags.if_verbose Feedback.msg_notice (str "  checking module: " ++ str (ModPath.to_string mp));
  let env = Modops.add_retroknowledge mb.mod_retroknowledge env in
  let (_:module_signature) =
    check_signature env mb.mod_type mb.mod_mp mb.mod_delta
  in
  let optsign = match mb.mod_expr with
    |Struct sign -> Some (check_signature env sign mb.mod_mp mb.mod_delta, mb.mod_delta)
    |Algebraic me -> Some (check_mexpression env me mb.mod_mp mb.mod_delta)
    |Abstract|FullStruct -> None
  in
  match optsign with
  |None -> ()
  |Some (sign,delta) ->
    let mtb1 = mk_mtb mp sign delta
    and mtb2 = mk_mtb mp mb.mod_type mb.mod_delta in
    let env = Modops.add_module_type mp mtb1 env in
    let cu = Subtyping.check_subtypes env mtb1 mtb2 in
    if not (Environ.check_constraints cu env) then
      CErrors.user_err Pp.(str "Incorrect universe constraints for module subtyping");

and check_module_type env mty =
  Flags.if_verbose Feedback.msg_notice (str "  checking module type: " ++ str (ModPath.to_string mty.mod_mp));
  let (_:module_signature) =
    check_signature env mty.mod_type mty.mod_mp mty.mod_delta in
  ()

and check_structure_field env mp lab res = function
  | SFBconst cb ->
      let c = Constant.make2 mp lab in
      check_constant_declaration env c cb
  | SFBmind mib ->
      let kn = KerName.make mp lab in
      let kn = Mod_subst.mind_of_delta_kn res kn in
      CheckInductive.check_inductive env kn mib
  | SFBmodule msb ->
      let () = check_module env (MPdot(mp,lab)) msb in
      Modops.add_module msb env
  | SFBmodtype mty ->
      check_module_type env mty;
      add_modtype mty env

and check_mexpr env mse mp_mse res = match mse with
  | MEident mp ->
      let mb = lookup_module mp env in
      let mb = Modops.strengthen_and_subst_mb mb mp_mse false in
      mb.mod_type, mb.mod_delta
  | MEapply (f,mp) ->
      let sign, delta = check_mexpr env f mp_mse res in
      let farg_id, farg_b, fbody_b = Modops.destr_functor sign in
      let mtb = Modops.module_type_of_module (lookup_module mp env) in
      let cu = Subtyping.check_subtypes env mtb farg_b in
      if not (Environ.check_constraints cu env) then
        CErrors.user_err Pp.(str "Incorrect universe constraints for module subtyping");
      let subst = Mod_subst.map_mbid farg_id mp Mod_subst.empty_delta_resolver in
      Modops.subst_signature subst fbody_b, Mod_subst.subst_codom_delta_resolver subst delta
  | MEwith _ -> CErrors.user_err Pp.(str "Unsupported 'with' constraint in module implementation")


and check_mexpression env sign mp_mse res = match sign with
  | MoreFunctor (arg_id, mtb, body) ->
      check_module_type env mtb;
      let env' = Modops.add_module_type (MPbound arg_id) mtb env in
      let body, delta = check_mexpression env' body mp_mse res in
      MoreFunctor(arg_id,mtb,body), delta
  | NoFunctor me -> check_mexpr env me mp_mse res

and check_signature env sign mp_mse res = match sign with
  | MoreFunctor (arg_id, mtb, body) ->
      check_module_type env mtb;
      let env' = Modops.add_module_type (MPbound arg_id) mtb env in
      let body = check_signature env' body mp_mse res in
      MoreFunctor(arg_id,mtb,body)
  | NoFunctor struc ->
      let (_:env) = List.fold_left (fun env (lab,mb) ->
	check_structure_field env mp_mse lab res mb) env struc
      in
      NoFunctor struc
