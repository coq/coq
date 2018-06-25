open Pp
open Util
open Names
open Cic
open Reduction
open Typeops
open Indtypes
open Modops
open Subtyping
open Declarations
open Environ

(** {6 Checking constants } *)

let check_constant_declaration env kn cb =
  Flags.if_verbose Feedback.msg_notice (str "  checking cst:" ++ prcon kn);
  (** Locally set the oracle for further typechecking *)
  let oracle = env.env_conv_oracle in
  let env = Environ.set_oracle env cb.const_typing_flags.conv_oracle in
  (** [env'] contains De Bruijn universe variables *)
  let env' =
    match cb.const_universes with
    | Monomorphic_const ctx -> push_context_set ~strict:true ctx env
    | Polymorphic_const auctx ->
      let ctx = Univ.AUContext.repr auctx in
      push_context ~strict:false ctx env
  in
  let ty = cb.const_type in
  let _ = infer_type env' ty in
  let () =
    match body_of_constant cb with
    | Some bd ->
      let j = infer env' bd in
      conv_leq env' j ty
    | None -> ()
  in
  let env =
    if constant_is_polymorphic cb then add_constant kn cb env
    else add_constant kn cb env'
  in
  (** Reset the value of the oracle *)
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
  let (_:module_signature) =
    check_signature env mb.mod_type mb.mod_mp mb.mod_delta
  in
  let optsign = match mb.mod_expr with
    |Struct sign -> Some (check_signature env sign mb.mod_mp mb.mod_delta)
    |Algebraic me -> Some (check_mexpression env me mb.mod_mp mb.mod_delta)
    |Abstract|FullStruct -> None
  in
  match optsign with
  |None -> ()
  |Some sign ->
    let mtb1 = mk_mtb mp sign mb.mod_delta
    and mtb2 = mk_mtb mp mb.mod_type mb.mod_delta in
    let env = add_module_type mp mtb1 env in
    Subtyping.check_subtypes env mtb1 mtb2

and check_module_type env mty =
  let (_:module_signature) =
    check_signature env mty.mod_type mty.mod_mp mty.mod_delta in
  ()

and check_structure_field env mp lab res = function
  | SFBconst cb ->
      let c = Constant.make2 mp lab in
      check_constant_declaration env c cb
  | SFBmind mib ->
      let kn = MutInd.make2 mp lab in
      let kn = mind_of_delta res kn in
      Indtypes.check_inductive env kn mib
  | SFBmodule msb ->
      let () = check_module env (MPdot(mp,lab)) msb in
      Modops.add_module msb env
  | SFBmodtype mty ->
      check_module_type env mty;
      add_modtype (MPdot(mp,lab)) mty env

and check_mexpr env mse mp_mse res = match mse with
  | MEident mp ->
      let mb = lookup_module mp env in
      (subst_and_strengthen mb mp_mse).mod_type
  | MEapply (f,mp) ->
      let sign = check_mexpr env f mp_mse res in
      let farg_id, farg_b, fbody_b = destr_functor sign in
      let mtb = module_type_of_module (Some mp) (lookup_module mp env) in
      check_subtypes env mtb farg_b;
      subst_signature (map_mbid farg_id mp) fbody_b
  | MEwith _ -> error_with_module ()

and check_mexpression env sign mp_mse res = match sign with
  | MoreFunctor (arg_id, mtb, body) ->
      check_module_type env mtb;
      let env' = add_module_type (MPbound arg_id) mtb env in
      let body = check_mexpression env' body mp_mse res in
      MoreFunctor(arg_id,mtb,body)
  | NoFunctor me -> check_mexpr env me mp_mse res

and check_signature env sign mp_mse res = match sign with
  | MoreFunctor (arg_id, mtb, body) ->
      check_module_type env mtb;
      let env' = add_module_type (MPbound arg_id) mtb env in
      let body = check_signature env' body mp_mse res in
      MoreFunctor(arg_id,mtb,body)
  | NoFunctor struc ->
      let (_:env) = List.fold_left (fun env (lab,mb) ->
	check_structure_field env mp_mse lab res mb) env struc
      in
      NoFunctor struc
