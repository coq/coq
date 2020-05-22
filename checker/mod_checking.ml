open Pp
open Util
open Names
open Reduction
open Typeops
open Declarations
open Environ

(** {6 Checking constants } *)

let indirect_accessor = ref {
  Opaqueproof.access_proof = (fun _ _ -> assert false);
  Opaqueproof.access_discharge = (fun _ _ -> assert false);
}

let set_indirect_accessor f = indirect_accessor := f

let register_opacified_constant env opac kn cb =
  let rec gather_consts s c =
    match Constr.kind c with
    | Constr.Const (c, _) -> Cset.add c s
    | _ -> Constr.fold gather_consts s c
  in
  let wo_body =
    Cset.fold
      (fun kn s ->
        if Declareops.constant_has_body (lookup_constant kn env) then s else
          match Cmap.find_opt kn opac with
          | None -> Cset.add kn s
          | Some s' -> Cset.union s' s)
      (gather_consts Cset.empty cb)
      Cset.empty
  in
  Cmap.add kn wo_body opac

let check_constant_declaration env opac kn cb opacify =
  Flags.if_verbose Feedback.msg_notice (str "  checking cst:" ++ Constant.print kn);
  let env = CheckFlags.set_local_flags cb.const_typing_flags env in
  let poly, env =
    match cb.const_universes with
    | Monomorphic ctx ->
      (* Monomorphic universes are stored at the library level, the
         ones in const_universes should not be needed *)
      false, env
    | Polymorphic auctx ->
      let ctx = Univ.AUContext.repr auctx in
      (* [env] contains De Bruijn universe variables *)
      let env = push_context ~strict:false ctx env in
      true, env
  in
  let ty = cb.const_type in
  let _ = infer_type env ty in
  let otab = Environ.opaque_tables env in
  let body, env = match cb.const_body with
    | Undef _ | Primitive _ -> None, env
    | Def c -> Some (Mod_subst.force_constr c), env
    | OpaqueDef o ->
      let c, u = Opaqueproof.force_proof !indirect_accessor otab o in
      let env = match u, cb.const_universes with
        | Opaqueproof.PrivateMonomorphic (), Monomorphic _ -> env
        | Opaqueproof.PrivatePolymorphic (_, local), Polymorphic _ ->
          push_subgraph local env
        | _ -> assert false
      in
      Some c, env
  in
  let () =
    match body with
    | Some bd ->
      let j = infer env bd in
      (try conv_leq env j.uj_type ty
       with NotConvertible -> Type_errors.error_actual_type env j ty)
    | None -> ()
  in
  match body with
  | Some body when opacify -> register_opacified_constant env opac kn body
  | Some _ | None -> opac

let check_constant_declaration env opac kn cb opacify =
  let opac = check_constant_declaration env opac kn cb opacify in
  Environ.add_constant kn cb env, opac

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
    mod_delta = delta;
    mod_retroknowledge = ModTypeRK; }

let collect_constants_without_body sign mp =
  let collect_sf s lab = function
  | SFBconst cb ->
     let c = Constant.make2 mp lab in
     if Declareops.constant_has_body cb then s else Cset.add c s
  | SFBmind _ | SFBmodule _ | SFBmodtype _ -> s in
  match sign with
  | MoreFunctor _ -> Cset.empty  (* currently ignored *)
  | NoFunctor struc ->
     List.fold_left (fun s (lab,mb) -> collect_sf s lab mb) Cset.empty struc

let rec check_module env opac mp mb =
  Flags.if_verbose Feedback.msg_notice (str "  checking module: " ++ str (ModPath.to_string mp));
  let env = Modops.add_retroknowledge mb.mod_retroknowledge env in
  let sign, opac =
    check_signature env opac mb.mod_type mb.mod_mp mb.mod_delta Cset.empty
  in
  let optsign, opac = match mb.mod_expr with
    |Struct sign_struct ->
      let opacify = collect_constants_without_body sign mb.mod_mp in
      let sign, opac = check_signature env opac sign_struct mb.mod_mp mb.mod_delta opacify in
      Some (sign, mb.mod_delta), opac
    |Algebraic me -> Some (check_mexpression env opac me mb.mod_mp mb.mod_delta), opac
    |Abstract|FullStruct -> None, opac
  in
  let () = match optsign with
  |None -> ()
  |Some (sign,delta) ->
    let mtb1 = mk_mtb mp sign delta
    and mtb2 = mk_mtb mp mb.mod_type mb.mod_delta in
    let env = Modops.add_module_type mp mtb1 env in
    let cu = Subtyping.check_subtypes env mtb1 mtb2 in
    if not (Environ.check_constraints cu env) then
      CErrors.user_err Pp.(str "Incorrect universe constraints for module subtyping");
  in
  opac

and check_module_type env mty =
  Flags.if_verbose Feedback.msg_notice (str "  checking module type: " ++ str (ModPath.to_string mty.mod_mp));
  let (_:module_signature), _ =
    check_signature env Cmap.empty mty.mod_type mty.mod_mp mty.mod_delta Cset.empty in
  ()

and check_structure_field env opac mp lab res opacify = function
  | SFBconst cb ->
      let c = Constant.make2 mp lab in
      check_constant_declaration env opac c cb (Cset.mem c opacify)
  | SFBmind mib ->
      let kn = KerName.make mp lab in
      let kn = Mod_subst.mind_of_delta_kn res kn in
      CheckInductive.check_inductive env kn mib, opac
  | SFBmodule msb ->
      let opac = check_module env opac (MPdot(mp,lab)) msb in
      Modops.add_module msb env, opac
  | SFBmodtype mty ->
      check_module_type env mty;
      add_modtype mty env, opac

and check_mexpr env opac mse mp_mse res = match mse with
  | MEident mp ->
      let mb = lookup_module mp env in
      let mb = Modops.strengthen_and_subst_mb mb mp_mse false in
      mb.mod_type, mb.mod_delta
  | MEapply (f,mp) ->
      let sign, delta = check_mexpr env opac f mp_mse res in
      let farg_id, farg_b, fbody_b = Modops.destr_functor sign in
      let mtb = Modops.module_type_of_module (lookup_module mp env) in
      let cu = Subtyping.check_subtypes env mtb farg_b in
      if not (Environ.check_constraints cu env) then
        CErrors.user_err Pp.(str "Incorrect universe constraints for module subtyping");
      let subst = Mod_subst.map_mbid farg_id mp Mod_subst.empty_delta_resolver in
      Modops.subst_signature subst fbody_b, Mod_subst.subst_codom_delta_resolver subst delta
  | MEwith _ -> CErrors.user_err Pp.(str "Unsupported 'with' constraint in module implementation")


and check_mexpression env opac sign mp_mse res = match sign with
  | MoreFunctor (arg_id, mtb, body) ->
      check_module_type env mtb;
      let env' = Modops.add_module_type (MPbound arg_id) mtb env in
      let body, delta = check_mexpression env' opac body mp_mse res in
      MoreFunctor(arg_id,mtb,body), delta
  | NoFunctor me -> check_mexpr env opac me mp_mse res

and check_signature env opac sign mp_mse res opacify = match sign with
  | MoreFunctor (arg_id, mtb, body) ->
      check_module_type env mtb;
      let env' = Modops.add_module_type (MPbound arg_id) mtb env in
      let body, opac = check_signature env' opac body mp_mse res Cset.empty in
      MoreFunctor(arg_id,mtb,body), opac
  | NoFunctor struc ->
      let (_:env), opac = List.fold_left (fun (env, opac) (lab,mb) ->
        check_structure_field env opac mp_mse lab res opacify mb) (env, opac) struc
      in
      NoFunctor struc, opac
