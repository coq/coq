open Pp
open Util
open Names
open Conversion
open Typeops
open Declarations
open Environ

(** {6 Checking constants } *)

let indirect_accessor : (Opaqueproof.opaque -> Constr.t * unit Opaqueproof.delayed_universes) ref =
  ref (fun _ -> assert false)

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

exception BadConstant of Constant.t * Pp.t

let check_constant_declaration env opac kn cb opacify =
  Flags.if_verbose Feedback.msg_notice (str "  checking cst:" ++ Constant.print kn);
  let env = CheckFlags.set_local_flags cb.const_typing_flags env in
  let poly, env =
    match cb.const_universes with
    | Monomorphic ->
      (* Monomorphic universes are stored at the library level, the
         ones in const_universes should not be needed *)
      false, env
    | Polymorphic auctx ->
      let ctx = UVars.AbstractContext.repr auctx in
      (* [env] contains De Bruijn universe variables *)
      let env = push_context ~strict:false ctx env in
      true, env
  in
  let ty = cb.const_type in
  let jty = infer_type env ty in
  if not (Sorts.relevance_equal cb.const_relevance (Sorts.relevance_of_sort jty.utj_type))
  then raise Pp.(BadConstant (kn, str "incorrect const_relevance"));
  let body, env = match cb.const_body with
    | Undef _ | Primitive _ | Symbol _ -> None, env
    | Def c -> Some c, env
    | OpaqueDef o ->
      let c, u = !indirect_accessor o in
      let env = match u, cb.const_universes with
        | Opaqueproof.PrivateMonomorphic (), Monomorphic -> env
        | Opaqueproof.PrivatePolymorphic local, Polymorphic _ ->
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

let check_instance_mask udecl umask lincheck =
  match udecl, umask with
    | _, None -> lincheck
    | Monomorphic, Some ([||], [||]) -> lincheck
    | Polymorphic uctx, Some (qmask, umask) ->
        let lincheck = Array.fold_left_i (fun i lincheck mask -> Partial_subst.maybe_add_quality mask () lincheck) lincheck qmask in
        let lincheck = Array.fold_left_i (fun i lincheck mask -> Partial_subst.maybe_add_univ mask () lincheck) lincheck umask in
        if (Array.length qmask, Array.length umask) <> UVars.AbstractContext.size uctx then CErrors.anomaly Pp.(str "Bad univ mask length.");
        lincheck
    | _ -> CErrors.anomaly Pp.(str "Bad univ mask length.")

let rec get_holes_profiles env nargs ndecls lincheck el =
  List.fold_left (get_holes_profiles_elim env nargs ndecls) lincheck el

and get_holes_profiles_elim env nargs ndecls lincheck = function
  | PEApp args -> Array.fold_left (get_holes_profiles_parg env nargs ndecls) lincheck args
  | PECase (ind, u, ret, brs) ->
      let mib, mip = Inductive.lookup_mind_specif env ind in
      let lincheck = check_instance_mask mib.mind_universes u lincheck in
      let lincheck = get_holes_profiles_parg env (nargs + mip.mind_nrealargs + 1) (ndecls + mip.mind_nrealdecls + 1) lincheck ret in
      Array.fold_left3 (fun lincheck nargs_b ndecls_b -> get_holes_profiles_parg env (nargs + nargs_b) (ndecls + ndecls_b) lincheck) lincheck mip.mind_consnrealargs mip.mind_consnrealdecls brs
  | PEProj proj ->
      let () = lookup_projection proj env |> ignore in
      lincheck

and get_holes_profiles_parg env nargs ndecls lincheck = function
  | EHoleIgnored -> lincheck
  | EHole i -> Partial_subst.add_term i nargs lincheck
  | ERigid (h, el) ->
      let lincheck = get_holes_profiles_head env nargs ndecls lincheck h in
      get_holes_profiles env nargs ndecls lincheck el

and get_holes_profiles_head env nargs ndecls lincheck = function
  | PHRel n -> if n <= ndecls then lincheck else Type_errors.error_unbound_rel env n
  | PHSymbol (c, u) ->
      let cb = lookup_constant c env in
      check_instance_mask cb.const_universes u lincheck
  | PHConstr (c, u) ->
      let (mib, _) = Inductive.lookup_mind_specif env (inductive_of_constructor c) in
      check_instance_mask mib.mind_universes u lincheck
  | PHInd (ind, u) ->
      let (mib, _) = Inductive.lookup_mind_specif env ind in
      check_instance_mask mib.mind_universes u lincheck
  | PHInt _  | PHFloat _ -> lincheck
  | PHSort PSSProp -> if Environ.sprop_allowed env then lincheck else Type_errors.error_disallowed_sprop env
  | PHSort PSType io -> Partial_subst.maybe_add_univ io () lincheck
  | PHSort PSQSort (qio, uio) ->
      lincheck
      |> Partial_subst.maybe_add_quality qio ()
      |> Partial_subst.maybe_add_univ uio ()
  | PHSort _ -> lincheck
  | PHLambda (tys, bod) | PHProd (tys, bod) ->
      let lincheck = Array.fold_left_i (fun i -> get_holes_profiles_parg env (nargs + i) (ndecls + i)) lincheck tys in
      let lincheck = get_holes_profiles_parg env (nargs + Array.length tys) (ndecls + Array.length tys) lincheck bod in
      lincheck

let check_rhs env holes_profile rhs =
  let rec check i c = match Constr.kind c with
    | App (f, args) when Constr.isRel f ->
        let n = Constr.destRel f in
        if n <= i then () else
          if n - i > Array.length holes_profile then CErrors.anomaly Pp.(str "Malformed right-hand-side substitution site");
          let d = holes_profile.(n-i-1) in
          if Array.length args >= d then () else CErrors.anomaly Pp.(str "Malformed right-hand-side substitution site")
    | Rel n when n > i ->
        if n - i > Array.length holes_profile then CErrors.anomaly Pp.(str "Malformed right-hand-side substitution site");
        let d = holes_profile.(n-i-1) in
        if d = 0 then () else CErrors.anomaly Pp.(str "Malformed right-hand-side substitution site")
    | _ -> Constr.iter_with_binders succ check i c
  in
  check 0 rhs

let check_rewrite_rule env lab i (symb, rule) =
  Flags.if_verbose Feedback.msg_notice (str "  checking rule:" ++ Label.print lab ++ str"#" ++ Pp.int i);
  let { nvars; lhs_pat; rhs } = rule in
  let symb_cb = Environ.lookup_constant symb env in
  let () =
    match symb_cb.const_body with Symbol _ -> ()
    | _ -> ignore @@ invalid_arg "Rule defined on non-symbol"
  in
  let lincheck = Partial_subst.make nvars in
  let lincheck = check_instance_mask symb_cb.const_universes (fst lhs_pat) lincheck in
  let lincheck = get_holes_profiles env 0 0 lincheck (snd lhs_pat) in
  let holes_profile, _, _ = Partial_subst.to_arrays lincheck in
  let () = check_rhs env holes_profile rhs in
  ()

let check_rewrite_rules_body env lab rrb =
  List.iteri (check_rewrite_rule env lab) rrb.rewrules_rules

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

let rec collect_constants_without_body sign mp accu =
  let collect_field s lab = function
  | SFBconst cb ->
     let c = Constant.make2 mp lab in
     if Declareops.constant_has_body cb then s else Cset.add c s
  | SFBmodule msb -> collect_constants_without_body msb.mod_type (MPdot(mp,lab)) s
  | SFBmind _ | SFBrules _ | SFBmodtype _ -> s in
  match sign with
  | MoreFunctor _ -> Cset.empty  (* currently ignored *)
  | NoFunctor struc ->
     List.fold_left (fun s (lab,mb) -> collect_field s lab mb) accu struc

let rec check_mexpr env opac mse mp_mse res = match mse with
  | MEident mp ->
    let mb = lookup_module mp env in
    let mb = Modops.strengthen_and_subst_module_body mb mp_mse false in
    mb.mod_type, mb.mod_delta
  | MEapply (f,mp) ->
    let sign, delta = check_mexpr env opac f mp_mse res in
    let farg_id, farg_b, fbody_b = Modops.destr_functor sign in
    let mtb = Modops.module_type_of_module (lookup_module mp env) in
    let state = (Environ.universes env, Conversion.checked_universes) in
    let _ : UGraph.t = Subtyping.check_subtypes state env mtb farg_b in
    let subst = Mod_subst.map_mbid farg_id mp Mod_subst.empty_delta_resolver in
    Modops.subst_signature subst fbody_b, Mod_subst.subst_codom_delta_resolver subst delta
  | MEwith _ -> CErrors.user_err Pp.(str "Unsupported 'with' constraint in module implementation")

let rec check_mexpression env opac sign mbtyp mp_mse res = match sign with
  | MEMoreFunctor body ->
    let arg_id, mtb, mbtyp = Modops.destr_functor mbtyp in
    let env' = Modops.add_module_type (MPbound arg_id) mtb env in
    let body, delta = check_mexpression env' opac body mbtyp mp_mse res in
    MoreFunctor(arg_id,mtb,body), delta
  | MENoFunctor me -> check_mexpr env opac me mp_mse res

let rec check_module env opac mp mb opacify =
  Flags.if_verbose Feedback.msg_notice (str "  checking module: " ++ str (ModPath.to_string mp));
  let env = Modops.add_retroknowledge mb.mod_retroknowledge env in
  let opac =
    check_signature env opac mb.mod_type mb.mod_mp mb.mod_delta opacify
  in
  let optsign, opac = match mb.mod_expr with
    | Struct sign_struct ->
      let opacify = collect_constants_without_body mb.mod_type mb.mod_mp opacify in
      (* TODO: a bit wasteful, we recheck the types of parameters twice *)
      let sign_struct = Modops.annotate_struct_body sign_struct mb.mod_type in
      let opac = check_signature env opac sign_struct mb.mod_mp mb.mod_delta opacify in
      Some (sign_struct, mb.mod_delta), opac
    | Algebraic me -> Some (check_mexpression env opac me mb.mod_type mb.mod_mp mb.mod_delta), opac
    | Abstract|FullStruct -> None, opac
  in
  let () = match optsign with
  | None -> ()
  | Some (sign,delta) ->
    let mtb1 = mk_mtb mp sign delta
    and mtb2 = mk_mtb mp mb.mod_type mb.mod_delta in
    let env = Modops.add_module_type mp mtb1 env in
    let state = (Environ.universes env, Conversion.checked_universes) in
    let _ : UGraph.t = Subtyping.check_subtypes state env mtb1 mtb2 in
    ()
  in
  opac

and check_module_type env mty =
  Flags.if_verbose Feedback.msg_notice (str "  checking module type: " ++ str (ModPath.to_string mty.mod_mp));
  let _ : _ Cmap.t =
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
      let opac = check_module env opac (MPdot(mp,lab)) msb opacify in
      Modops.add_module msb env, opac
  | SFBmodtype mty ->
      check_module_type env mty;
      add_modtype mty env, opac
  | SFBrules rrb ->
      check_rewrite_rules_body env lab rrb;
      Environ.add_rewrite_rules rrb.rewrules_rules env, opac

and check_signature env opac sign mp_mse res opacify = match sign with
  | MoreFunctor (arg_id, mtb, body) ->
      check_module_type env mtb;
      let env' = Modops.add_module_type (MPbound arg_id) mtb env in
      let opac = check_signature env' opac body mp_mse res Cset.empty in
      opac
  | NoFunctor struc ->
      let (_:env), opac = List.fold_left (fun (env, opac) (lab,mb) ->
        check_structure_field env opac mp_mse lab res opacify mb) (env, opac) struc
      in
      opac

let check_module env opac mp mb = check_module env opac mp mb Cset.empty
