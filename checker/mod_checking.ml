open Pp
open Util
open Names
open Conversion
open Declarations
open Mod_declarations
open Environ

(** {6 Checking constants } *)

type axioms = { cset : KerName.Set.t }

let empty_axioms = { cset = KerName.Set.empty }

let constants_of_axioms {cset} = KerName.Set.elements cset

let axioms_add c {cset} = {cset=KerName.Set.add (Constant.user c) cset}

type check_state = {
  st_retro : (int * CPrimitives.prim_ind_ex) Mindmap.t * CPrimitives.prim_type_ex Cmap.t;
}

let empty_state = {
  st_retro = (Mindmap.empty, Cmap.empty);
}

let indirect_accessor : (Opaqueproof.opaque -> Opaqueproof.opaque_proofterm) ref =
  ref (fun _ -> assert false)

let set_indirect_accessor f = indirect_accessor := f

exception BadConstant of Constant.t * Pp.t

let check_constant_declaration env st kn cb =
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
      let () = check_ucontext ctx env in
      let env = push_context ~strict:false ctx env in
      true, env
  in
  let ty = cb.const_type in
  let jty = Typeops.infer_type env ty in
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
      let j = Typeops.infer env bd in
      begin match conv_leq env j.uj_type ty with
      | Result.Ok () -> ()
      | Result.Error () -> Type_errors.error_actual_type env j ty
      end
    | None -> ()
  in
  let retro, st = match Cmap.find_opt kn (snd st.st_retro) with
  | None -> None, st
  | Some retro ->
    let (ind_retro, cst_retro) = st.st_retro in
    let st = { st_retro = (ind_retro, Cmap.remove kn cst_retro) } in
    Some retro, st
  in
  retro, st

let check_constant_declaration env st kn cb =
  let retro, st = NewProfile.profile "check_constant" ~args:(fun () ->
      [("name", `String (Constant.to_string kn))])
      (fun () -> check_constant_declaration env st kn cb)
      ()
  in
  let env = Environ.add_constant kn cb env in
  let env = match retro with
  | None -> env
  | Some (CPrimitives.PTE prm) ->
    (* TODO: Some checking is performed by this function, but it looks too lightweight *)
    Primred.add_retroknowledge env (Retroknowledge.Register_type (prm, kn))
  in
  env, st

let check_quality_mask env qmask lincheck =
  let open Sorts.Quality in
  match qmask with
  | PQConstant QSProp -> if Environ.sprop_allowed env then lincheck else Type_errors.error_not_allowed_sprop env
  | PQConstant (QProp | QType) | PQGlobal _ -> lincheck
  | PQVar qio -> Partial_subst.maybe_add_quality qio () lincheck

let check_instance_mask env udecl umask lincheck =
  match udecl, umask with
    | Monomorphic, ([||], [||]) -> lincheck
    | Polymorphic uctx, (qmask, umask) ->
        let lincheck = Array.fold_left_i (fun i lincheck mask -> check_quality_mask env mask lincheck) lincheck qmask in
        let lincheck = Array.fold_left_i (fun i lincheck mask -> Partial_subst.maybe_add_univ mask () lincheck) lincheck umask in
        if (Array.length qmask, Array.length umask) <> UVars.AbstractContext.size uctx then CErrors.anomaly Pp.(str "Bad univ mask length.");
        lincheck
    | _ -> CErrors.anomaly Pp.(str "Bad univ mask length.")

let rec get_holes_profiles env nargs ndecls lincheck el =
  List.fold_left (get_holes_profiles_elim env nargs ndecls) lincheck el

and get_holes_profiles_elim env nargs ndecls lincheck = function
  | PEApp args -> Array.fold_left (get_holes_profiles_parg env nargs ndecls) lincheck args
  | PECase (ind, ret, brs) ->
      let mib, mip = Inductive.lookup_mind_specif env ind in
      let lincheck = get_holes_profiles_parg env (nargs + mip.mind_nrealargs + 1) (ndecls + mip.mind_nrealdecls + 1) lincheck ret in
      Array.fold_left3 (fun lincheck nargs_b ndecls_b -> get_holes_profiles_parg env (nargs + nargs_b) (ndecls + ndecls_b) lincheck) lincheck mip.mind_consnrealargs mip.mind_consnrealdecls brs
  | PEProj proj ->
      let () = lookup_projection (Projection.make proj false) env |> ignore in
      lincheck

and get_holes_profiles_headelim env nargs ndecls lincheck (h, el) =
  let lincheck = get_holes_profiles_head env nargs ndecls lincheck h in
  get_holes_profiles env nargs ndecls lincheck el

and get_holes_profiles_parg env nargs ndecls lincheck = function
  | EHoleIgnored -> lincheck
  | EHole i -> Partial_subst.add_term i nargs lincheck
  | ERigid hel ->
      get_holes_profiles_headelim env nargs ndecls lincheck hel

and get_holes_profiles_head env nargs ndecls lincheck = function
  | PHRel n -> if n <= ndecls then lincheck else Type_errors.error_unbound_rel env n
  | PHSymbol (c, u) ->
      let cb = lookup_constant c env in
      check_instance_mask env cb.const_universes u lincheck
  | PHConstr (c, u) ->
      let (mib, _) = Inductive.lookup_mind_specif env (inductive_of_constructor c) in
      check_instance_mask env mib.mind_universes u lincheck
  | PHInd (ind, u) ->
      let (mib, _) = Inductive.lookup_mind_specif env ind in
      check_instance_mask env mib.mind_universes u lincheck
  | PHInt _  | PHFloat _ | PHString _ -> lincheck
  | PHSort PSSProp -> if Environ.sprop_allowed env then lincheck else Type_errors.error_not_allowed_sprop env
  | PHSort PSGlobal (_, io)
  | PHSort PSType io -> Partial_subst.maybe_add_univ io () lincheck
  | PHSort PSQSort (qio, uio) ->
      lincheck
      |> Partial_subst.maybe_add_quality qio ()
      |> Partial_subst.maybe_add_univ uio ()
  | PHSort _ -> lincheck
  | PHLambda (tys, bod) ->
      let lincheck = Array.fold_left_i (fun i -> get_holes_profiles_parg env (nargs + i) (ndecls + i)) lincheck tys in
      let lincheck = get_holes_profiles_headelim env (nargs + Array.length tys) (ndecls + Array.length tys) lincheck bod in
      lincheck
  | PHProd (tys, bod) ->
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
  Flags.if_verbose Feedback.msg_notice (str "  checking rule:" ++ Id.print lab ++ str"#" ++ Pp.int i);
  let { nvars; lhs_pat; rhs } = rule in
  let symb_cb = Environ.lookup_constant symb env in
  let () =
    match symb_cb.const_body with Symbol _ -> ()
    | _ -> ignore @@ invalid_arg "Rule defined on non-symbol"
  in
  let lincheck = Partial_subst.make nvars in
  let lincheck = check_instance_mask env symb_cb.const_universes (fst lhs_pat) lincheck in
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

let mk_mtb sign delta = Mod_declarations.make_module_type sign delta

let rec check_mexpr env mse mp_mse res = match mse with
  | MEident mp ->
    let mb = lookup_module mp env in
    let mb = Modops.strengthen_and_subst_module_body mp mb mp_mse false in
    mod_type mb, mod_delta mb
  | MEapply (f,mp) ->
    let sign, delta = check_mexpr env f mp_mse res in
    let farg_id, farg_b, fbody_b = Modops.destr_functor sign in
    let state = (Environ.universes env, Conversion.checked_universes) in
    let _ : UGraph.t = Subtyping.check_subtypes state env mp (MPbound farg_id) farg_b in
    let mp_delta =
      let mb = lookup_module mp env in
      match mod_type mb with
      | NoFunctor _ -> mod_delta mb
      | MoreFunctor _ -> Mod_subst.empty_delta_resolver mp
    in
    let subst =
      Mod_subst.map_mbid farg_id mp (Mod_subst.of_body_delta_resolver mp_delta)
    in
    Modops.subst_signature subst mp_mse fbody_b, Mod_subst.subst_codom_delta_resolver subst delta
  | MEwith _ -> CErrors.user_err Pp.(str "Unsupported 'with' constraint in module implementation")

let rec check_mexpression env sign mbtyp mp_mse res = match sign with
  | MEMoreFunctor body ->
    let arg_id, mtb, mbtyp = Modops.destr_functor mbtyp in
    let env' = Modops.add_module_parameter arg_id mtb env in
    let body, delta = check_mexpression env' body mbtyp mp_mse res in
    MoreFunctor(arg_id,mtb,body), delta
  | MENoFunctor me -> check_mexpr env me mp_mse res

let rec check_module env st mp (mb : Mod_declarations.module_body) =
  Flags.if_verbose Feedback.msg_notice (str "  checking module: " ++ str (ModPath.to_string mp));
  let delta_mb = mod_delta mb in
  let st =
    check_signature env st (mod_type mb) mp delta_mb
  in
  let optsign, st = match Mod_declarations.mod_expr mb with
    | Struct (reso, sign_struct) ->
      (* TODO: a bit wasteful, we recheck the types of parameters twice *)
      let sign_struct = Modops.annotate_struct_body sign_struct (mod_type mb) in
      (* The implementation is checked in its own right, hence its bytecode is
         compiled too; it is local to this check and never exported. With the VM
         disabled the bytecode is never run, so we skip the recompilation. *)
      let env, sign_struct =
        if !CheckFlags.enable_vm then
          let vmtab, sign_struct =
            Modops.compile_signature env (Environ.vm_library env) mp reso sign_struct in
          Environ.set_vm_library vmtab env, sign_struct
        else env, sign_struct
      in
      let st = check_signature env st sign_struct mp reso in
      Some (sign_struct, reso), st
    | Algebraic me -> Some (check_mexpression env me (mod_type mb) mp delta_mb), st
    | Abstract|FullStruct -> None, st
  in
  let () = match optsign with
  | None -> ()
  | Some (sign,delta) ->
    let mtb1 = mk_mtb sign (Mod_subst.of_body_delta_resolver delta)
    and mtb2 = mk_mtb (mod_type mb) (Mod_subst.of_body_delta_resolver delta_mb) in
    let state = (Environ.universes env, Conversion.checked_universes) in
    let env = Modops.add_module mp (module_body_of_type mtb1) env in
    let _ : UGraph.t = Subtyping.check_subtypes state env mp mp mtb2 in
    ()
  in
  st

and check_module_type env mp (mty : Mod_declarations.module_type_body) =
  Flags.if_verbose Feedback.msg_notice (str "  checking module type: " ++ str (ModPath.to_string @@ mp));
  let _ : check_state =
    check_signature env empty_state (mod_type mty) mp (mod_delta mty) in
  ()

and check_structure_field : type a. _ -> _ -> _ -> _ -> a Mod_subst.delta_resolver -> _ -> _  =
  fun env st mp lab res -> function
  | SFBconst cb ->
      let kn = KerName.make mp lab in
      let kn = Mod_subst.constant_of_delta_kn res kn in
      check_constant_declaration env st kn cb
  | SFBmind mib ->
      let kn = KerName.make mp lab in
      let kn = Mod_subst.mind_of_delta_kn res kn in
      let retro = Mindmap.find_opt kn (fst st.st_retro) in
      let st = match retro with
      | None -> st
      | Some _ ->
        let (ind_retro, cst_retro) = st.st_retro in
        let st = { st_retro = (Mindmap.remove kn ind_retro, cst_retro) } in
        st
      in
      CheckInductive.check_inductive env kn mib retro, st
  | SFBmodule msb ->
      let mp = MPdot(mp, lab) in
      let st = check_module env st mp msb in
      Modops.add_module mp msb env, st
  | SFBmodtype mty ->
      let mp = MPdot (mp, lab) in
      let () = check_module_type env mp mty in
      add_modtype mp mty env, st
  | SFBrules rrb ->
      check_rewrite_rules_body env lab rrb;
      Environ.add_rewrite_rules rrb.rewrules_rules env, st

and check_signature : type a. _ -> _ -> _ -> _ -> a Mod_subst.delta_resolver -> _ =
  fun env st sign mp_mse res -> match sign with
  | MoreFunctor (arg_id, mtb, body) ->
      let () = check_module_type env (MPbound arg_id) mtb in
      let env' = Modops.add_module_parameter arg_id mtb env in
      let st = check_signature env' st body mp_mse res in
      st
  | NoFunctor struc ->
      let (_:env), st = List.fold_left (fun (env, st) (lab,mb) ->
        check_structure_field env st mp_mse lab res mb) (env, st) struc
      in
      st

let rec collect_module_axioms env axioms mp mb =
  match mod_expr mb with
  | Struct (reso, struc) ->
    (* Module with implementation separate from its type: don't produce axioms from the type *)
    let struc = Modops.annotate_struct_body struc (mod_type mb) in
    collect_signature_axioms env axioms struc mp reso
  | Algebraic _ ->
    (* any axioms are already declared from the modules and functors
       involved in the application (this means an axiom in a functor
       is reported as coming from the functor rather than from the
       application) *)
    axioms
  | Abstract | FullStruct ->
    collect_signature_axioms env axioms (mod_type mb) mp (mod_delta mb)

and collect_signature_axioms : type a. _ -> _ -> _ -> _ -> a Mod_subst.delta_resolver -> _ =
  fun env axioms sign mp res -> match sign with
  | MoreFunctor (arg_id, mtb, body) ->
    let env = Modops.add_module_parameter arg_id mtb env in
    collect_signature_axioms env axioms body mp res
  | NoFunctor struc ->
    let fold (env, axioms) (lab, field) = match field with
    | SFBconst cb ->
      let kn = Mod_subst.constant_of_delta_kn res (KerName.make mp lab) in
      let axioms =
        match cb.const_body with
        | Def _ | OpaqueDef _ | Primitive _ -> axioms
        | Undef _ | Symbol _ -> axioms_add kn axioms
      in
      Environ.add_constant kn cb env, axioms
    | SFBmodule mb ->
      let mp = MPdot (mp, lab) in
      let axioms = collect_module_axioms env axioms mp mb in
      Modops.add_module mp mb env, axioms
    | SFBmodtype mtb -> Environ.add_modtype (MPdot (mp, lab)) mtb env, axioms
    | SFBmind mib ->
      let kn = Mod_subst.mind_of_delta_kn res (KerName.make mp lab) in
      Environ.add_mind kn mib env, axioms
    | SFBrules _ -> env, axioms
    in
    snd (List.fold_left fold (env, axioms) struc)

let eq_prim_ind (type a b) (p : a CPrimitives.prim_ind) (q : b CPrimitives.prim_ind) =
  String.equal (CPrimitives.prim_ind_to_string p) (CPrimitives.prim_ind_to_string q)

let get_retroknowlege env retro =
  let fold (imap, cmap, extind) = function
  | Retroknowledge.Register_ind (prm, (ind, i)) ->
    (* Tolerate redeclarations because the kernel allows it somehow *)
    let check_prm map = match Mindmap.find_opt ind map with
    | None -> ()
    | Some (_, CPrimitives.PIE prm') ->
      if not (eq_prim_ind prm prm') then
        CErrors.user_err Pp.(str "Inconsistent primitive registration for inductive " ++ MutInd.print ind ++ str ".")
    in
    let () = check_prm imap in
    let () = check_prm extind in
    (* It is allowed to register inductives coming from another library, so we have
       to account for that. *)
    if Environ.mem_mind ind env then
      let spec = Inductive.lookup_mind_specif env (ind, i) in
      let () = Safe_typing.check_register_ind (ind, i) prm spec in
      (imap, cmap, Mindmap.add ind (i, CPrimitives.PIE prm) extind)
    else
      (Mindmap.add ind (i, CPrimitives.PIE prm) imap, cmap, extind)
  | Retroknowledge.Register_type (prm, cst) ->
    let () = assert (not (Cmap.mem cst cmap)) in
    let () = assert (not (Environ.mem_constant cst env)) in
    (imap, Cmap.add cst (CPrimitives.PTE prm) cmap, extind)
  in
  let (imap, cmap, _) = List.fold_left fold (Mindmap.empty, Cmap.empty, Mindmap.empty) retro in
  (imap, cmap)

let check_module env axioms retro mp mb =
  let retro = get_retroknowlege env retro in
  let st = { st_retro = retro } in
  let { st_retro = (imap, cmap) } = check_module env st mp mb in
  let () = match Mindmap.choose_opt imap, Cmap.choose_opt cmap with
  | None, None -> ()
  | Some (ind, _), (None | Some _) ->
    CErrors.user_err Pp.(str "Retroknowledge registration for unknown inductive " ++ MutInd.print ind ++ str ".")
  | None, Some (cst, _) ->
    CErrors.user_err Pp.(str "Retroknowledge registration for unknown constant " ++ Constant.print cst ++ str ".")
  in
  collect_module_axioms env axioms mp mb

let check_module env axioms retro mp mb =
  NewProfile.profile "check_module"
    ~args:(fun () -> [("name", `String (ModPath.to_string mp))])
    (fun () -> check_module env axioms retro mp mb)
    ()
