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

(* This module checks subtyping of module types *)

(*i*)
open Names
open UVars
open Util
open Constr
open Declarations
open Mod_declarations
open Declareops
open Conversion
open Inductive
open Modops
open Context
open Mod_subst
(*i*)

(* This local type is used to subtype a constant with a constructor or
   an inductive type. It can also be useful to allow reorderings in
   inductive types *)
type namedobject =
  | Constant of constant_body
  | IndType of inductive * mutual_inductive_body
  | IndConstr of constructor * mutual_inductive_body
  | Rules

type namedmodule =
  | Module of module_body
  | Modtype of module_type_body

(* adds above information about one mutual inductive: all types and
   constructors *)

let add_mib_nameobjects mp l mib map =
  let ind = MutInd.make2 mp l in
  let add_mip_nameobjects j oib map =
    let ip = (ind,j) in
    let map =
      Array.fold_right_i
      (fun i id map ->
        Id.Map.add id (IndConstr((ip,i+1), mib)) map)
      oib.mind_consnames
      map
    in
      Id.Map.add oib.mind_typename (IndType (ip, mib)) map
  in
  Array.fold_right_i add_mip_nameobjects mib.mind_packets map


(* creates (namedobject/namedmodule) map for the whole signature *)

type labmap = { objs : namedobject Id.Map.t; mods : namedmodule Id.Map.t }

let empty_labmap = { objs = Id.Map.empty; mods = Id.Map.empty }

(** How to look up the fields of the implementation (subtype) side of a
    check.

    [Direct] is used when the caller guarantees that the fields of the
    module at [mp1] are part of the environment, unsubstituted — the
    invariant documented in [check_structure] for [nargs = 0]: this holds
    for the current interactive module (Include self), for any module
    already added to the environment (functor application), and for a
    module about to be closed. Fields are then looked up directly in the
    environment, which avoids building a label map over the whole
    signature when only a few fields are checked.

    [Direct (Some reso)] additionally means that constant and submodule
    fields must be seen strengthened w.r.t. [reso], producing the same
    fields as looking them up in [Modops.strengthen] of the signature.
    Strengthening of constants is performed on demand in [check_constant].

    Lookups fall back to the label map (built lazily from the signature)
    when the label does not correspond to a field of the module (e.g. the
    name of a constructor or of a secondary inductive type of a block), so
    behavior is unchanged in those cases. *)
type direct_access =
  | NoDirect
  | Direct of Mod_subst.delta_resolver option

type sigview = { sv_direct : direct_access; sv_map : labmap Lazy.t }

let get_obj_fallback mp view l =
  try Id.Map.find l (Lazy.force view.sv_map).objs
  with Not_found -> error_no_such_label_sub l (ModPath.to_string mp)

let get_obj env mp view l =
  match view.sv_direct with
  | NoDirect -> get_obj_fallback mp view l
  | Direct _ ->
    (* strengthening of constants, when required, is done in [check_constant] *)
    begin match Environ.lookup_constant_opt (Constant.make2 mp l) env with
    | Some cb -> Constant cb
    | None ->
      let mind = MutInd.make2 mp l in
      if Environ.mem_mind mind env then
        let mib = Environ.lookup_mind mind env in
        if Id.equal mib.mind_packets.(0).mind_typename l
        then IndType ((mind, 0), mib)
        else get_obj_fallback mp view l
      else get_obj_fallback mp view l
    end

let get_mod_fallback mp view l =
  try Id.Map.find l (Lazy.force view.sv_map).mods
  with Not_found -> error_no_such_label_sub l (ModPath.to_string mp)

let get_mod env mp view l =
  match view.sv_direct with
  | NoDirect -> get_mod_fallback mp view l
  | Direct str ->
    let mp' = MPdot (mp, l) in
    begin match Environ.lookup_module mp' env with
    | mb ->
      let mb = match str with
        | Some _ -> Modops.strengthen_module mp' mb
        | None -> mb
      in
      Module mb
    | exception Not_found ->
      match Environ.lookup_modtype mp' env with
      | mtb -> Modtype mtb
      | exception Not_found -> get_mod_fallback mp view l
    end

(** Cache of successful constant field checks.

    A successful check of an implementation field [cb1] against an
    expected field [cb2] is a function of the pair itself whenever both
    substitutions leave the bodies physically unchanged (checked at run
    time) and the check did not produce new universe constraints (the
    returned state is physically the input one; the kernel-side checking
    mode never produces constraints, and the inference mode returns its
    input state unchanged when all needed constraints are already
    entailed). Such a check stays valid later in the same process:
    - the environment only grows, and a successful conversion is
      preserved by adding constants, universe constraints or rewrite
      rules (conversion success is monotone in the environment);
    - constant bodies are immutable, and rolling back the environment
      (Undo, Reset) also drops every object that could re-present the
      cached pair;
    - conversion compares constant references up to the delta resolver
      (canonical names), so a successful check is independent of the
      user-level path under which physically equal bodies are reached.

    Cached verdicts are only valid as long as the ambient environment
    evolves monotonically. The cache is therefore purely functional and
    threaded through the checks: callers store it alongside the
    environment their checks were performed in (a [safe_environment]
    field on the kernel side), so that discarding or rolling back that
    environment also discards or rolls back the cache.

    The cache is indexed by the label of the field — whose hash is cheap,
    and which is stable across the module paths under which the same
    bodies may be rechecked (e.g. re-including a functor in each stage of
    a chain of module types) — and holds a short list of successfully
    checked pairs for that label, compared physically. The list is
    capped, so the cache retains a bounded number of bodies per label
    ever checked. Failures are not cached (they raise). *)
module Cache =
struct
  type t = (constant_body * constant_body) list Id.Map.t

  let empty = Id.Map.empty

  let max_gen = 16

  let mem l cb1 cb2 cache =
    match Id.Map.find_opt l cache with
    | None -> false
    | Some pairs -> List.exists (fun (c1, c2) -> c1 == cb1 && c2 == cb2) pairs

  let add l cb1 cb2 cache =
    let prev = match Id.Map.find_opt l cache with
      | None -> []
      | Some pairs ->
        if List.length pairs >= max_gen
        then CList.firstn (max_gen - 1) pairs
        else pairs
    in
    Id.Map.add l ((cb1, cb2) :: prev) cache
end

let make_labmap mp list =
  let add_one (l,e) map =
   match e with
    | SFBconst cb -> { map with objs = Id.Map.add l (Constant cb) map.objs }
    | SFBrules _ -> { map with objs = Id.Map.add l Rules map.objs }
    | SFBmind mib -> { map with objs = add_mib_nameobjects mp l mib map.objs }
    | SFBmodule mb -> { map with mods = Id.Map.add l (Module mb) map.mods }
    | SFBmodtype mtb -> { map with mods = Id.Map.add l (Modtype mtb) map.mods }
  in
  CList.fold_right add_one list empty_labmap

let check_conv_error error why state poly pb env a1 a2 =
  if poly then match Conversion.default_conv pb env a1 a2 with
  | Result.Ok () -> fst state
  | Result.Error () ->  error (IncompatiblePolymorphism (env, a1, a2))
  else match Conversion.generic_conv pb ~l2r:false TransparentState.full env state a1 a2 with
  | Result.Ok state -> state
  | Result.Error None -> error why
  | Result.Error (Some (Univ e)) -> error (IncompatibleUniverses { err = e; env; t1 = a1; t2 = a2 })
  | Result.Error (Some (Qual e)) -> error (IncompatibleQualities { err = e; env; t1 = a1; t2 = a2 })

(** Subtyping of polymorphic contexts *)

let check_polymorphic_universes env ctxT ctx =
  if not @@ eq_sizes (AbstractContext.size ctxT) (AbstractContext.size ctx) then false
  else
    let uctxT = AbstractContext.repr ctxT in
    let () = Environ.check_ucontext uctxT env in
    let env = Environ.push_context ~strict:false uctxT env in
    let qcst, ucst = UContext.constraints (AbstractContext.repr ctx) in
    UGraph.check_constraints ucst (Environ.universes env) &&
    QGraph.check_constraints qcst (Environ.qualities env)

let check_universes error env u1 u2 =
  match u1, u2 with
  | Monomorphic, Monomorphic -> env
  | Polymorphic auctx1, Polymorphic auctx2 ->
    if not (check_polymorphic_universes env auctx2 auctx1) then
      error (IncompatibleUnivConstraints { env; got = auctx1; expect = auctx2; } )
    else
      let () = Environ.check_ucontext (UVars.AbstractContext.repr auctx2) env in
      let env = Environ.push_context ~strict:false (UVars.AbstractContext.repr auctx2) env in
      env
  | Monomorphic, Polymorphic _ -> error (PolymorphicStatusExpected true)
  | Polymorphic _, Monomorphic -> error (PolymorphicStatusExpected false)

let check_variance error v1 v2 =
  match v1, v2 with
  | None, None -> ()
  | Some v1, Some v2 ->
    if not (Array.for_all2 Variance.check_subtype v2 v1) then
      error IncompatibleVariance
  | None, Some _ -> error (CumulativeStatusExpected true)
  | Some _, None -> error (CumulativeStatusExpected false)

let squash_info_equal s1 s2 = match s1, s2 with
  | AlwaysSquashed, AlwaysSquashed -> true
  | SometimesSquashed s1, SometimesSquashed s2 -> Sorts.Quality.Set.equal s1 s2
  | (AlwaysSquashed | SometimesSquashed _), _ -> false

(* for now we do not allow reorderings *)

let check_inductive (cst, ustate) trace env mp1 l info1 mp2 mib2 subst1 subst2 reso1 reso2=
  let kn1 = KerName.make mp1 l in
  let kn2 = KerName.make mp2 l in
  let error why = error_signature_mismatch trace l why in
  let mib1 =
    match info1 with
      | IndType ((_,0), mib) -> Declareops.subst_mind_body subst1 mib
      | _ -> error (InductiveFieldExpected mib2)
  in
  let poly = inductive_is_polymorphic mib1 in
  let check_conv why cst pb = check_conv_error error why (cst, ustate) poly pb in

  let check_rel_ctx err env cst ctx1 ctx2 =
    let () = if not (List.same_length ctx1 ctx2) then error err in
    List.fold_right2 (fun d1 d2 (env, cst) ->
        let open Context.Rel.Declaration in
        match d1, d2 with
        | LocalAssum (_, t1), LocalAssum (_, t2) ->
          let cst = check_conv err cst CONV env t1 t2 in
          Environ.push_rel d1 env, cst
        | LocalDef (_, b1, t1), LocalDef (_, b2, t2) ->
          let cst = check_conv err cst CONV env t1 t2 in
          let cst = check_conv err cst CONV env b1 b2 in
          Environ.push_rel d1 env, cst
        | (LocalAssum _ | LocalDef _), _ -> error err)
      ctx1 ctx2 (env, cst)
  in

  let env = check_universes error env mib1.mind_universes mib2.mind_universes in
  let () = check_variance error mib1.mind_variance mib2.mind_variance in
  let inst = make_abstract_instance (Declareops.inductive_polymorphic_context mib1) in
  let mib2 =  Declareops.subst_mind_body subst2 mib2 in
  let check_inductive_type ~is_ctor cst name t1 t2 =
    let err = if is_ctor then NotConvertibleConstructorField (name, Some (env, t1, t2))
      else NotConvertibleInductiveField (name, Some (env, t1, t2))
    in
    let ctx1, o1 = Term.decompose_prod_decls t1 in
    let ctx2, o2 = Term.decompose_prod_decls t2 in
    let env, cst = check_rel_ctx err env cst ctx1 ctx2 in
    let pb = if is_ctor then CONV else CUMUL in
    check_conv err cst pb env o1 o2
  in

  let check_packet cst p1 p2 =
    let check f test why = let fp2 = f p2 in if not (test (f p1) fp2) then error (why fp2) in
      if not (Array.equal Id.equal p1.mind_consnames p2.mind_consnames) then
        error (NotSameConstructorNamesField (p1.mind_consnames, p2.mind_consnames));
      if not (Id.equal p1.mind_typename p2.mind_typename) then
        error (NotSameInductiveNameInBlockField (p1.mind_typename, p2.mind_typename));
      check (fun p -> p.mind_squashed) (Option.equal squash_info_equal)
        (fun _ -> NotConvertibleInductiveField (p2.mind_typename, None));
      (* nf_lc later *)
      (* nf_arity later *)
      (* user_lc ignored *)
      (* user_arity ignored *)
      check (fun p -> p.mind_nrealargs) Int.equal (fun _ -> NotConvertibleInductiveField (p2.mind_typename, None)); (* How can it fail since the type of inductive are checked below? [HH] *)
      (* listrec ignored *)
      (* finite done *)
      (* nparams done *)
      (* params_ctxt done because part of the inductive types *)
      let ty1 = type_of_inductive ((mib1, p1), inst) in
      let ty2 = type_of_inductive ((mib2, p2), inst) in
      let cst = check_inductive_type ~is_ctor:false cst p2.mind_typename ty1 ty2 in
      (* we check that records and their field names are preserved. *)
      (** FIXME: this check looks nonsense *)
      check (fun p -> p.mind_record <> NotRecord) (==) (fun x -> RecordFieldExpected x);
      if p1.mind_record <> NotRecord then begin
        let rec names_prod_letin t = match kind t with
          | Prod(n,_,t) -> n.binder_name::(names_prod_letin t)
          | LetIn(n,_,_,t) -> n.binder_name::(names_prod_letin t)
          | Cast(t,_,_) -> names_prod_letin t
          | _ -> []
        in
        assert (Int.equal (Array.length p1.mind_user_lc) 1);
        assert (Int.equal (Array.length p2.mind_user_lc) 1);
        let get_proj_names p =
          (* can nparamdecls depend on which mib we look at? *)
          let nparamdecls = List.length mib1.mind_params_ctxt in
          let names = names_prod_letin (p.mind_user_lc.(0)) in
          snd (List.chop nparamdecls names)
        in
        (* p1 is implementation, p2 is signature (expected) *)
        let expected = get_proj_names p2 in
        let got = get_proj_names p1 in
        if not (List.equal Name.equal expected got) then
          error (RecordProjectionsExpected { expected; got });
      end;
      cst
  in
  let mind = MutInd.make1 kn1 in
  let check_cons_types i cst p1 p2 =
    Array.fold_left3 (check_inductive_type ~is_ctor:true)
      cst
      p2.mind_consnames
      (arities_of_constructors ((mind,i), inst) (mib1, p1))
      (arities_of_constructors ((mind,i), inst) (mib2, p2))
  in
  let check f test why = if not (test (f mib1) (f mib2)) then error (why (f mib2)) in
  check (fun mib -> mib.mind_finite<>CoFinite) (==) (fun x -> FiniteInductiveFieldExpected x);
  if not (Int.equal (Declareops.mind_ntypes mib1) (Declareops.mind_ntypes mib2)) then
    error (InductiveNumbersFieldExpected { got = Declareops.mind_ntypes mib1; expected = Declareops.mind_ntypes mib2 });
  assert (List.is_empty mib1.mind_hyps && List.is_empty mib2.mind_hyps);
  assert (Array.length mib1.mind_packets >= 1
            && Array.length mib2.mind_packets >= 1);

  (* Check that the parameters are the same (ignoring names).
     It seems like we could accept differences in localdef params, but
     because they can be accessed through a localdef constructor
     argument it would lead to inconsistency. *)
  let cst =
    let ctx1 = mib1.mind_params_ctxt in
    let ctx2 = mib2.mind_params_ctxt in
    let _env, cst = check_rel_ctx
        (InductiveParams { env; got = ctx1; expected = ctx2; })
        env cst ctx1 ctx2
    in
    cst
  in

  let () =
    let kn1' = kn_of_delta reso1 kn1 in
    let kn2' = kn_of_delta reso2 kn2 in
    let mind1 = MutInd.make kn1 kn1' in
    let mind2 = subst_mind subst2 (MutInd.make kn2 kn2') in
    if KerName.equal kn2 kn2' || KerName.equal kn1' (MutInd.canonical mind2)
    then ()
    else error (NotEqualInductiveAliases (mind1, mind2))
  in
  (* we first check simple things *)
  let cst =
    Array.fold_left2 check_packet cst mib1.mind_packets mib2.mind_packets
  in
  (* and constructor types in the end *)
  let cst =
    Array.fold_left2_i check_cons_types cst mib1.mind_packets mib2.mind_packets
  in
    cst


let check_constant (cst, ustate) cache trace env mp1 l strengthen1 info1 cb2 subst1 subst2 =
  let error why = error_signature_mismatch trace l why in
  let check_conv why cst poly pb = check_conv_error error why (cst, ustate) poly pb in
  let check_type poly cst env t1 t2 =
    let err = NotConvertibleTypeField (env, t1, t2) in
    check_conv err cst poly CUMUL env t1 t2
  in
  match info1 with
    | IndType _ | IndConstr _ | Rules -> error DefinitionFieldExpected
    | Constant cb1_0 ->
      let cb2_0 = cb2 in
      let () = assert (List.is_empty cb1_0.const_hyps && List.is_empty cb2_0.const_hyps) in
      (* On-demand strengthening (see [direct_access]) only happens with an
         empty [subst1], so it commutes with the substitution below. *)
      let () = assert (Option.is_empty strengthen1 || is_empty_subst subst1) in
      let scb1 = Declareops.subst_const_body subst1 cb1_0 in
      let scb2 = Declareops.subst_const_body subst2 cb2_0 in
      (* The outcome only depends on the pair of bodies when both
         substitutions leave them physically unchanged, see [Cache]. *)
      let context_free = scb1 == cb1_0 && scb2 == cb2_0 in
      if context_free && Cache.mem l cb1_0 cb2_0 cache then (cst, cache)
      else begin
      let cb1 = match strengthen1 with
        | Some reso -> Modops.strengthen_const mp1 l scb1 reso
        | None -> scb1
      in
      let cb2 = scb2 in
      (* Start by checking universes *)
      let env = check_universes error env cb1.const_universes cb2.const_universes in
      let poly = Declareops.constant_is_polymorphic cb1 in
      (* Now check types *)
      let typ1 = cb1.const_type in
      let typ2 = cb2.const_type in
      let cst' = check_type poly cst env typ1 typ2 in
      (* Now we check the bodies:
         - A transparent constant can only be implemented by a compatible
           transparent constant.
         - A primitive cannot be implemented.
           (We could try to allow implementing with the same primitive,
            but for some reason we get cb1.const_body = Def,
            without some use case there is no motivation to solve this.)
         - In the signature, an opaque is handled just as a parameter:
           anything of the right type can implement it, even if bodies differ.
      *)
      let cst' =
        (match cb2.const_body with
         | Undef _ | OpaqueDef _ -> cst'
         | Primitive _ | Symbol _ -> error (NotConvertibleBodyField None)
         | Def c2 ->
           (match cb1.const_body with
            | Primitive _ | Undef _ | OpaqueDef _ | Symbol _ -> error (NotConvertibleBodyField None)
            | Def c1 ->
              (* NB: cb1 might have been strengthened and appear as transparent.
                 Anyway [check_conv] will handle that afterwards. *)
              check_conv (NotConvertibleBodyField (Some (env, c1, c2))) cst' poly CONV env c1 c2))
      in
      (* Only cache checks that produced no new universe constraints: they
         are then pure and stay valid as long as the environment the cache
         is stored alongside evolves monotonically. *)
      let cache =
        if context_free && cst' == cst then Cache.add l cb1_0 cb2_0 cache
        else cache
      in
      (cst', cache)
      end

let rec check_modules state cache trace env mp1 msb1 mp2 msb2 subst1 subst2 =
  let mty1 = module_type_of_module msb1 in
  let mty2 = module_type_of_module msb2 in
  check_modtypes state cache trace env mp1 mty1 mp2 mty2 subst1 subst2

and check_signatures (cst, ustate) cache trace env mp1 sig1 dir mp2 sig2 subst1 subst2 reso1 reso2 =
  let view = { sv_direct = dir; sv_map = lazy (make_labmap mp1 sig1) } in
  let strengthen1 = match dir with Direct str -> str | NoDirect -> None in
  let check_one_body (cst, cache) (l,spec2) =
    match spec2 with
        | SFBconst cb2 ->
            check_constant (cst, ustate) cache trace env mp1 l strengthen1 (get_obj env mp1 view l)
              cb2 subst1 subst2
        | SFBmind mib2 ->
            check_inductive (cst, ustate) trace env mp1 l (get_obj env mp1 view l)
              mp2 mib2 subst1 subst2 reso1 reso2,
            cache
        | SFBrules _ ->
            error_signature_mismatch trace l NoRewriteRulesSubtyping
        | SFBmodule msb2 ->
            let mp1' = MPdot (mp1, l) in
            let mp2' = MPdot (mp2, l) in
            begin match get_mod env mp1 view l with
              | Module msb1 -> check_modules (cst, ustate) cache (Submodule l :: trace) env mp1' msb1 mp2' msb2 subst1 subst2
              | _ -> error_signature_mismatch trace l ModuleFieldExpected
            end
        | SFBmodtype mtb2 ->
            let mtb1 = match get_mod env mp1 view l with
              | Modtype mtb -> mtb
              | _ -> error_signature_mismatch trace l ModuleTypeFieldExpected
            in
            let mp1' = MPdot (mp1, l) in
            let mp2' = MPdot (mp2, l) in
            (* Check for equivalence via subtyping in both directions *)
            let cst, cache =
              let env = add_module mp1' (module_body_of_type mtb1) env in
              check_modtypes (cst, ustate) cache (Submodule l :: trace) env mp1' mtb1 mp2' mtb2 subst1 subst2
            in
            let env = add_module mp2' (module_body_of_type mtb2) env in
            check_modtypes (cst, ustate) cache (Submodule l :: trace) env mp2' mtb2 mp1' mtb1 subst2 subst1
  in
    List.fold_left check_one_body (cst, cache) sig2

and check_modtypes ?(dir=NoDirect) (cst, ustate) cache trace env mp1 mtb1 mp2 mtb2 subst1 subst2 =
  if mtb1==mtb2 || mod_type mtb1 == mod_type mtb2 then (cst, cache)
  else
    (* Invariant: [delta1] is [mod_delta mtb1] transported into the name space
       of [env], and [subst2] sends [mp2] to [mp1] with [delta1] as resolver.
       As we descend into a functor, [subst1] renames the implementation's
       parameters into the signature's ones, so [delta1] must follow, and the
       resolver carried by [subst2] must be kept in sync with it. Otherwise the
       canonical names computed through [subst2] live in a different name space
       than the ones computed through [subst1] and can never be recognised as
       equal. Note that re-adding the binding for [mp2] also matters when [mp2]
       is a submodule of the module the enclosing [subst2] talks about: for a
       functor field the enclosing resolver carries no information at all,
       since [mod_global_delta] is [None] on functors. *)
    let rec check_structure (cst, cache) ~nargs env struc1 struc2 subst1 subst2 delta1 =
      match struc1,struc2 with
      | NoFunctor list1,
        NoFunctor list2 ->
        let env, dir =
          if Int.equal nargs 0 then
            (* Not a functor, so the body and all its subcomponents should
               already be in the environment *)
            env, dir
          else
            (* We only add the subcomponents, the functor per se is already
               part of the environment but the subtyping check will never access
               it directly.  The fields added to the environment are
               substituted, so direct access does not apply to them. *)
            Modops.add_structure mp1 (subst_structure subst1 mp1 list1) delta1 env,
            NoDirect
        in
        let delta_mtb2 = mod_delta mtb2 in
        check_signatures (cst, ustate) cache trace env
          mp1 list1 dir mp2 list2 subst1 subst2
          delta1 delta_mtb2
      | MoreFunctor (arg_id1,arg_t1,body_t1),
        MoreFunctor (arg_id2,arg_t2,body_t2) ->
        let mparg1 = MPbound arg_id1 in
        let mparg2 = MPbound arg_id2 in
        let nsubst = map_mbid arg_id1 mparg2 (mod_delta arg_t2) in
        let subst1 = join nsubst subst1 in
        let delta1 = subst_codom_delta_resolver nsubst delta1 in
        let subst2 = add_mp mp2 mp1 delta1 subst2 in
        let env = add_module_parameter arg_id2 arg_t2 env in
        let cst, cache = check_modtypes (cst, ustate) cache (FunctorArgument (nargs+1) :: trace) env mparg2 arg_t2 mparg1 arg_t1 subst2 subst1 in
        (* contravariant *)
        check_structure (cst, cache) ~nargs:(nargs + 1) env body_t1 body_t2 subst1 subst2 delta1
      | _ , _ -> error_incompatible_modtypes mtb1 mtb2
    in
    check_structure (cst, cache) ~nargs:0 env (mod_type mtb1) (mod_type mtb2) subst1 subst2
      (subst_codom_delta_resolver subst1 (mod_delta mtb1))

let check_subtypes ?(direct=false) ~cache state env mp_sup mp_super super =
  let sup = match Environ.lookup_module mp_sup env with
  | mb -> module_type_of_module mb
  | exception Not_found -> assert false
  in
  let subst2 = map_mp mp_super mp_sup (mod_delta sup) in
  if direct then
    (* The caller guarantees that the fields of [mp_sup] are in [env],
       unsubstituted; look them up there on demand instead of eagerly
       strengthening the whole signature (see [direct_access]).
       [mod_global_delta] is [None] on functors, where [strengthen] does
       not strengthen either. *)
    let dir = Direct (mod_global_delta sup) in
    check_modtypes ~dir (state) cache [] env mp_sup sup mp_super super empty_subst subst2
  else
    check_modtypes state cache [] env
      mp_sup (strengthen sup mp_sup) mp_super super empty_subst subst2
