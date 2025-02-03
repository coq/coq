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
        Label.Map.add (Label.of_id id) (IndConstr((ip,i+1), mib)) map)
      oib.mind_consnames
      map
    in
      Label.Map.add (Label.of_id oib.mind_typename) (IndType (ip, mib)) map
  in
  Array.fold_right_i add_mip_nameobjects mib.mind_packets map


(* creates (namedobject/namedmodule) map for the whole signature *)

type labmap = { objs : namedobject Label.Map.t; mods : namedmodule Label.Map.t }

let empty_labmap = { objs = Label.Map.empty; mods = Label.Map.empty }

let get_obj mp map l =
  try Label.Map.find l map.objs
  with Not_found -> error_no_such_label_sub l (ModPath.to_string mp)

let get_mod mp map l =
  try Label.Map.find l map.mods
  with Not_found -> error_no_such_label_sub l (ModPath.to_string mp)

let make_labmap mp list =
  let add_one (l,e) map =
   match e with
    | SFBconst cb -> { map with objs = Label.Map.add l (Constant cb) map.objs }
    | SFBrules _ -> { map with objs = Label.Map.add l Rules map.objs }
    | SFBmind mib -> { map with objs = add_mib_nameobjects mp l mib map.objs }
    | SFBmodule mb -> { map with mods = Label.Map.add l (Module mb) map.mods }
    | SFBmodtype mtb -> { map with mods = Label.Map.add l (Modtype mtb) map.mods }
  in
  CList.fold_right add_one list empty_labmap

let check_conv_error error why state poly pb env a1 a2 =
  if poly then match Conversion.default_conv pb env a1 a2 with
  | Result.Ok () -> fst state
  | Result.Error () ->  error (IncompatiblePolymorphism (env, a1, a2))
  else match Conversion.generic_conv pb ~l2r:false TransparentState.full env state a1 a2 with
  | Result.Ok state -> state
  | Result.Error None -> error why
  | Result.Error (Some e) -> error (IncompatibleUniverses e)

let check_universes error env u1 u2 =
  match u1, u2 with
  | Monomorphic, Monomorphic -> env
  | Polymorphic auctx1, Polymorphic auctx2 ->
    if not (UGraph.check_subtype (Environ.universes env) auctx2 auctx1) then
      error (IncompatibleConstraints { got = auctx1; expect = auctx2; } )
    else
      Environ.push_context ~strict:false (UVars.AbstractContext.repr auctx2) env
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
  let check_conv why cst poly pb = check_conv_error error why (cst, ustate) poly pb in
  let mib1 =
    match info1 with
      | IndType ((_,0), mib) -> Declareops.subst_mind_body subst1 mib
      | _ -> error (InductiveFieldExpected mib2)
  in
  let env = check_universes error env mib1.mind_universes mib2.mind_universes in
  let () = check_variance error mib1.mind_variance mib2.mind_variance in
  let inst = make_abstract_instance (Declareops.inductive_polymorphic_context mib1) in
  let mib2 =  Declareops.subst_mind_body subst2 mib2 in
  let check_inductive_type cst name t1 t2 =
    check_conv (NotConvertibleInductiveField name)
      cst (inductive_is_polymorphic mib1) CUMUL env t1 t2
  in

  let check_packet cst p1 p2 =
    let check f test why = if not (test (f p1) (f p2)) then error why in
      check (fun p -> p.mind_consnames) (Array.equal Id.equal) NotSameConstructorNamesField;
      check (fun p -> p.mind_typename) Id.equal NotSameInductiveNameInBlockField;
      check (fun p -> p.mind_squashed) (Option.equal squash_info_equal)
        (NotConvertibleInductiveField p2.mind_typename);
      (* nf_lc later *)
      (* nf_arity later *)
      (* user_lc ignored *)
      (* user_arity ignored *)
      check (fun p -> p.mind_nrealargs) Int.equal (NotConvertibleInductiveField p2.mind_typename); (* How can it fail since the type of inductive are checked below? [HH] *)
      (* listrec ignored *)
      (* finite done *)
      (* nparams done *)
      (* params_ctxt done because part of the inductive types *)
      let ty1 = type_of_inductive ((mib1, p1), inst) in
      let ty2 = type_of_inductive ((mib2, p2), inst) in
      let cst = check_inductive_type cst p2.mind_typename ty1 ty2 in
        cst
  in
  let mind = MutInd.make1 kn1 in
  let check_cons_types i cst p1 p2 =
    Array.fold_left3
      (fun cst id t1 t2 -> check_conv (NotConvertibleConstructorField id) cst
        (inductive_is_polymorphic mib1) CONV env t1 t2)
      cst
      p2.mind_consnames
      (arities_of_constructors ((mind,i), inst) (mib1, p1))
      (arities_of_constructors ((mind,i), inst) (mib2, p2))
  in
  let check f test why = if not (test (f mib1) (f mib2)) then error (why (f mib2)) in
  check (fun mib -> mib.mind_finite<>CoFinite) (==) (fun x -> FiniteInductiveFieldExpected x);
  check (fun mib -> mib.mind_ntypes) Int.equal (fun x -> InductiveNumbersFieldExpected x);
  assert (List.is_empty mib1.mind_hyps && List.is_empty mib2.mind_hyps);
  assert (Array.length mib1.mind_packets >= 1
            && Array.length mib2.mind_packets >= 1);

  (* Check that the expected numbers of uniform parameters are the same *)
  (* No need to check the contexts of parameters: it is checked *)
  (* at the time of checking the inductive arities in check_packet. *)
  (* Notice that we don't expect the local definitions to match: only *)
  (* the inductive types and constructors types have to be convertible *)
  check (fun mib -> mib.mind_nparams) Int.equal (fun x -> InductiveParamsNumberField x);

  begin
    let kn2' = kn_of_delta reso2 kn2 in
    if KerName.equal kn2 kn2' ||
       MutInd.CanOrd.equal (mind_of_delta_kn reso1 kn1)
                    (subst_mind subst2 (MutInd.make kn2 kn2'))
    then ()
    else error NotEqualInductiveAliases
  end;
  (* we check that records and their field names are preserved. *)
  (** FIXME: this check looks nonsense *)
  check (fun mib -> mib.mind_record <> NotRecord) (==) (fun x -> RecordFieldExpected x);
  if mib1.mind_record <> NotRecord then begin
    let rec names_prod_letin t = match kind t with
      | Prod(n,_,t) -> n.binder_name::(names_prod_letin t)
      | LetIn(n,_,_,t) -> n.binder_name::(names_prod_letin t)
      | Cast(t,_,_) -> names_prod_letin t
      | _ -> []
    in
    assert (Int.equal (Array.length mib1.mind_packets) 1);
    assert (Int.equal (Array.length mib2.mind_packets) 1);
    assert (Int.equal (Array.length mib1.mind_packets.(0).mind_user_lc) 1);
    assert (Int.equal (Array.length mib2.mind_packets.(0).mind_user_lc) 1);
    check (fun mib ->
      let nparamdecls = List.length mib.mind_params_ctxt in
      let names = names_prod_letin (mib.mind_packets.(0).mind_user_lc.(0)) in
      snd (List.chop nparamdecls names)) (List.equal Name.equal)
      (fun x -> RecordProjectionsExpected x);
  end;
  (* we first check simple things *)
  let cst =
    Array.fold_left2 check_packet cst mib1.mind_packets mib2.mind_packets
  in
  (* and constructor types in the end *)
  let cst =
    Array.fold_left2_i check_cons_types cst mib1.mind_packets mib2.mind_packets
  in
    cst


let check_constant (cst, ustate) trace env l info1 cb2 subst1 subst2 =
  let error why = error_signature_mismatch trace l why in
  let check_conv why cst poly pb = check_conv_error error why (cst, ustate) poly pb in
  let check_type poly cst env t1 t2 =
    let err = NotConvertibleTypeField (env, t1, t2) in
    check_conv err cst poly CUMUL env t1 t2
  in
  match info1 with
    | IndType _ | IndConstr _ | Rules -> error DefinitionFieldExpected
    | Constant cb1 ->
      let () = assert (List.is_empty cb1.const_hyps && List.is_empty cb2.const_hyps) in
      let cb1 = Declareops.subst_const_body subst1 cb1 in
      let cb2 = Declareops.subst_const_body subst2 cb2 in
      (* Start by checking universes *)
      let env = check_universes error env cb1.const_universes cb2.const_universes in
      let poly = Declareops.constant_is_polymorphic cb1 in
      (* Now check types *)
      let typ1 = cb1.const_type in
      let typ2 = cb2.const_type in
      let cst = check_type poly cst env typ1 typ2 in
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
      (match cb2.const_body with
       | Undef _ | OpaqueDef _ -> cst
       | Primitive _ | Symbol _ -> error NotConvertibleBodyField
       | Def c2 ->
         (match cb1.const_body with
          | Primitive _ | Undef _ | OpaqueDef _ | Symbol _ -> error NotConvertibleBodyField
          | Def c1 ->
            (* NB: cb1 might have been strengthened and appear as transparent.
               Anyway [check_conv] will handle that afterwards. *)
            check_conv NotConvertibleBodyField cst poly CONV env c1 c2))

let rec check_modules state trace env mp1 msb1 mp2 msb2 subst1 subst2 =
  let mty1 = module_type_of_module msb1 in
  let mty2 = module_type_of_module msb2 in
  check_modtypes state trace env mp1 mty1 mp2 mty2 subst1 subst2 false

and check_signatures (cst, ustate) trace env mp1 sig1 mp2 sig2 subst1 subst2 reso1 reso2 =
  let map1 = make_labmap mp1 sig1 in
  let check_one_body cst (l,spec2) =
    match spec2 with
        | SFBconst cb2 ->
            check_constant (cst, ustate) trace env l (get_obj mp1 map1 l)
              cb2 subst1 subst2
        | SFBmind mib2 ->
            check_inductive (cst, ustate) trace env mp1 l (get_obj mp1 map1 l)
              mp2 mib2 subst1 subst2 reso1 reso2
        | SFBrules _ ->
            error_signature_mismatch trace l NoRewriteRulesSubtyping
        | SFBmodule msb2 ->
            let mp1' = MPdot (mp1, l) in
            let mp2' = MPdot (mp2, l) in
            begin match get_mod mp1 map1 l with
              | Module msb1 -> check_modules (cst, ustate) (Submodule l :: trace) env mp1' msb1 mp2' msb2 subst1 subst2
              | _ -> error_signature_mismatch trace l ModuleFieldExpected
            end
        | SFBmodtype mtb2 ->
            let mtb1 = match get_mod mp1 map1 l with
              | Modtype mtb -> mtb
              | _ -> error_signature_mismatch trace l ModuleTypeFieldExpected
            in
            let mp1' = MPdot (mp1, l) in
            let mp2' = MPdot (mp2, l) in
            let env = add_module mp2' (module_body_of_type mtb2) (add_module mp1' (module_body_of_type mtb1) env) in
            check_modtypes (cst, ustate) (Submodule l :: trace) env mp1' mtb1 mp2' mtb2 subst1 subst2 true
  in
    List.fold_left check_one_body cst sig2

and check_modtypes (cst, ustate) trace env mp1 mtb1 mp2 mtb2 subst1 subst2 equiv =
  if mtb1==mtb2 || mod_type mtb1 == mod_type mtb2 then cst
  else
    let rec check_structure cst ~nargs env struc1 struc2 equiv subst1 subst2 =
      match struc1,struc2 with
      | NoFunctor list1,
        NoFunctor list2 ->
        let delta_mtb1 = mod_delta mtb1 in
        let delta_mtb2 = mod_delta mtb2 in
        if equiv then
          let subst2 = add_mp mp2 mp1 delta_mtb1 subst2 in
          let cst = check_signatures (cst, ustate) trace env
            mp1 list1 mp2 list2 subst1 subst2
            delta_mtb1 delta_mtb2
          in
          let cst = check_signatures (cst, ustate) trace env
            mp2 list2 mp1 list1 subst2 subst1
            delta_mtb2 delta_mtb1
          in
          cst
        else
          check_signatures (cst, ustate) trace env
            mp1 list1 mp2 list2 subst1 subst2
            delta_mtb1 delta_mtb2
      | MoreFunctor (arg_id1,arg_t1,body_t1),
        MoreFunctor (arg_id2,arg_t2,body_t2) ->
        let mparg1 = MPbound arg_id1 in
        let mparg2 = MPbound arg_id2 in
        let subst1 = join (map_mbid arg_id1 mparg2 (mod_delta arg_t2)) subst1 in
        let env = add_module_parameter arg_id2 arg_t2 env in
        let cst = check_modtypes (cst, ustate) (FunctorArgument (nargs+1) :: trace) env mparg2 arg_t2 mparg1 arg_t1 subst2 subst1 equiv in
        (* contravariant *)
        let env =
          if Modops.is_functor body_t1 then env
          else
            let mtb = make_module_type (subst_signature subst1 mp1 body_t1) (mod_delta mtb1) in
            add_module mp1 (module_body_of_type mtb) env
        in
        check_structure cst ~nargs:(nargs + 1) env body_t1 body_t2 equiv subst1 subst2
      | _ , _ -> error_incompatible_modtypes mtb1 mtb2
    in
    check_structure cst ~nargs:0 env (mod_type mtb1) (mod_type mtb2) equiv subst1 subst2

let check_subtypes state env mp_sup sup mp_super super =
  let env = add_module mp_sup (module_body_of_type sup) env in
  check_modtypes state [] env
    mp_sup (strengthen sup mp_sup) mp_super super empty_subst
    (map_mp mp_super mp_sup (mod_delta sup)) false
