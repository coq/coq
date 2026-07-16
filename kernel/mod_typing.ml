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

(* This module provides the main functions for type-checking module
   declarations *)

open Util
open Names
open Declarations
open Mod_declarations
open Entries
open Environ
open Modops
open Mod_subst

let rec mp_from_mexpr = function
  | MEident mp -> mp
  | MEapply (expr,_) -> mp_from_mexpr expr
  | MEwith (expr,_) -> mp_from_mexpr expr

let is_modular = function
  | SFBmodule _ | SFBmodtype _ -> true
  | SFBconst _ | SFBmind _ | SFBrules _ -> false

(** Split a [structure_body] at some label corresponding to
    a modular definition or not. *)

let split_struc k m struc =
  let rec split rev_before = function
    | [] -> raise Not_found
    | (k',b)::after when Id.equal k k' && (is_modular b) == (m : bool) ->
      List.rev rev_before,b,after
    | h::tail -> split (h::rev_before) tail
  in split [] struc

let discr_resolver mp mtb = match mod_type mtb with
  | NoFunctor _ -> mod_delta mtb
  | MoreFunctor _ -> empty_delta_resolver mp

let rec rebuild_mp mp l =
  match l with
  | []-> mp
  | i::r -> rebuild_mp (MPdot(mp,i)) r

let infer_gen_conv state env c1 c2 =
  Conversion.generic_conv Conversion.CONV ~l2r:false TransparentState.full env state c1 c2

let infer_gen_conv_leq state env c1 c2 =
  Conversion.generic_conv Conversion.CUMUL ~l2r:false TransparentState.full env state c1 c2

type with_body = {
  w_def : Constr.t;
  w_univs : universes;
  w_bytecode : Vmlibrary.indirect_code;
}

let rec check_with_def (cst, ustate) env struc (idl, wth) mp reso =
  let lab,idl = match idl with
    | [] -> assert false
    | id::idl -> id, idl
  in
  let error why = error_incorrect_with_constraint lab why in
  try
    let modular = not (List.is_empty idl) in
    let before,spec,after = split_struc lab modular struc in
    let env' = Modops.add_structure mp before reso env in
    if List.is_empty idl then
      (* Toplevel definition *)
      let cb = match spec with
        | SFBconst cb -> cb
        | _ -> error_not_a_constant lab
      in
      (* In the spirit of subtyping.check_constant, we accept
         any implementations of parameters and opaque terms,
         as long as they have the right type *)
      let (univs, typ), ctx' =
        match cb.const_universes, wth.w_univs with
        | Monomorphic, Monomorphic ->
          let error_univ_mismatch env t1 t2 = function
            | Conversion.Univ err -> error (WithSignatureMismatch (IncompatibleUniverses { err; env; t1; t2 }))
            | Conversion.Qual err -> error (WithSignatureMismatch (IncompatibleQualities { err; env; t1; t2 }))
          in
          let j = Typeops.infer env' wth.w_def in
          begin match cb.const_body with
          | Undef _ | OpaqueDef _ ->
            let typ = cb.const_type in
            begin match infer_gen_conv_leq (cst, ustate) env' j.uj_type typ with
            | Result.Ok cst -> (cb.const_universes, cb.const_type), cst
            | Result.Error None -> error (WithSignatureMismatch (NotConvertibleTypeField (env', j.uj_type, typ)))
            | Result.Error (Some e) -> error_univ_mismatch env' j.uj_type typ e
            end
          | Def c' ->
            begin match infer_gen_conv (cst, ustate) env' wth.w_def c' with
            | Result.Ok cst -> (cb.const_universes, cb.const_type), cst
            | Result.Error None -> error (WithSignatureMismatch (NotConvertibleBodyField (Some (env', wth.w_def, c'))))
            | Result.Error (Some e) -> error_univ_mismatch env' wth.w_def c' e
            end
          | Primitive _ -> error WithCannotConstrainPrimitive
          | Symbol _ -> error WithCannotConstrainSymbol
          end
        | Polymorphic uctx, Polymorphic ctx ->
          let () =
            if not (Subtyping.check_polymorphic_universes env uctx ctx) then
              error (WithSignatureMismatch (IncompatibleUnivConstraints { env; got = ctx; expect = uctx }))
          in
          (** Terms are compared in a context with De Bruijn universe indices *)
          let () = check_ucontext (UVars.AbstractContext.repr uctx) env in
          let j =
            (* Use 1. the external environment with 2. the with Definition constraints *)
            let jenv = Environ.push_context ~strict:false (UVars.AbstractContext.repr ctx) env in
            Typeops.infer jenv wth.w_def
          in
          let env' = Environ.push_context ~strict:false (UVars.AbstractContext.repr uctx) env' in
          let () = match cb.const_body with
            | Undef _ | OpaqueDef _ ->
              let typ = cb.const_type in
              begin match Conversion.conv_leq env' j.uj_type typ with
              | Result.Ok () -> ()
              | Result.Error () -> error (WithSignatureMismatch (NotConvertibleTypeField (env', typ, j.uj_type)))
              end
            | Def c' ->
              begin match Conversion.conv env' wth.w_def c' with
              | Result.Ok () -> ()
              | Result.Error () -> error (WithSignatureMismatch (NotConvertibleBodyField (Some (env', wth.w_def, c'))))
              end
            | Primitive _ -> error WithCannotConstrainPrimitive
            | Symbol _ -> error WithCannotConstrainSymbol
          in
          (cb.const_universes, cb.const_type), cst
        | Monomorphic, Polymorphic _ -> error (WithSignatureMismatch (PolymorphicStatusExpected true))
        | Polymorphic _, Monomorphic -> error (WithSignatureMismatch (PolymorphicStatusExpected false))
      in
      (* Here we have two choices for the type of the constant: either pick the
         type T from module constant or the type U from the with Definition
         constant, including their universe constraints. In general, we only
         have U ≤ T, so the corresponding module types will only satisfy
         MU ≤ MT. In some sense MU is minimal and MT maximal, so both are
         canonical. Depending on the context, one may be preferred to the
         other but there is no "best" choice a priori. Some code out there
         depends on picking MT, so we enshrine this decision here. *)
      let cb' =
        { cb with
          const_body = Def wth.w_def;
          const_type = typ;
          const_universes = univs;
          const_body_code = wth.w_bytecode; }
      in
      before@(lab,SFBconst(cb'))::after, ctx'
    else
      (* Definition inside a sub-module *)
      let mb = match spec with
        | SFBmodule mb -> mb
        | _ -> error_not_a_module_label lab
      in
      begin match Mod_declarations.mod_expr mb with
        | Abstract ->
          let struc = Modops.destr_nofunctor (MPdot (mp,lab)) (mod_type mb) in
          let struc', cst =
            check_with_def (cst, ustate) env' struc (idl, wth) (MPdot(mp,lab)) (mod_delta mb)
          in
          let mb' = replace_module_body struc' (mod_delta mb) mb in
          before@(lab,SFBmodule mb')::after, cst
        | _ -> error_generative_module_expected lab
      end
  with
  | Not_found -> error_no_such_label lab mp

(* [mp] is the ambient modpath of [struc],
   [new_mp] is the path of the module to replace [idl] with *)
let rec check_with_mod (cst, ustate) env struc (idl,new_mp) mp reso =
  let lab,idl = match idl with
    | [] -> assert false
    | id::idl -> id, idl
  in
  try
    let before,spec,after = split_struc lab true struc in
    let env' = Modops.add_structure mp before reso env in
    let old = match spec with
      | SFBmodule mb -> mb
      | _ -> error_not_a_module_label lab
    in
    if List.is_empty idl then
      (* Toplevel module definition *)
      let new_mb = lookup_module new_mp env in
      let cst = match Mod_declarations.mod_expr old with
        | Abstract ->
          let mtb_old = module_type_of_module old in
          let cst = Subtyping.check_subtypes (cst, ustate) env' new_mp (MPdot (mp, lab)) mtb_old in
          cst
        | Algebraic (MENoFunctor (MEident(mp'))) ->
          check_modpath_equiv env' new_mp mp';
          cst
        | _ -> error_generative_module_expected lab
      in
      let mp' = MPdot (mp,lab) in
      let new_mb = strengthen_and_subst_module_body new_mp new_mb mp' false in
      (** TODO: check this is fine when new_mb is a functor *)
      let new_mb' = strengthen_module_body ~src:new_mp (mod_type new_mb) (mod_delta new_mb) new_mb in
      let subreso = mod_delta new_mb in
      (* we propagate the new equality in the rest of the signature
         with the identity substitution accompanied by the new resolver*)
      let id_subst = map_mp mp' mp' subreso in
      let new_after = subst_structure id_subst mp after in
      before @ (lab, SFBmodule new_mb') :: new_after, subreso, cst
    else
      (* Module definition of a sub-module *)
      let mp' = MPdot (mp,lab) in
      let old = match spec with
        | SFBmodule msb -> msb
        | _ -> error_not_a_module_label lab
      in
      begin match Mod_declarations.mod_expr old with
      | Abstract ->
        let struc = destr_nofunctor mp' (mod_type old) in
        let struc', subreso, cst =
          check_with_mod (cst, ustate) env' struc (idl,new_mp) mp' (mod_delta old)
        in
        let reso' = add_delta_resolver (mod_delta old) (upcast_delta_resolver mp' subreso) in
        let new_mb = replace_module_body struc' reso' old in
        let id_subst = map_mp mp' mp' reso' in
        let new_after = subst_structure id_subst mp after in
        before @ (lab, SFBmodule new_mb) :: new_after, subreso, cst
      | Algebraic (MENoFunctor (MEident mp0)) ->
        let () = check_modpath_equiv env' new_mp (rebuild_mp mp0 idl) in
        before@(lab,spec)::after, reso, cst
      | _ -> error_generative_module_expected lab
      end
  with
  | Not_found -> error_no_such_label lab mp

type 'a vm_handler = { vm_handler : env -> universes -> Constr.t -> 'a -> 'a * Vmlibrary.indirect_code }
type 'a vm_state = 'a * 'a vm_handler

let check_with ustate vmstate env mp (sign,reso,cst,vm) = function
  | WithDef(idl, (c, ctx)) ->
    let struc = destr_nofunctor mp sign in
    let univs = match ctx with None -> Monomorphic | Some uctx -> Polymorphic uctx in
    let vm, bcode = vmstate.vm_handler env univs c vm in
    let body = { w_def = c; w_univs = univs; w_bytecode = bcode } in
    let struc', cst = check_with_def (cst, ustate) env struc (idl, body) mp reso in
    NoFunctor struc', reso, cst, vm
  | WithMod(idl,new_mp) ->
    let struc = destr_nofunctor mp sign in
    let struc', subreso, cst = check_with_mod (cst, ustate) env struc (idl, new_mp) mp reso in
    let reso' = add_delta_resolver reso (upcast_delta_resolver mp subreso) in
    NoFunctor struc', reso', cst, vm

let check_with_alg ustate vmstate env mp (sign, alg, reso, cst, vm) wd =
  let struc, reso, cst, vm = check_with ustate vmstate env mp (sign, reso, cst, vm) wd in
  struc, MEwith (alg, wd), reso, cst, vm

let rec translate_apply ustate env inl mp subst (sign, reso, cst) args = match args with
| [] ->
  let sign = subst_signature subst mp sign in
  let reso = subst_codom_delta_resolver subst reso in
  (sign, reso, cst)
| mp1 :: args ->
  let farg_id, farg_b, sign = destr_functor sign in
  let farg_b =
    if is_empty_subst subst then farg_b
    else subst_modtype subst_codom subst (MPbound farg_id) farg_b
  in
  let cst = Subtyping.check_subtypes ~direct:true (cst, ustate) env mp1 (MPbound farg_id) farg_b in
  let mp_delta = discr_resolver mp1 (lookup_module mp1 env) in
  let mp_delta = inline_delta_resolver env inl mp1 farg_id farg_b mp_delta in
  let nsubst = map_mbid farg_id mp1 mp_delta in
  let subst = join subst nsubst in
  translate_apply ustate env inl mp subst (sign, reso, cst) args

(** Translation of a module struct entry :
    - We translate to a module when a [module_path] is given,
      otherwise to a module type.
    - The first output is the expanded signature
    - The second output is the algebraic expression, kept for the extraction.
*)

let rec decompose_apply accu = function
| MEapply (f, arg) -> decompose_apply (arg :: accu) f
| (MEident _ | MEwith _) as f -> f, accu

let rec translate_mse (cst, ustate) (vm, vmstate) env mpo inl me = match me with
  | MEident mp1 ->
    let mb = match mpo with
      | Some mp -> strengthen_and_subst_module_body mp1 (lookup_module mp1 env) mp false
      | None ->
        let mt = lookup_modtype mp1 env in
        module_body_of_type mt
    in
    mod_type mb, me, mod_delta mb, cst, vm
  | MEapply _ ->
    let fe, args = decompose_apply [] me in
    let (sign, alg, reso, cst, vm) = translate_mse (cst, ustate) (vm, vmstate) env mpo inl fe in
    let mp = match mpo with Some mp -> mp | None -> mp_from_mexpr fe in
    let (sign, reso, cst) = translate_apply ustate env inl mp empty_subst (sign, reso, cst) args in
    let alg = List.fold_left (fun accu arg -> MEapply (accu, arg)) alg args in
    (sign, alg, reso, cst, vm)
  | MEwith(me, with_decl) ->
    assert (Option.is_empty mpo); (* No 'with' syntax for modules *)
    let mp = mp_from_mexpr me in
    check_with_alg ustate vmstate env mp (translate_mse (cst, ustate) (vm, vmstate) env None inl me) with_decl

let mk_modtype = Mod_declarations.make_module_type

let rec translate_mse_funct (cst, ustate) (vm, vmstate) env ~is_mod mp inl mse = function
  | [] ->
    let sign,alg,reso,cst,vm = translate_mse (cst, ustate) (vm, vmstate) env (if is_mod then Some mp else None) inl mse in
    let sign,reso =
      if is_mod then sign,reso
      else subst_modtype_signature_and_resolver (mp_from_mexpr mse) mp sign reso in
    sign, MENoFunctor alg, reso, cst, vm
  | (mbid, ty, ty_inl) :: params ->
    let mp_id = MPbound mbid in
    let mtb, cst, vm = translate_modtype (cst, ustate) (vm, vmstate) env mp_id ty_inl ([],ty) in
    let env' = add_module_parameter mbid mtb env in
    let sign,alg,reso,cst,vm = translate_mse_funct (cst, ustate) (vm, vmstate) env' ~is_mod mp inl mse params in
    let alg' = MEMoreFunctor alg in
    MoreFunctor (mbid, mtb, sign), alg',reso, cst, vm

and translate_modtype state vmstate env mp inl (params,mte) =
  let sign,alg,reso,cst,vm = translate_mse_funct state vmstate env ~is_mod:false mp inl mte params in
  let mtb = mk_modtype sign reso in
  set_algebraic_type mtb alg, cst, vm

(** [finalize_module] :
    from an already-translated (or interactive) implementation and
    an (optional) signature entry, produces a final [module_body] *)

let finalize_module_alg (cst, ustate) (vm, vmstate) env mp (sign,alg,reso) restype = match restype with
  | None ->
    let impl = match alg with Some e -> Algebraic e | None -> FullStruct in
    let mb = make_module_body sign reso in
    let mb = set_implementation impl mb in
    mb, cst, vm
  | Some (params_mte,inl) ->
    let res_mtb, cst, vm = translate_modtype (cst, ustate) (vm, vmstate) env mp inl params_mte in
    let auto_mtb = Mod_declarations.make_module_body sign reso in
    (* This function is supposed to be called in a state where the current module
       is about to be closed, so all subcomponents of the module are already
       part of the environment. We only need to add the toplevel module entry. *)
    let env = Environ.shallow_add_module mp auto_mtb env in
    let cst = Subtyping.check_subtypes ~direct:true (cst, ustate) env mp mp res_mtb in
    let impl = match alg with
    | Some e -> Algebraic e
    | None ->
      let sign = match sign with
      | NoFunctor s -> s
      | MoreFunctor _ -> assert false (* All non-algebraic callers enforce this *)
      in
      Struct (reso,sign)
    in
    let mb = module_body_of_type res_mtb in
    let mb = set_implementation impl mb in
    mb,
    (** constraints from module body typing + subtyping + module type. *)
    cst,
    vm

let finalize_module univs vm env mp (sign, reso) typ =
  finalize_module_alg univs vm env mp (sign, None, reso) typ

let translate_module (cst, ustate) (vm, vmstate) env mp inl = function
  | MType (params,ty) ->
    let mtb, cst, vm = translate_modtype (cst, ustate) (vm, vmstate) env mp inl (params,ty) in
    module_body_of_type mtb, cst, vm
  | MExpr (params,mse,oty) ->
    let (sg,alg,reso,cst,vm) = translate_mse_funct (cst, ustate) (vm, vmstate) env ~is_mod:true mp inl mse params in
    let restype = Option.map (fun ty -> ((params,ty),inl)) oty in
    (* finalize_module_alg expects the subcomponents to be part of the environment *)
    let env = match sg with
    | NoFunctor struc -> Modops.add_structure mp struc reso env
    | MoreFunctor _ -> env
    in
    finalize_module_alg (cst, ustate) (vm, vmstate) env mp (sg,Some alg,reso) restype

(** We now forbid any Include of functors with restricted signatures.
    Otherwise, we could end with the creation of undesired axioms
    (see #3746). Note that restricted non-functorized modules are ok,
    thanks to strengthening. *)

let rec unfunct env = function
| NoFunctor me -> env, me
| MoreFunctor (mbid, mtb, me) ->
  let env = Modops.add_module_parameter mbid mtb env in
  unfunct env me

let rec forbid_incl_signed_functor env = function
  | MEapply(fe,_) -> forbid_incl_signed_functor env fe
  | MEwith _ -> assert false (* No 'with' syntax for modules *)
  | MEident mp1 ->
    let mb = lookup_module mp1 env in
    match mod_type mb, mod_type_alg mb, Mod_declarations.mod_expr mb with
    | MoreFunctor _, Some _, _ ->
      (* functor + restricted signature = error *)
      error_include_restricted_functor mp1
    | MoreFunctor _ as sign, None, Algebraic me ->
      (* functor, no signature yet, a definition which may be restricted *)
      let me = annotate_module_expression me sign in
      let env, me = unfunct env me in
      forbid_incl_signed_functor env me
    | _ -> ()

let rec translate_mse_include_module (cst, ustate) (vm, vmstate) env mp inl = function
  | MEident mp1 ->
    let mb = strengthen_and_subst_module_body mp1 (lookup_module mp1 env) mp true in
    let sign = clean_bounded_mod_expr (mod_type mb) in
    sign, (), mod_delta mb, cst, vm
  | MEapply _ as me ->
    let fe, args = decompose_apply [] me in
    let (sign, (), reso, cst, vm) = translate_mse_include_module (cst, ustate) (vm, vmstate) env mp inl fe in
    let (sign, reso, cst) = translate_apply ustate env inl mp empty_subst (sign, reso, cst) args in
    (sign, (), reso, cst, vm)
  | MEwith _ -> assert false (* No 'with' syntax for modules *)

let translate_mse_include is_mod (cst, ustate) (vm, vmstate) env mp inl me =
  if is_mod then
    let () = forbid_incl_signed_functor env me in
    translate_mse_include_module (cst, ustate) (vm, vmstate) env mp inl me
  else
    let mtb, cst, vm = translate_modtype (cst, ustate) (vm, vmstate) env mp inl ([],me) in
    let sign = clean_bounded_mod_expr (mod_type mtb) in
    sign, (), mod_delta mtb, cst, vm
