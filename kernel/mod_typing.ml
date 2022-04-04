(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
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
open Entries
open Environ
open Modops
open Mod_subst

type 'alg translation =
  module_signature * 'alg * delta_resolver * Univ.Constraints.t

let rec mp_from_mexpr = function
  | MEident mp -> mp
  | MEapply (expr,_) -> mp_from_mexpr expr
  | MEwith (expr,_) -> mp_from_mexpr expr

let is_modular = function
  | SFBmodule _ | SFBmodtype _ -> true
  | SFBconst _ | SFBmind _ -> false

(** Split a [structure_body] at some label corresponding to
    a modular definition or not. *)

let split_struc k m struc =
  let rec split rev_before = function
    | [] -> raise Not_found
    | (k',b)::after when Label.equal k k' && (is_modular b) == (m : bool) ->
      List.rev rev_before,b,after
    | h::tail -> split (h::rev_before) tail
  in split [] struc

let discr_resolver mtb = match mtb.mod_type with
  | NoFunctor _ -> mtb.mod_delta
  | MoreFunctor _ -> empty_delta_resolver

let rec rebuild_mp mp l =
  match l with
  | []-> mp
  | i::r -> rebuild_mp (MPdot(mp,Label.of_id i)) r

let infer_gen_conv state env c1 c2 =
  Reduction.generic_conv Reduction.CONV ~l2r:false (fun _ -> None) TransparentState.full env state c1 c2

let infer_gen_conv_leq state env c1 c2 =
  Reduction.generic_conv Reduction.CUMUL ~l2r:false (fun _ -> None) TransparentState.full env state c1 c2

let rec check_with_def (cst, ustate) env struc (idl,(c,ctx)) mp reso =
  let lab,idl = match idl with
    | [] -> assert false
    | id::idl -> Label.of_id id, idl
  in
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
      let univs, ctx' =
        match cb.const_universes, ctx with
        | Monomorphic, None ->
          let cst = match cb.const_body with
            | Undef _ | OpaqueDef _ ->
              let j = Typeops.infer env' c in
              assert (j.uj_val == c); (* relevances should already be correct here *)
              let typ = cb.const_type in
              let cst = infer_gen_conv_leq (cst, ustate) env' j.uj_type typ in
              cst
            | Def c' ->
              infer_gen_conv (cst, ustate) env' c c'
            | Primitive _ ->
              error_incorrect_with_constraint lab
          in
          Monomorphic, cst
        | Polymorphic uctx, Some ctx ->
          let () =
            if not (UGraph.check_subtype (Environ.universes env) uctx ctx) then
              error_incorrect_with_constraint lab
          in
          (** Terms are compared in a context with De Bruijn universe indices *)
          let env' = Environ.push_context ~strict:false (Univ.AbstractContext.repr uctx) env in
          let () = match cb.const_body with
            | Undef _ | OpaqueDef _ ->
              let j = Typeops.infer env' c in
              assert (j.uj_val == c); (* relevances should already be correct here *)
              let typ = cb.const_type in
              begin
                try Reduction.conv_leq env' j.uj_type typ
                with Reduction.NotConvertible -> error_incorrect_with_constraint lab
              end
            | Def c' ->
              begin
                try Reduction.conv env' c c'
                with Reduction.NotConvertible -> error_incorrect_with_constraint lab
              end
            | Primitive _ ->
              error_incorrect_with_constraint lab
          in
          Polymorphic ctx, cst
        | _ -> error_incorrect_with_constraint lab
      in
      let def = Def c in
      (*      let ctx' = Univ.UContext.make (newus, cst) in *)
      let cb' =
        { cb with
          const_body = def;
          const_universes = univs ;
          const_body_code =
              (Vmbytegen.compile_constant_body ~fail_on_error:false env' cb.const_universes def) }
      in
      before@(lab,SFBconst(cb'))::after, ctx'
    else
      (* Definition inside a sub-module *)
      let mb = match spec with
        | SFBmodule mb -> mb
        | _ -> error_not_a_module_label lab
      in
      begin match mb.mod_expr with
        | Abstract ->
          let struc = Modops.destr_nofunctor (MPdot (mp,lab)) mb.mod_type in
          let struc', cst =
            check_with_def (cst, ustate) env' struc (idl,(c,ctx)) (MPdot(mp,lab)) mb.mod_delta
          in
          let mb' = { mb with
                      mod_type = NoFunctor struc';
                      mod_type_alg = None }
          in
          before@(lab,SFBmodule mb')::after, cst
        | _ -> error_generative_module_expected lab
      end
  with
  | Not_found -> error_no_such_label lab mp
  | Reduction.NotConvertible -> error_incorrect_with_constraint lab

let rec check_with_mod (cst, ustate) env struc (idl,new_mp) mp reso =
  let lab,idl = match idl with
    | [] -> assert false
    | id::idl -> Label.of_id id, idl
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
      let new_mtb = module_type_of_module new_mb in
      let cst = match old.mod_expr with
        | Abstract ->
          let mtb_old = module_type_of_module old in
          let cst = Subtyping.check_subtypes (cst, ustate) env' new_mtb mtb_old in
          cst
        | Algebraic (NoFunctor (MEident(mp'))) ->
          check_modpath_equiv env' new_mp mp';
          cst
        | _ -> error_generative_module_expected lab
      in
      let mp' = MPdot (mp,lab) in
      let new_mb = strengthen_and_subst_module_body new_mb mp' false in
      let new_mb' =
        { new_mb with
          mod_mp = mp';
          mod_expr = Algebraic (NoFunctor (MEident new_mp));
        }
      in
      let new_reso = add_delta_resolver reso new_mb.mod_delta in
      (* we propagate the new equality in the rest of the signature
         with the identity substitution accompanied by the new resolver*)
      let id_subst = map_mp mp' mp' new_mb.mod_delta in
      let new_after = subst_structure id_subst after in
      before@(lab,SFBmodule new_mb')::new_after, new_reso, cst
    else
      (* Module definition of a sub-module *)
      let mp' = MPdot (mp,lab) in
      let old = match spec with
        | SFBmodule msb -> msb
        | _ -> error_not_a_module_label lab
      in
      begin match old.mod_expr with
      | Abstract ->
        let struc = destr_nofunctor mp' old.mod_type in
        let struc',reso',cst =
          check_with_mod (cst, ustate) env' struc (idl,new_mp) mp' old.mod_delta
        in
        let new_mb =
          { old with
            mod_type = NoFunctor struc';
            mod_type_alg = None;
            mod_delta = reso' }
        in
        let new_reso = add_delta_resolver reso reso' in
        let id_subst = map_mp mp' mp' reso' in
        let new_after = subst_structure id_subst after in
        before@(lab,SFBmodule new_mb)::new_after, new_reso, cst
      | Algebraic (NoFunctor (MEident mp0)) ->
        let mpnew = rebuild_mp mp0 idl in
        check_modpath_equiv env' mpnew mp;
        before@(lab,spec)::after, reso, cst
      | _ -> error_generative_module_expected lab
      end
  with
  | Not_found -> error_no_such_label lab mp
  | Reduction.NotConvertible -> error_incorrect_with_constraint lab

let check_with ustate env mp (sign,reso,cst) = function
  | WithDef(idl, (c, ctx)) ->
    let struc = destr_nofunctor mp sign in
    let struc', cst = check_with_def (cst, ustate) env struc (idl, (c, ctx)) mp reso in
    NoFunctor struc', reso, cst
  | WithMod(idl,new_mp) ->
    let struc = destr_nofunctor mp sign in
    let struc',reso',cst = check_with_mod (cst, ustate) env struc (idl,new_mp) mp reso in
    NoFunctor struc', reso', cst

let check_with_alg ustate env mp (sign,alg,reso,cst) wd =
  let struc, reso, cst = check_with ustate env mp (sign, reso, cst) wd in
  struc, MEwith (alg, wd), reso, cst

let translate_apply ustate env inl (sign,alg,reso,cst) mp1 mkalg =
  let farg_id, farg_b, fbody_b = destr_functor sign in
  let mtb = module_type_of_module (lookup_module mp1 env) in
  let cst = Subtyping.check_subtypes (cst, ustate) env mtb farg_b in
  let mp_delta = discr_resolver mtb in
  let mp_delta = inline_delta_resolver env inl mp1 farg_id farg_b mp_delta in
  let subst = map_mbid farg_id mp1 mp_delta in
  let body = subst_signature subst fbody_b in
  let alg' = mkalg alg mp1 in
  let reso' = subst_codom_delta_resolver subst reso in
  body, alg', reso', cst

(** Translation of a module struct entry :
    - We translate to a module when a [module_path] is given,
      otherwise to a module type.
    - The first output is the expanded signature
    - The second output is the algebraic expression, kept for the extraction.
*)

let mk_alg_app alg arg = MEapply (alg,arg)

let rec translate_mse (cst, ustate) env mpo inl = function
  | MEident mp1 as me ->
    let mb = match mpo with
      | Some mp -> strengthen_and_subst_module_body (lookup_module mp1 env) mp false
      | None ->
        let mt = lookup_modtype mp1 env in
        module_body_of_type mt.mod_mp mt
    in
    mb.mod_type, me, mb.mod_delta, cst
  | MEapply (fe,mp1) ->
    translate_apply ustate env inl (translate_mse (cst, ustate) env mpo inl fe) mp1 mk_alg_app
  |MEwith(me, with_decl) ->
    assert (Option.is_empty mpo); (* No 'with' syntax for modules *)
    let mp = mp_from_mexpr me in
    check_with_alg ustate env mp (translate_mse (cst, ustate) env None inl me) with_decl

let mk_mod mp e ty reso =
  { mod_mp = mp;
    mod_expr = e;
    mod_type = ty;
    mod_type_alg = None;
    mod_delta = reso;
    mod_retroknowledge = ModBodyRK []; }

let mk_modtype mp ty reso =
  let mb = mk_mod mp Abstract ty reso in
  { mb with mod_expr = (); mod_retroknowledge = ModTypeRK }

let rec translate_mse_funct (cst, ustate) env ~is_mod mp inl mse = function
  |[] ->
    let sign,alg,reso,cst = translate_mse (cst, ustate) env (if is_mod then Some mp else None) inl mse in
    let sign,reso =
      if is_mod then sign,reso
      else subst_modtype_signature_and_resolver (mp_from_mexpr mse) mp sign reso in
    sign, NoFunctor alg, reso, cst
  |(mbid, ty, ty_inl) :: params ->
    let mp_id = MPbound mbid in
    let mtb, cst = translate_modtype (cst, ustate) env mp_id ty_inl ([],ty) in
    let env' = add_module_type mp_id mtb env in
    let sign,alg,reso,cst = translate_mse_funct (cst, ustate) env' ~is_mod mp inl mse params in
    let alg' = MoreFunctor (mbid,mtb,alg) in
    MoreFunctor (mbid, mtb, sign), alg',reso, cst

and translate_modtype state env mp inl (params,mte) =
  let sign,alg,reso,cst = translate_mse_funct state env ~is_mod:false mp inl mte params in
  let mtb = mk_modtype mp sign reso in
  { mtb with mod_type_alg = Some alg }, cst

(** [finalize_module] :
    from an already-translated (or interactive) implementation and
    an (optional) signature entry, produces a final [module_body] *)

let finalize_module (cst, ustate) env mp (sign,alg,reso) restype = match restype with
  | None ->
    let impl = match alg with Some e -> Algebraic e | None -> FullStruct in
    mk_mod mp impl sign reso, cst
  | Some (params_mte,inl) ->
    let res_mtb, cst = translate_modtype (cst, ustate) env mp inl params_mte in
    let auto_mtb = mk_modtype mp sign reso in
    let cst = Subtyping.check_subtypes (cst, ustate) env auto_mtb res_mtb in
    let impl = match alg with Some e -> Algebraic e | None -> Struct sign in
    { res_mtb with
      mod_mp = mp;
      mod_expr = impl;
      mod_retroknowledge = ModBodyRK [];
    },
    (** constraints from module body typing + subtyping + module type. *)
    cst

let translate_module (cst, ustate) env mp inl = function
  | MType (params,ty) ->
    let mtb, cst = translate_modtype (cst, ustate) env mp inl (params,ty) in
    module_body_of_type mp mtb, cst
  |MExpr (params,mse,oty) ->
    let (sg,alg,reso,cst) = translate_mse_funct (cst, ustate) env ~is_mod:true mp inl mse params in
    let restype = Option.map (fun ty -> ((params,ty),inl)) oty in
    finalize_module (cst, ustate) env mp (sg,Some alg,reso) restype

(** We now forbid any Include of functors with restricted signatures.
    Otherwise, we could end with the creation of undesired axioms
    (see #3746). Note that restricted non-functorized modules are ok,
    thanks to strengthening. *)

let rec unfunct = function
  | NoFunctor me -> me
  | MoreFunctor(_,_,me) -> unfunct me

let rec forbid_incl_signed_functor env = function
  | MEapply(fe,_) -> forbid_incl_signed_functor env fe
  | MEwith _ -> assert false (* No 'with' syntax for modules *)
  | MEident mp1 ->
    let mb = lookup_module mp1 env in
    match mb.mod_type, mb.mod_type_alg, mb.mod_expr with
    | MoreFunctor _, Some _, _ ->
      (* functor + restricted signature = error *)
      error_include_restricted_functor mp1
    | MoreFunctor _, None, Algebraic me ->
      (* functor, no signature yet, a definition which may be restricted *)
      forbid_incl_signed_functor env (unfunct me)
    |_ -> ()

let rec translate_mse_include_module (cst, ustate) env mp inl = function
  | MEident mp1 ->
    let mb = strengthen_and_subst_module_body (lookup_module mp1 env) mp true in
    let sign = clean_bounded_mod_expr mb.mod_type in
    sign,(),mb.mod_delta,cst
  | MEapply (fe,arg) ->
    let ftrans = translate_mse_include_module (cst, ustate) env mp inl fe in
    translate_apply ustate env inl ftrans arg (fun _ _ -> ())
  | MEwith _ -> assert false (* No 'with' syntax for modules *)

let translate_mse_include is_mod (cst, ustate) env mp inl me =
  if is_mod then
    let () = forbid_incl_signed_functor env me in
    translate_mse_include_module (cst, ustate) env mp inl me
  else
    let mtb, cst = translate_modtype (cst, ustate) env mp inl ([],me) in
    let sign = clean_bounded_mod_expr mtb.mod_type in
    sign, (), mtb.mod_delta, cst
