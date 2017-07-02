(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
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
  module_signature * 'alg * delta_resolver * Univ.ContextSet.t

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

let (+++) = Univ.ContextSet.union

let rec check_with_def env struc (idl,(c,ctx)) mp equiv =
  let lab,idl = match idl with
    | [] -> assert false
    | id::idl -> Label.of_id id, idl
  in
  try
    let modular = not (List.is_empty idl) in
    let before,spec,after = split_struc lab modular struc in
    let env' = Modops.add_structure mp before equiv env in
    if List.is_empty idl then
      (* Toplevel definition *)
      let cb = match spec with
	| SFBconst cb -> cb
	| _ -> error_not_a_constant lab
      in
      (* In the spirit of subtyping.check_constant, we accept
         any implementations of parameters and opaques terms,
	 as long as they have the right type *)
      let uctx = Declareops.universes_of_constant (opaque_tables env) cb in
      let uctx = (* Context of the spec *)
        match cb.const_universes with
        | Monomorphic_const _ -> uctx
        | Polymorphic_const auctx ->
	  Univ.instantiate_univ_context auctx
      in
      let c', univs, ctx' = 
	if not (Declareops.constant_is_polymorphic cb) then
	  let env' = Environ.push_context ~strict:true uctx env' in
	  let env' = Environ.push_context ~strict:true ctx env' in
	  let c',cst = match cb.const_body with
	    | Undef _ | OpaqueDef _ ->
	      let j = Typeops.infer env' c in
	      let typ = Typeops.type_of_constant_type env' cb.const_type in
	      let cst' = Reduction.infer_conv_leq env' (Environ.universes env')
						j.uj_type typ in
	      j.uj_val, cst'
	    | Def cs ->
	       let c' = Mod_subst.force_constr cs in
	         c, Reduction.infer_conv env' (Environ.universes env') c c'
	  in c', Monomorphic_const ctx, Univ.ContextSet.add_constraints cst (Univ.ContextSet.of_context ctx)
	else
	  let cus, ccst = Univ.UContext.dest uctx in
	  let newus, cst = Univ.UContext.dest ctx in
	  let () =
	    if not (Univ.Instance.length cus == Univ.Instance.length newus) then
	      error_incorrect_with_constraint lab
	  in
	  let inst = Univ.Instance.append cus newus in
	  let csti = Univ.enforce_eq_instances cus newus cst in
	  let csta = Univ.Constraint.union csti ccst in
	  let env' = Environ.push_context ~strict:false (Univ.UContext.make (inst, csta)) env in
	  let () = if not (UGraph.check_constraints cst (Environ.universes env')) then
		     error_incorrect_with_constraint lab
	  in
	  let cst = match cb.const_body with
	    | Undef _ | OpaqueDef _ ->
	      let j = Typeops.infer env' c in
	      let typ = Typeops.type_of_constant_type env' cb.const_type in
	      let typ = Vars.subst_instance_constr cus typ in
	      let cst' = Reduction.infer_conv_leq env' (Environ.universes env')
						j.uj_type typ in
	      cst'
	    | Def cs ->
	       let c' = Vars.subst_instance_constr cus (Mod_subst.force_constr cs) in
	       let cst' = Reduction.infer_conv env' (Environ.universes env') c c' in
	        cst'
	  in
	    if not (Univ.Constraint.is_empty cst) then
	      error_incorrect_with_constraint lab;
	    let subst, ctx = Univ.abstract_universes ctx in
	      Vars.subst_univs_level_constr subst c, Polymorphic_const ctx, Univ.ContextSet.empty
      in
      let def = Def (Mod_subst.from_val c') in
(*      let ctx' = Univ.UContext.make (newus, cst) in *)
      let cb' =
	{ cb with
	  const_body = def;
          const_universes = univs ;
	  const_body_code = Option.map Cemitcodes.from_val
                              (compile_constant_body env' cb.const_universes def) }
      in
      before@(lab,SFBconst(cb'))::after, c', ctx'
    else
      (* Definition inside a sub-module *)
      let mb = match spec with
	| SFBmodule mb -> mb
	| _ -> error_not_a_module (Label.to_string lab)
      in
      begin match mb.mod_expr with
      | Abstract ->
        let struc = Modops.destr_nofunctor mb.mod_type in
        let struc',c',cst =
          check_with_def env' struc (idl,(c,ctx)) (MPdot(mp,lab)) mb.mod_delta
        in
        let mb' = { mb with
          mod_type = NoFunctor struc';
	  mod_type_alg = None }
        in
	before@(lab,SFBmodule mb')::after, c', cst
      | _ -> error_generative_module_expected lab
      end
  with
  | Not_found -> error_no_such_label lab
  | Reduction.NotConvertible -> error_incorrect_with_constraint lab

let rec check_with_mod env struc (idl,mp1) mp equiv =
  let lab,idl = match idl with
    | [] -> assert false
    | id::idl -> Label.of_id id, idl
  in
  try
    let before,spec,after = split_struc lab true struc in
    let env' = Modops.add_structure mp before equiv env in
    let old = match spec with
      | SFBmodule mb -> mb
      | _ -> error_not_a_module (Label.to_string lab)
    in
    if List.is_empty idl then
      (* Toplevel module definition *)
      let mb_mp1 = lookup_module mp1 env in
      let mtb_mp1 = module_type_of_module mb_mp1 in
      let cst = match old.mod_expr with
	| Abstract ->
	  begin
            try
              let mtb_old = module_type_of_module old in
              let chk_cst = Subtyping.check_subtypes env' mtb_mp1 mtb_old in
              Univ.ContextSet.add_constraints chk_cst old.mod_constraints
	    with Failure _ ->
              (* TODO: where can a Failure come from ??? *)
              error_incorrect_with_constraint lab
	  end
	| Algebraic (NoFunctor (MEident(mp'))) ->
	  check_modpath_equiv env' mp1 mp';
	  old.mod_constraints
	| _ -> error_generative_module_expected lab
      in
      let mp' = MPdot (mp,lab) in
      let new_mb = strengthen_and_subst_mb mb_mp1 mp' false in
      let new_mb' =
        { new_mb with
          mod_mp = mp';
          mod_expr = Algebraic (NoFunctor (MEident mp1));
          mod_constraints = cst }
      in
      let new_equiv = add_delta_resolver equiv new_mb.mod_delta in
      (* we propagate the new equality in the rest of the signature
	 with the identity substitution accompagned by the new resolver*)
      let id_subst = map_mp mp' mp' new_mb.mod_delta in
      let new_after = subst_structure id_subst after in
      before@(lab,SFBmodule new_mb')::new_after, new_equiv, cst
    else
      (* Module definition of a sub-module *)
      let mp' = MPdot (mp,lab) in
      let old = match spec with
        | SFBmodule msb -> msb
	| _ -> error_not_a_module (Label.to_string lab)
      in
      begin match old.mod_expr with
      | Abstract ->
        let struc = destr_nofunctor old.mod_type in
	let struc',equiv',cst =
          check_with_mod env' struc (idl,mp1) mp' old.mod_delta
        in
	let new_mb =
          { old with
            mod_type = NoFunctor struc';
            mod_type_alg = None;
            mod_delta = equiv' }
        in
	let new_equiv = add_delta_resolver equiv equiv' in
	let id_subst = map_mp mp' mp' equiv' in
        let new_after = subst_structure id_subst after in
	before@(lab,SFBmodule new_mb)::new_after, new_equiv, cst
      | Algebraic (NoFunctor (MEident mp0)) ->
	let mpnew = rebuild_mp mp0 idl in
	check_modpath_equiv env' mpnew mp;
	before@(lab,spec)::after, equiv, Univ.ContextSet.empty
      | _ -> error_generative_module_expected lab
      end
  with
  | Not_found -> error_no_such_label lab
  | Reduction.NotConvertible -> error_incorrect_with_constraint lab

let check_with env mp (sign,alg,reso,cst) = function
  |WithDef(idl,c) ->
    let struc = destr_nofunctor sign in
    let struc',c',cst' = check_with_def env struc (idl,c) mp reso in
    let wd' = WithDef (idl,(c',Univ.ContextSet.to_context cst')) in
    NoFunctor struc', MEwith (alg,wd'), reso, cst+++cst'
  |WithMod(idl,mp1) as wd ->
    let struc = destr_nofunctor sign in
    let struc',reso',cst' = check_with_mod env struc (idl,mp1) mp reso in
    NoFunctor struc', MEwith (alg,wd), reso', cst+++cst'

let translate_apply env inl (sign,alg,reso,cst1) mp1 mkalg =
  let farg_id, farg_b, fbody_b = destr_functor sign in
  let mtb = module_type_of_module (lookup_module mp1 env) in
  let cst2 = Subtyping.check_subtypes env mtb farg_b in
  let mp_delta = discr_resolver mtb in
  let mp_delta = inline_delta_resolver env inl mp1 farg_id farg_b mp_delta in
  let subst = map_mbid farg_id mp1 mp_delta in
  let body = subst_signature subst fbody_b in
  let alg' = mkalg alg mp1 in
  let reso' = subst_codom_delta_resolver subst reso in
  body,alg',reso', Univ.ContextSet.add_constraints cst2 cst1

(** Translation of a module struct entry :
    - We translate to a module when a [module_path] is given,
      otherwise to a module type.
    - The first output is the expanded signature
    - The second output is the algebraic expression, kept for the extraction.
*)

let mk_alg_app alg arg = MEapply (alg,arg)

let rec translate_mse env mpo inl = function
  |MEident mp1 as me ->
    let mb = match mpo with
      |Some mp -> strengthen_and_subst_mb (lookup_module mp1 env) mp false
      |None -> lookup_modtype mp1 env
    in
    mb.mod_type, me, mb.mod_delta, Univ.ContextSet.empty
  |MEapply (fe,mp1) ->
    translate_apply env inl (translate_mse env mpo inl fe) mp1 mk_alg_app
  |MEwith(me, with_decl) ->
    assert (mpo == None); (* No 'with' syntax for modules *)
    let mp = mp_from_mexpr me in
    check_with env mp (translate_mse env None inl me) with_decl

let mk_mod mp e ty cst reso =
  { mod_mp = mp;
    mod_expr = e;
    mod_type = ty;
    mod_type_alg = None;
    mod_constraints = cst;
    mod_delta = reso;
    mod_retroknowledge = [] }

let mk_modtype mp ty cst reso = mk_mod mp Abstract ty cst reso

let rec translate_mse_funct env mpo inl mse = function
  |[] ->
    let sign,alg,reso,cst = translate_mse env mpo inl mse in
    sign, NoFunctor alg, reso, cst
  |(mbid, ty) :: params ->
    let mp_id = MPbound mbid in
    let mtb = translate_modtype env mp_id inl ([],ty) in
    let env' = add_module_type mp_id mtb env in
    let sign,alg,reso,cst = translate_mse_funct env' mpo inl mse params in
    let alg' = MoreFunctor (mbid,mtb,alg) in
    MoreFunctor (mbid, mtb, sign), alg',reso, cst +++ mtb.mod_constraints

and translate_modtype env mp inl (params,mte) =
  let sign,alg,reso,cst = translate_mse_funct env None inl mte params in
  let mtb = mk_modtype (mp_from_mexpr mte) sign cst reso in
  let mtb' = subst_modtype_and_resolver mtb mp in
  { mtb' with mod_type_alg = Some alg }

(** [finalize_module] :
    from an already-translated (or interactive) implementation and
    an (optional) signature entry, produces a final [module_body] *)

let finalize_module env mp (sign,alg,reso,cst) restype = match restype with
  |None ->
    let impl = match alg with Some e -> Algebraic e | None -> FullStruct in
    mk_mod mp impl sign cst reso
  |Some (params_mte,inl) ->
    let res_mtb = translate_modtype env mp inl params_mte in
    let auto_mtb = mk_modtype mp sign Univ.ContextSet.empty reso in
    let cst' = Subtyping.check_subtypes env auto_mtb res_mtb in
    let impl = match alg with Some e -> Algebraic e | None -> Struct sign in
    { res_mtb with
      mod_mp = mp;
      mod_expr = impl;
      (** cst from module body typing,
          cst' from subtyping,
          constraints from module type. *)
      mod_constraints =
        Univ.ContextSet.add_constraints cst' (cst +++ res_mtb.mod_constraints) }

let translate_module env mp inl = function
  |MType (params,ty) ->
    let mtb = translate_modtype env mp inl (params,ty) in
    module_body_of_type mp mtb
  |MExpr (params,mse,oty) ->
    let (sg,alg,reso,cst) = translate_mse_funct env (Some mp) inl mse params in
    let restype = Option.map (fun ty -> ((params,ty),inl)) oty in
    finalize_module env mp (sg,Some alg,reso,cst) restype

(** We now forbid any Include of functors with restricted signatures.
    Otherwise, we could end with the creation of undesired axioms
    (see #3746). Note that restricted non-functorized modules are ok,
    thanks to strengthening. *)

let rec unfunct = function
  |NoFunctor me -> me
  |MoreFunctor(_,_,me) -> unfunct me

let rec forbid_incl_signed_functor env = function
  |MEapply(fe,_) -> forbid_incl_signed_functor env fe
  |MEwith _ -> assert false (* No 'with' syntax for modules *)
  |MEident mp1 ->
    let mb = lookup_module mp1 env in
    match mb.mod_type, mb.mod_type_alg, mb.mod_expr with
    |MoreFunctor _, Some _, _ ->
      (* functor + restricted signature = error *)
      error_include_restricted_functor mp1
    |MoreFunctor _, None, Algebraic me ->
      (* functor, no signature yet, a definition which may be restricted *)
      forbid_incl_signed_functor env (unfunct me)
    |_ -> ()

let rec translate_mse_inclmod env mp inl = function
  |MEident mp1 ->
    let mb = strengthen_and_subst_mb (lookup_module mp1 env) mp true in
    let sign = clean_bounded_mod_expr mb.mod_type in
    sign,(),mb.mod_delta,Univ.ContextSet.empty
  |MEapply (fe,arg) ->
    let ftrans = translate_mse_inclmod env mp inl fe in
    translate_apply env inl ftrans arg (fun _ _ -> ())
  |MEwith _ -> assert false (* No 'with' syntax for modules *)

let translate_mse_incl is_mod env mp inl me =
  if is_mod then
    let () = forbid_incl_signed_functor env me in
    translate_mse_inclmod env mp inl me
  else
    let mtb = translate_modtype env mp inl ([],me) in
    let sign = clean_bounded_mod_expr mtb.mod_type in
    sign,(),mtb.mod_delta,mtb.mod_constraints
