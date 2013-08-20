(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
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

exception Not_path

let path_of_mexpr = function
  | MSEident mp -> mp
  | _ -> raise Not_path

let rec mp_from_mexpr = function
  | MSEident mp -> mp
  | MSEapply (expr,_) -> mp_from_mexpr expr
  | MSEfunctor (_,_,expr) -> mp_from_mexpr expr
  | MSEwith (expr,_) -> mp_from_mexpr expr

let is_modular = function
  | SFBmodule _ | SFBmodtype _ -> true
  | SFBconst _ | SFBmind _ -> false

(** Split a [structure_body] at some label corresponding to
    a modular definition or not. *)

let split_sign k m struc =
  let rec split rev_before = function
    | [] -> raise Not_found
    | (k',b)::after when Label.equal k k' && (is_modular b) == (m : bool) ->
      List.rev rev_before,b,after
    | h::tail -> split (h::rev_before) tail
  in split [] struc

let discr_resolver mtb = match mtb.typ_expr with
  | SEBstruct _ -> mtb.typ_delta
  | _ -> empty_delta_resolver (* when mp is a functor *)

let rec rebuild_mp mp l =
  match l with
  | []-> mp
  | i::r -> rebuild_mp (MPdot(mp,Label.of_id i)) r

let (+++) = Univ.union_constraints

let rec check_with_def env sign (idl,c) mp equiv =
  let sig_b = match sign with
    | SEBstruct(sig_b) -> sig_b
    | _ -> error_signature_expected sign
  in
  let lab,idl = match idl with
    | [] -> assert false
    | id::idl -> Label.of_id id, idl
  in
  try
    let modular = not (List.is_empty idl) in
    let before,spec,after = split_sign lab modular sig_b in
    let env' = Modops.add_signature mp before equiv env in
    if List.is_empty idl then
      (* Toplevel definition *)
      let cb = match spec with
	| SFBconst cb -> cb
	| _ -> error_not_a_constant lab
      in
      (* In the spirit of subtyping.check_constant, we accept
         any implementations of parameters and opaques terms,
	 as long as they have the right type *)
      let def,cst = match cb.const_body with
	| Undef _ | OpaqueDef _ ->
	  let j,cst1 = Typeops.infer env' c in
	  let typ = Typeops.type_of_constant_type env' cb.const_type in
	  let cst2 = Reduction.conv_leq env' j.uj_type typ in
	  let cst = Future.force cb.const_constraints +++ cst1 +++ cst2 in
	  let def = Def (Lazyconstr.from_val j.uj_val) in
	  def,cst
	| Def cs ->
	  let cst1 = Reduction.conv env' c (Lazyconstr.force cs) in
	  let cst = Future.force cb.const_constraints +++ cst1 in
	  let def = Def (Lazyconstr.from_val c) in
	  def,cst
      in
      let cb' =
	{ cb with
	  const_body = def;
	  const_body_code = Cemitcodes.from_val (compile_constant_body env' def);
	  const_constraints = Future.from_val cst }
      in
      SEBstruct(before@(lab,SFBconst(cb'))::after),cb',cst
    else
      (* Definition inside a sub-module *)
      let mb = match spec with
	| SFBmodule mb -> mb
	| _ -> error_not_a_module (Label.to_string lab)
      in
      begin match mb.mod_expr with
      | Some _ -> error_generative_module_expected lab
      | None ->
	let sign,cb,cst =
          check_with_def env' mb.mod_type (idl,c) (MPdot(mp,lab)) mb.mod_delta
        in
        let mb' = { mb with
          mod_type = sign;
	  mod_type_alg = None }
        in
	SEBstruct(before@(lab,SFBmodule mb')::after),cb,cst
      end
  with
  | Not_found -> error_no_such_label lab
  | Reduction.NotConvertible -> error_incorrect_with_constraint lab

let rec check_with_mod env sign (idl,mp1) mp equiv =
  let sig_b = match sign with
    | SEBstruct(sig_b) -> sig_b
    | _ -> error_signature_expected sign
  in
  let lab,idl = match idl with
    | [] -> assert false
    | id::idl -> Label.of_id id, idl
  in
  try
    let before,spec,after = split_sign lab true sig_b in
    let env' = Modops.add_signature mp before equiv env in
    let old = match spec with
      | SFBmodule mb -> mb
      | _ -> error_not_a_module (Label.to_string lab)
    in
    if List.is_empty idl then
      (* Toplevel module definition *)
      let mb_mp1 = lookup_module mp1 env in
      let mtb_mp1 = module_type_of_module None mb_mp1  in
      let cst = match old.mod_expr with
	| None ->
	  begin
            try
              let mtb_old = module_type_of_module None old in
              Subtyping.check_subtypes env' mtb_mp1 mtb_old
                +++ old.mod_constraints
	    with Failure _ -> error_incorrect_with_constraint lab
	  end
	| Some (SEBident(mp')) ->
	  check_modpath_equiv env' mp1 mp';
	  old.mod_constraints
	| _ ->  error_generative_module_expected lab
      in
      let mp' = MPdot (mp,lab) in
      let new_mb = strengthen_and_subst_mb mb_mp1 mp' false in
      let new_mb' = {new_mb with
        mod_mp = mp';
        mod_expr = Some (SEBident mp1);
        mod_constraints = cst }
      in
      (* we propagate the new equality in the rest of the signature
	 with the identity substitution accompagned by the new resolver*)
      let id_subst = map_mp mp' mp' new_mb.mod_delta in
      SEBstruct(before@(lab,SFBmodule new_mb')::subst_signature id_subst after),
      add_delta_resolver equiv new_mb.mod_delta,cst
    else
      (* Module definition of a sub-module *)
      let mp' = MPdot (mp,lab) in
      let old = match spec with
        | SFBmodule msb -> msb
	| _ -> error_not_a_module (Label.to_string lab)
      in
      begin match old.mod_expr with
      | None ->
	let sign,equiv',cst =
	  check_with_mod env' old.mod_type (idl,mp1) mp' old.mod_delta in
	let new_equiv = add_delta_resolver equiv equiv' in
	let new_mb = { old with
          mod_type = sign;
          mod_type_alg = None;
          mod_delta = equiv'}
	in
	let id_subst = map_mp mp' mp' equiv' in
	SEBstruct(before@(lab,SFBmodule new_mb)::subst_signature id_subst after),
	new_equiv,cst
      | Some (SEBident mp0) ->
	let mpnew = rebuild_mp mp0 idl in
	check_modpath_equiv env' mpnew mp;
	SEBstruct(before@(lab,spec)::after),equiv,Univ.empty_constraint
      | _ -> error_generative_module_expected lab
      end
  with
  | Not_found -> error_no_such_label lab
  | Reduction.NotConvertible -> error_incorrect_with_constraint lab

let check_with env sign with_decl alg_sign mp equiv =
  let sign,wd,equiv,cst= match with_decl with
    | With_Definition (idl,c) ->
	let sign,cb,cst = check_with_def env sign (idl,c) mp equiv in
	sign,With_definition_body(idl,cb),equiv,cst
    | With_Module (idl,mp1) ->
	let sign,equiv,cst = check_with_mod env sign (idl,mp1) mp equiv in
	sign,With_module_body(idl,mp1),equiv,cst
  in
  match alg_sign with
  | None -> sign, None, equiv, cst
  | Some s -> sign, Some (SEBwith(s, wd)), equiv, cst

let rec translate_module env mp inl me =
  match me.mod_entry_expr, me.mod_entry_type with
    | None, None ->
	Errors.anomaly ~label:"Mod_typing.translate_module"
          (Pp.str "empty type and expr in module entry")
    | None, Some mte ->
	let mtb = translate_module_type env mp inl mte in
	  { mod_mp = mp;
	    mod_expr = None;
	    mod_type = mtb.typ_expr;
	    mod_type_alg = mtb.typ_expr_alg;
	    mod_delta = mtb.typ_delta;
	    mod_constraints = mtb.typ_constraints; 
	    mod_retroknowledge = []}
   | Some mexpr, _ ->
	let sign,alg_implem,resolver,cst1 =
	  translate_struct_module_entry env mp inl mexpr in
	let sign,alg1,resolver,cst2 =
	  match me.mod_entry_type with
	    | None ->
		sign,None,resolver,Univ.empty_constraint
	    | Some mte ->
		let mtb = translate_module_type env mp inl mte in
                let cst = Subtyping.check_subtypes env
		  {typ_mp = mp;
		   typ_expr = sign;
		   typ_expr_alg = None;
		   typ_constraints = Univ.empty_constraint;
		   typ_delta = resolver;}
		  mtb
		in
		  mtb.typ_expr,mtb.typ_expr_alg,mtb.typ_delta,cst
	in
	  { mod_mp = mp;
	    mod_type = sign;
	    mod_expr = alg_implem;
	    mod_type_alg = alg1;
	    mod_constraints = cst1 +++ cst2;
	    mod_delta = resolver;
	    mod_retroknowledge = []} 
	    (* spiwack: not so sure about that. It may
	       cause a bug when closing nested modules.
	       If it does, I don't really know how to
	       fix the bug.*)

and translate_apply env inl ftrans mexpr mkalg =
  let sign,alg,resolver,cst1 = ftrans in
  let farg_id, farg_b, fbody_b = destr_functor sign in
  let mp1 =
    try path_of_mexpr mexpr
    with Not_path -> error_application_to_not_path mexpr
  in
  let mtb = module_type_of_module None (lookup_module mp1 env) in
  let cst2 = Subtyping.check_subtypes env mtb farg_b in
  let mp_delta = discr_resolver mtb in
  let mp_delta = inline_delta_resolver env inl mp1 farg_id farg_b mp_delta in
  let subst = map_mbid farg_id mp1 mp_delta in
  subst_struct_expr subst fbody_b,
  mkalg alg mp1 cst2,
  subst_codom_delta_resolver subst resolver,
  cst1 +++ cst2

and translate_functor env inl arg_id arg_e trans mkalg =
  let mtb = translate_module_type env (MPbound arg_id) inl arg_e in
  let env' = add_module (module_body_of_type (MPbound arg_id) mtb) env in
  let sign,alg,resolver,cst = trans env'
  in
  SEBfunctor (arg_id, mtb, sign),
  mkalg alg arg_id mtb,
  resolver,
  cst +++ mtb.typ_constraints

and translate_struct_module_entry env mp inl = function
  | MSEident mp1 ->
      let mb = lookup_module mp1 env in
      let mb' = strengthen_and_subst_mb mb mp false in
      mb'.mod_type, Some (SEBident mp1), mb'.mod_delta,Univ.empty_constraint
  | MSEfunctor (arg_id, arg_e, body_expr) ->
      let trans env' = translate_struct_module_entry env' mp inl body_expr in
      let mkalg a id m = Option.map (fun a -> SEBfunctor (id,m,a)) a in
      translate_functor env inl arg_id arg_e trans mkalg
  | MSEapply (fexpr,mexpr) ->
      let trans = translate_struct_module_entry env mp inl fexpr in
      let mkalg a mp c = Option.map (fun a -> SEBapply(a,SEBident mp,c)) a in
      translate_apply env inl trans mexpr mkalg
  | MSEwith(mte, with_decl) ->
      let sign,alg,resolve,cst1 =
	translate_struct_module_entry env mp inl mte in
      let sign,alg,resolve,cst2 =
	check_with env sign with_decl alg mp resolve in
      sign,alg,resolve, cst1 +++ cst2

and translate_struct_type_entry env inl = function
  | MSEident mp1 ->
      let mtb = lookup_modtype mp1 env in
      mtb.typ_expr,Some (SEBident mp1),mtb.typ_delta,Univ.empty_constraint
  | MSEfunctor (arg_id, arg_e, body_expr) ->
      let trans env' = translate_struct_type_entry env' inl body_expr in
      translate_functor env inl arg_id arg_e trans (fun _ _ _ -> None)
  | MSEapply (fexpr,mexpr) ->
      let trans = translate_struct_type_entry env inl fexpr in
      translate_apply env inl trans mexpr (fun _ _ _ -> None)
  | MSEwith(mte, with_decl) ->
      let sign,alg,resolve,cst1 = translate_struct_type_entry env inl mte in
      let sign,alg,resolve,cst2 =
	check_with env sign with_decl alg (mp_from_mexpr mte) resolve
      in
      sign,alg,resolve, cst1 +++ cst2

and translate_module_type env mp inl mte =
  let mp_from = mp_from_mexpr mte in
  let sign,alg,resolve,cst = translate_struct_type_entry env inl mte in
  let mtb = subst_modtype_and_resolver
    {typ_mp = mp_from;
     typ_expr = sign;
     typ_expr_alg = None;
     typ_constraints = cst;
     typ_delta = resolve} mp
  in {mtb with typ_expr_alg = alg}

let rec translate_struct_include_module_entry env mp inl = function
  | MSEident mp1 ->
      let mb = lookup_module mp1 env in
      let mb' = strengthen_and_subst_mb mb mp true in
      let mb_typ = clean_bounded_mod_expr mb'.mod_type in
      mb_typ,None,mb'.mod_delta,Univ.empty_constraint
  | MSEapply (fexpr,mexpr) ->
      let ftrans = translate_struct_include_module_entry env mp inl fexpr in
      translate_apply env inl ftrans mexpr (fun _ _ _ -> None)
  | _ -> Modops.error_higher_order_include ()

let rec add_struct_expr_constraints env = function
  | SEBident _ -> env

  | SEBfunctor (_,mtb,meb) ->
      add_struct_expr_constraints
	(add_modtype_constraints env mtb) meb

  | SEBstruct (structure_body) ->
      List.fold_left
        (fun env (_,item) -> add_struct_elem_constraints env item)
        env
        structure_body

  | SEBapply (meb1,meb2,cst) ->
      Environ.add_constraints cst
        (add_struct_expr_constraints
	  (add_struct_expr_constraints env meb1)
	  meb2)
  | SEBwith(meb,With_definition_body(_,cb))->
      Environ.add_constraints (Future.force cb.const_constraints)
	(add_struct_expr_constraints env meb)
  | SEBwith(meb,With_module_body(_,_))->
      add_struct_expr_constraints env meb
		
and add_struct_elem_constraints env = function 
  | SFBconst cb -> 
      Environ.add_constraints (Future.force cb.const_constraints) env
  | SFBmind mib -> Environ.add_constraints mib.mind_constraints env
  | SFBmodule mb -> add_module_constraints env mb
  | SFBmodtype mtb -> add_modtype_constraints env mtb

and add_module_constraints env mb =
  let env = match mb.mod_expr with
    | None -> env
    | Some meb -> add_struct_expr_constraints env meb
  in
  let env =
    add_struct_expr_constraints env mb.mod_type
  in
    Environ.add_constraints mb.mod_constraints env

and add_modtype_constraints env mtb =
  Environ.add_constraints mtb.typ_constraints
    (add_struct_expr_constraints env mtb.typ_expr)


let rec struct_expr_constraints cst = function
  | SEBident _ -> cst

  | SEBfunctor (_,mtb,meb) ->
      struct_expr_constraints
	(modtype_constraints cst mtb) meb

  | SEBstruct (structure_body) ->
      List.fold_left
        (fun cst (_,item) -> struct_elem_constraints cst item)
        cst
        structure_body

  | SEBapply (meb1,meb2,cst1) ->
      struct_expr_constraints (struct_expr_constraints (cst1 +++ cst) meb1)
        meb2
  | SEBwith(meb,With_definition_body(_,cb))->
      struct_expr_constraints ((Future.force cb.const_constraints) +++ cst) meb
  | SEBwith(meb,With_module_body(_,_))->
      struct_expr_constraints  cst meb

and struct_elem_constraints cst = function
  | SFBconst cb -> cst
  | SFBmind mib -> cst
  | SFBmodule mb -> module_constraints cst mb
  | SFBmodtype mtb -> modtype_constraints cst mtb

and module_constraints cst mb =
  let cst = match mb.mod_expr with
    | None -> cst
    | Some meb -> struct_expr_constraints cst meb in
  let cst = struct_expr_constraints cst mb.mod_type in
  mb.mod_constraints +++ cst

and modtype_constraints cst mtb =
  struct_expr_constraints (mtb.typ_constraints +++ cst) mtb.typ_expr


let struct_expr_constraints = struct_expr_constraints Univ.empty_constraint
let module_constraints = module_constraints Univ.empty_constraint
