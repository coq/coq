(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
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
open Univ
open Declarations
open Entries
open Environ
open Term_typing
open Modops
open Subtyping
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

let rec list_split_assoc k rev_before = function
  | [] -> raise Not_found
  | (k',b)::after when k=k' -> rev_before,b,after
  | h::tail -> list_split_assoc k (h::rev_before) tail

let discr_resolver env mtb =
     match mtb.typ_expr with
	SEBstruct _ -> 
	  mtb.typ_delta
      | _ -> (*case mp is a functor *)
	  empty_delta_resolver
	
let rec rebuild_mp mp l =
  match l with
      []-> mp
    | i::r -> rebuild_mp (MPdot(mp,i)) r 
	
let rec check_with env sign with_decl alg_sign mp equiv = 
  let sign,wd,equiv,cst= match with_decl with
    | With_Definition (id,_) ->
	let sign,cb,cst = check_with_aux_def env sign with_decl mp equiv in
	  sign,With_definition_body(id,cb),equiv,cst
    | With_Module (id,mp1) -> 
	let sign,equiv,cst = 
	  check_with_aux_mod env sign with_decl mp equiv in
	  sign,With_module_body(id,mp1),equiv,cst in
    if alg_sign = None then
      sign,None,equiv,cst
    else
      sign,Some (SEBwith(Option.get(alg_sign),wd)),equiv,cst
	    
and check_with_aux_def env sign with_decl mp equiv = 
  let sig_b = match sign with 
    | SEBstruct(sig_b) -> sig_b
    | _ -> error_signature_expected sign
  in
  let id,idl = match with_decl with
    | With_Definition (id::idl,_) | With_Module (id::idl,_) -> id,idl
    | With_Definition ([],_) | With_Module ([],_) -> assert false
  in
  let l = label_of_id id in
    try
      let rev_before,spec,after = list_split_assoc l [] sig_b in
      let before = List.rev rev_before in
      let env' = Modops.add_signature mp before equiv env in
	match with_decl with
          | With_Definition ([],_) -> assert false
	  | With_Definition ([id],c) ->
	      let cb = match spec with
		  SFBconst cb -> cb
		| _ -> error_not_a_constant l
	      in
		begin
		  match cb.const_body with
		    | None ->
			let (j,cst1) = Typeops.infer env' c in
			let typ = Typeops.type_of_constant_type env' cb.const_type in
			let cst2 = Reduction.conv_leq env' j.uj_type typ in
			let cst =
			  union_constraints
			    (union_constraints cb.const_constraints cst1)
			    cst2 in
			let body = Some (Declarations.from_val j.uj_val) in
			let cb' = {cb with
				     const_body = body;
				     const_body_code = Cemitcodes.from_val
                            (compile_constant_body env' body false);
                                     const_constraints = cst} in
			  SEBstruct(before@((l,SFBconst(cb'))::after)),cb',cst
		    | Some b ->
			let cst1 = Reduction.conv env' c (Declarations.force b) in
			let cst = union_constraints cb.const_constraints cst1 in
			let body = Some (Declarations.from_val c) in
			let cb' = {cb with
				     const_body = body;
				     const_body_code = Cemitcodes.from_val
                            (compile_constant_body env' body false);
                                     const_constraints = cst} in
			  SEBstruct(before@((l,SFBconst(cb'))::after)),cb',cst
	      end
	  | With_Definition (_::_,c) ->
	      let old = match spec with
		  SFBmodule msb -> msb
		| _ -> error_not_a_module (string_of_label l)
	      in
		begin
		  match old.mod_expr with
                    | None ->
			let new_with_decl = With_Definition (idl,c) in 
			let sign,cb,cst = 
			  check_with_aux_def env' old.mod_type new_with_decl 
			    (MPdot(mp,l)) old.mod_delta in
			let new_spec = SFBmodule({old with
						    mod_type = sign;
						    mod_type_alg = None}) in
			  SEBstruct(before@((l,new_spec)::after)),cb,cst
                    | Some msb ->
			error_a_generative_module_expected l
		end
	  | _ -> anomaly "Modtyping:incorrect use of with"
    with
	Not_found -> error_no_such_label l
      | Reduction.NotConvertible -> error_with_incorrect l

and check_with_aux_mod env sign with_decl mp equiv = 
  let sig_b = match sign with 
    | SEBstruct(sig_b) ->sig_b
    | _ -> error_signature_expected sign
  in
  let id,idl = match with_decl with
    | With_Definition (id::idl,_) | With_Module (id::idl,_) -> id,idl
    | With_Definition ([],_) | With_Module ([],_) -> assert false
  in
  let l = label_of_id id in
    try
      let rev_before,spec,after = list_split_assoc l [] sig_b in
      let before = List.rev rev_before in
      let rec mp_rec = function
	| [] -> mp
	| i::r -> MPdot(mp_rec r,label_of_id i)
      in
      let env' = Modops.add_signature mp before equiv env in
	match with_decl with
          | With_Module ([],_) -> assert false
	  | With_Module ([id], mp1) ->
	      let old = match spec with
		  SFBmodule msb -> msb
		| _ -> error_not_a_module (string_of_label l)
	      in
	      let mb_mp1 = (lookup_module mp1 env) in
	      let mtb_mp1 = 
		module_type_of_module env' None mb_mp1  in
	      let cst =
		match old.mod_expr with
		    None ->
		      begin
			try union_constraints
			  (check_subtypes env' mtb_mp1 
			     (module_type_of_module env' None old))
			  old.mod_constraints
			with Failure _ -> error_with_incorrect (label_of_id id)
		      end
		  | Some (SEBident(mp')) ->
		      check_modpath_equiv env' mp1 mp';
		      old.mod_constraints
		  | _ ->  error_a_generative_module_expected l
	      in
	      let new_mb = strengthen_and_subst_mb mb_mp1
		(MPdot(mp,l)) env false in
	      let new_spec = SFBmodule {new_mb with 
					  mod_mp = MPdot(mp,l);
					  mod_expr = Some (SEBident mp1);
					  mod_constraints = cst} in
		(* we propagate the new equality in the rest of the signature
		   with the identity substitution accompagned by the new resolver*)
	      let id_subst = map_mp (MPdot(mp,l)) (MPdot(mp,l)) new_mb.mod_delta in
		SEBstruct(before@(l,new_spec)::subst_signature id_subst after),
	      add_delta_resolver equiv new_mb.mod_delta,cst
          | With_Module (idc,mp1) -> 
	      let old = match spec with
		  SFBmodule msb -> msb
		| _ -> error_not_a_module (string_of_label l)
	      in
	      begin
		match old.mod_expr with
		    None ->
		      let new_with_decl = With_Module (idl,mp1) in
		      let sign,equiv',cst =
			check_with_aux_mod env'
			  old.mod_type new_with_decl (MPdot(mp,l)) old.mod_delta in
		      let new_equiv = add_delta_resolver equiv equiv' in
		      let new_spec = SFBmodule {old with 
						  mod_type = sign;
						  mod_type_alg = None;
						  mod_delta = equiv'}
		      in
		      let id_subst = map_mp (MPdot(mp,l)) (MPdot(mp,l)) equiv' in
			SEBstruct(before@(l,new_spec)::subst_signature id_subst after),
		      new_equiv,cst
		  | Some (SEBident(mp')) ->
		      let mpnew = rebuild_mp mp' (List.map label_of_id idl) in
			check_modpath_equiv env' mpnew mp;
			  SEBstruct(before@(l,spec)::after)
			    ,equiv,empty_constraint
		  | _ ->
		      error_a_generative_module_expected l
              end
	  | _ -> anomaly "Modtyping:incorrect use of with"
    with
	Not_found -> error_no_such_label l
      | Reduction.NotConvertible -> error_with_incorrect l

and translate_module env mp inl me =
  match me.mod_entry_expr, me.mod_entry_type with
    | None, None ->
	anomaly "Mod_typing.translate_module: empty type and expr in module entry"
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
		sign,None,resolver,empty_constraint
	    | Some mte ->
		let mtb = translate_module_type env mp inl mte in
                let cst = check_subtypes env
		  {typ_mp = mp;
		   typ_expr = sign;
		   typ_expr_alg = None;
		   typ_constraints = empty_constraint;
		   typ_delta = resolver;}
		  mtb
		in
		  mtb.typ_expr,mtb.typ_expr_alg,mtb.typ_delta,cst
	in
	  { mod_mp = mp;
	    mod_type = sign;
	    mod_expr = alg_implem;
	    mod_type_alg = alg1;
	    mod_constraints = Univ.union_constraints cst1 cst2;
	    mod_delta = resolver;
	    mod_retroknowledge = []} 
	    (* spiwack: not so sure about that. It may
	       cause a bug when closing nested modules.
	       If it does, I don't really know how to
	       fix the bug.*)

and translate_apply env inl ftrans mexpr mkalg =
  let sign,alg,resolver,cst1 = ftrans in
  let farg_id, farg_b, fbody_b = destr_functor env sign in
  let mp1 =
    try path_of_mexpr mexpr
    with Not_path -> error_application_to_not_path mexpr
  in
  let mtb = module_type_of_module env None (lookup_module mp1 env) in
  let cst2 = check_subtypes env mtb farg_b in
  let mp_delta = discr_resolver env mtb in
  let mp_delta = inline_delta_resolver env inl mp1 farg_id farg_b mp_delta in
  let subst = map_mbid farg_id mp1 mp_delta
  in
  subst_struct_expr subst fbody_b,
  mkalg alg mp1 cst2,
  subst_codom_delta_resolver subst resolver,
  Univ.union_constraints cst1 cst2

and translate_functor env inl arg_id arg_e trans mkalg =
  let mtb = translate_module_type env (MPbound arg_id) inl arg_e in
  let env' = add_module (module_body_of_type (MPbound arg_id) mtb) env in
  let sign,alg,resolver,cst = trans env'
  in
  SEBfunctor (arg_id, mtb, sign),
  mkalg alg arg_id mtb,
  resolver,
  Univ.union_constraints cst mtb.typ_constraints

and translate_struct_module_entry env mp inl = function
  | MSEident mp1 ->
      let mb = lookup_module mp1 env in
      let mb' = strengthen_and_subst_mb mb mp env false in
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
      sign,alg,resolve,Univ.union_constraints cst1 cst2

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
      sign,alg,resolve,Univ.union_constraints cst1 cst2

and translate_module_type env mp inl mte =
  let mp_from = mp_from_mexpr mte in
  let sign,alg,resolve,cst = translate_struct_type_entry env inl mte in
  let mtb = subst_modtype_and_resolver
    {typ_mp = mp_from;
     typ_expr = sign;
     typ_expr_alg = None;
     typ_constraints = cst;
     typ_delta = resolve} mp env
  in {mtb with typ_expr_alg = alg}

let rec translate_struct_include_module_entry env mp inl = function
  | MSEident mp1 ->
      let mb = lookup_module mp1 env in
      let mb' = strengthen_and_subst_mb mb mp env true in
      let mb_typ = clean_bounded_mod_expr mb'.mod_type in
      mb_typ,None,mb'.mod_delta,Univ.empty_constraint
  | MSEapply (fexpr,mexpr) ->
      let ftrans = translate_struct_include_module_entry env mp inl fexpr in
      translate_apply env inl ftrans mexpr (fun _ _ _ -> None)
  | _ -> error ("You cannot Include a high-order structure.")

let rec add_struct_expr_constraints env = function
  | SEBident _ -> env

  | SEBfunctor (_,mtb,meb) ->
      add_struct_expr_constraints
	(add_modtype_constraints env mtb) meb

  | SEBstruct (structure_body) ->
      List.fold_left
        (fun env (l,item) -> add_struct_elem_constraints env item)
        env
        structure_body

  | SEBapply (meb1,meb2,cst) ->
      Environ.add_constraints cst
        (add_struct_expr_constraints
	  (add_struct_expr_constraints env meb1)
	  meb2)
  | SEBwith(meb,With_definition_body(_,cb))->
      Environ.add_constraints cb.const_constraints
	(add_struct_expr_constraints env meb)
  | SEBwith(meb,With_module_body(_,_))->
      add_struct_expr_constraints env meb
		
and add_struct_elem_constraints env = function 
  | SFBconst cb -> Environ.add_constraints cb.const_constraints env
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
        (fun cst (l,item) -> struct_elem_constraints cst item)
        cst
        structure_body

  | SEBapply (meb1,meb2,cst1) ->
      struct_expr_constraints
	(struct_expr_constraints (Univ.union_constraints cst1 cst) meb1)
	meb2
  | SEBwith(meb,With_definition_body(_,cb))->
      struct_expr_constraints
        (Univ.union_constraints cb.const_constraints cst) meb
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
  let cst = 
      struct_expr_constraints cst mb.mod_type in
  Univ.union_constraints mb.mod_constraints cst

and modtype_constraints cst mtb =
  struct_expr_constraints  (Univ.union_constraints mtb.typ_constraints cst) mtb.typ_expr


let struct_expr_constraints = struct_expr_constraints Univ.empty_constraint
let module_constraints = module_constraints Univ.empty_constraint
