(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
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

let rec list_split_assoc k rev_before = function
  | [] -> raise Not_found
  | (k',b)::after when k=k' -> rev_before,b,after
  | h::tail -> list_split_assoc k (h::rev_before) tail

let rec list_fold_map2 f e = function
  |  []  -> (e,[],[])
  |  h::t ->
       let e',h1',h2' = f e h in
       let e'',t1',t2' = list_fold_map2 f e' t in
	 e'',h1'::t1',h2'::t2'

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
	  let cb = 
	    match spec with
	    | SFBconst cb -> cb
	    | _ -> error_not_a_constant l in
	  begin match cb.const_body with
	  | Def b ->
	      let cst1 = Reduction.conv env' c (Declarations.force b) in
	      let cst = Constraint.union cb.const_constraints cst1 in
	      let body = Def (Declarations.from_val c) in
	      let cb' = {cb with
			 const_body = body;
			 const_body_code = Cemitcodes.from_val 
			   (compile_constant_body env' body false);
                         const_constraints = cst} in
	      SEBstruct(before@((l,SFBconst(cb'))::after)),cb',cst
	  | Opaque (Some b) -> assert false
(*
	      let cst1 = Reduction.conv env' c (Declarations.force b) in
	      let cst = Constraint.union cb.const_constraints cst1 in
	      let body = Opaque (Some (Declarations.from_val c)) in
	      let cb' = {cb with
			 const_body = body;
			 const_body_code = Cemitcodes.from_val 
			   (compile_constant_body env' body false);
                         const_constraints = cst} in
	      SEBstruct(before@((l,SFBconst(cb'))::after)),cb',cst *)
	  | Opaque None ->
	      let (j,cst1) = Typeops.infer env' c in
	      let typ = Typeops.type_of_constant_type env' cb.const_type in
	      let cst2 = Reduction.conv_leq env' j.uj_type typ in
	      let cst =
		Constraint.union
		  (Constraint.union cb.const_constraints cst1)
		  cst2 in
	      let body = Def (Declarations.from_val j.uj_val) in
	      let cb' = {cb with
			 const_body = body;
			 const_body_code = Cemitcodes.from_val
                           (compile_constant_body env' body false);
                         const_constraints = cst} in
	      SEBstruct(before@((l,SFBconst(cb'))::after)),cb',cst
	  | Primitive _ -> assert false
	  end
      | With_Definition (_::_,c) ->
	  let old = 
	    match spec with
	    | SFBmodule msb -> msb
	    | _ -> error_not_a_module (string_of_label l)
	  in
	  begin match old.mod_expr with
          | None ->
	      let new_with_decl = With_Definition (idl,c) in 
	      let sign,cb,cst = 
		check_with_aux_def env' old.mod_type new_with_decl 
		  (MPdot(mp,l)) old.mod_delta in
	      let new_spec = SFBmodule({old with
					mod_type = sign;
					mod_type_alg = None}) in
	      SEBstruct(before@((l,new_spec)::after)),cb,cst
          | Some msb -> error_a_generative_module_expected l
	  end
      | _ -> anomaly "Modtyping:incorrect use of with"
    with
      Not_found -> error_no_such_label l
    | Reduction.NotConvertible -> Printf.printf "ICI\n\n";error_with_incorrect l

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
			try Constraint.union
			  (check_subtypes env' mtb_mp1 
			     (module_type_of_module env' None old))
			  old.mod_constraints
			with Failure _ -> Printf.printf "ICI1\n\n";error_with_incorrect (label_of_id id)
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
			    ,equiv,Constraint.empty
		  | _ ->
		      error_a_generative_module_expected l
              end
	  | _ -> anomaly "Modtyping:incorrect use of with"
    with
	Not_found -> error_no_such_label l
      | Reduction.NotConvertible ->Printf.printf "ICI2\n\n"; error_with_incorrect l

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
	    mod_retroknowledge = []
	  }
   | Some mexpr, _ ->
	let sign,alg_implem,resolver,cst1 =
	  translate_struct_module_entry env mp inl mexpr in
	let sign,alg1,resolver,cst2 =
	  match me.mod_entry_type with
	    | None ->
		sign,None,resolver,Constraint.empty
	    | Some mte ->
		let mtb = translate_module_type env mp inl mte in
                let cst = check_subtypes env
		  {typ_mp = mp;
		   typ_expr = sign;
		   typ_expr_alg = None;
		   typ_constraints = Constraint.empty;
		   typ_delta = resolver;}
		  mtb
		in
		  mtb.typ_expr,mtb.typ_expr_alg,mtb.typ_delta,cst
	in
	  { mod_mp = mp;
	    mod_type = sign;
	    mod_expr = Some alg_implem;
	    mod_type_alg = alg1;
	    mod_constraints = Univ.Constraint.union cst1 cst2;
	    mod_delta = resolver;
	    mod_retroknowledge = []
	  }


and translate_struct_module_entry env mp inl mse  = match mse with
  | MSEident mp1 ->
      let mb = lookup_module mp1 env in 
      let mb' = strengthen_and_subst_mb mb mp env false in
	mb'.mod_type, SEBident mp1, mb'.mod_delta,Univ.Constraint.empty
  | MSEfunctor (arg_id, arg_e, body_expr) ->
      let mtb = translate_module_type env (MPbound arg_id) inl arg_e in
      let env' = add_module (module_body_of_type (MPbound arg_id) mtb) 
	env in
      let sign,alg,resolver,cst =
	translate_struct_module_entry env' mp inl body_expr in
      SEBfunctor (arg_id, mtb, sign),SEBfunctor (arg_id, mtb, alg),resolver,
      Univ.Constraint.union cst mtb.typ_constraints
  | MSEapply (fexpr,mexpr) ->
      let sign,alg,resolver,cst1 =
	translate_struct_module_entry env mp inl fexpr
      in
      let farg_id, farg_b, fbody_b = destr_functor env sign in
      let mtb,mp1 = 
	try
	  let mp1 = path_of_mexpr mexpr in
	      let mtb = module_type_of_module env None (lookup_module mp1 env) in
		mtb,mp1
	with
	  | Not_path -> error_application_to_not_path mexpr
	      (* place for nondep_supertype *) in
      let cst = check_subtypes env mtb farg_b in
      let mp_delta = discr_resolver env mtb in
      let mp_delta = if not inl then mp_delta else
	complete_inline_delta_resolver env mp1 farg_id farg_b mp_delta
      in
      let subst = map_mbid farg_id mp1 mp_delta in
	(subst_struct_expr subst fbody_b),SEBapply(alg,SEBident mp1,cst),
      (subst_codom_delta_resolver subst resolver),
      Univ.Constraint.union cst1 cst
  | MSEwith(mte, with_decl) ->
      let sign,alg,resolve,cst1 = translate_struct_module_entry env mp inl mte in
      let sign,alg,resolve,cst2 = check_with env sign with_decl (Some alg) mp resolve in
	sign,Option.get alg,resolve,Univ.Constraint.union cst1 cst2
	  
and translate_struct_type_entry env inl mse = match mse with
  | MSEident mp1 ->
      let mtb = lookup_modtype mp1 env in 
	mtb.typ_expr,
      Some (SEBident mp1),mtb.typ_delta,mp1,Univ.Constraint.empty
  | MSEfunctor (arg_id, arg_e, body_expr) ->
      let mtb = translate_module_type env (MPbound arg_id) inl arg_e in
      let env' = add_module (module_body_of_type (MPbound arg_id) mtb) env  in
      let sign,alg,resolve,mp_from,cst =
	translate_struct_type_entry env' inl body_expr in
	SEBfunctor (arg_id, mtb, sign),None,resolve,mp_from,
      Univ.Constraint.union cst mtb.typ_constraints
  | MSEapply (fexpr,mexpr) ->
      let sign,alg,resolve,mp_from,cst1 =
	translate_struct_type_entry env inl fexpr
      in
      let farg_id, farg_b, fbody_b = destr_functor env sign in
      let mtb,mp1 = 
	try
	  let mp1 = path_of_mexpr mexpr in
	  let mtb = module_type_of_module env None (lookup_module mp1 env) in
	    mtb,mp1
	with
	  | Not_path -> error_application_to_not_path mexpr
	      (* place for nondep_supertype *) in
      let cst2 = check_subtypes env mtb farg_b in
      let mp_delta = discr_resolver env mtb in
      let mp_delta = if not inl then mp_delta else
	complete_inline_delta_resolver env mp1 farg_id farg_b mp_delta
      in
      let subst = map_mbid farg_id mp1 mp_delta in
	(subst_struct_expr subst fbody_b),None,
      (subst_codom_delta_resolver subst resolve),mp_from,Univ.Constraint.union cst1 cst2
  | MSEwith(mte, with_decl) ->
      let sign,alg,resolve,mp_from,cst = translate_struct_type_entry env inl mte in
      let sign,alg,resolve,cst1 = 
	check_with env sign with_decl alg mp_from resolve in
	sign,alg,resolve,mp_from,Univ.Constraint.union cst cst1    

and translate_module_type env mp inl mte =
	let sign,alg,resolve,mp_from,cst = translate_struct_type_entry env inl mte in
	 subst_modtype_and_resolver 
	   {typ_mp = mp_from;
	    typ_expr = sign;
	    typ_expr_alg = alg;
	    typ_constraints = cst;
	    typ_delta = resolve} mp env
	   
let rec translate_struct_include_module_entry env mp inl mse  = match mse with
  | MSEident mp1 ->
      let mb = lookup_module mp1 env in 
      let mb' = strengthen_and_subst_mb mb mp env true in
      let mb_typ = clean_bounded_mod_expr mb'.mod_type in 
	mb_typ, mb'.mod_delta,Univ.Constraint.empty
  | MSEapply (fexpr,mexpr) ->
      let sign,resolver,cst1 =
	translate_struct_include_module_entry env mp inl fexpr in
      let farg_id, farg_b, fbody_b = destr_functor env sign in
      let mtb,mp1 = 
	try
	  let mp1 = path_of_mexpr mexpr in
	      let mtb = module_type_of_module env None (lookup_module mp1 env) in
		mtb,mp1
	with
	  | Not_path -> error_application_to_not_path mexpr
	      (* place for nondep_supertype *) in
      let cst = check_subtypes env mtb farg_b in
      let mp_delta =  discr_resolver env mtb in
      let mp_delta = if not inl then mp_delta else
	complete_inline_delta_resolver env mp1 farg_id farg_b mp_delta
      in
      let subst = map_mbid farg_id mp1 mp_delta in
	(subst_struct_expr subst fbody_b),
      (subst_codom_delta_resolver subst resolver),
      Univ.Constraint.union cst1 cst
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
	(struct_expr_constraints (Univ.Constraint.union cst1 cst) meb1)
	meb2
  | SEBwith(meb,With_definition_body(_,cb))->
      struct_expr_constraints
        (Univ.Constraint.union cb.const_constraints cst) meb
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
  Univ.Constraint.union mb.mod_constraints cst

and modtype_constraints cst mtb =
  struct_expr_constraints  (Univ.Constraint.union mtb.typ_constraints cst) mtb.typ_expr


let struct_expr_constraints = struct_expr_constraints Univ.Constraint.empty
let module_constraints = module_constraints Univ.Constraint.empty
