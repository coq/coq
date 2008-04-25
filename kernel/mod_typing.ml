(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

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

let rec check_with env mtb with_decl = 
  match with_decl with
    | With_Definition (id,_) -> 
	let cb = check_with_aux_def env mtb with_decl in
	  SEBwith(mtb,With_definition_body(id,cb)),empty_subst
    | With_Module (id,mp) -> 
	let cst,sub = check_with_aux_mod env mtb with_decl true in
	  SEBwith(mtb,With_module_body(id,mp,cst)),sub

and check_with_aux_def env mtb with_decl = 
  let msid,sig_b = match (eval_struct env mtb) with 
    | SEBstruct(msid,sig_b) ->
	msid,sig_b
    | _ -> error_signature_expected mtb
  in
  let id,idl = match with_decl with 
    | With_Definition (id::idl,_) | With_Module (id::idl,_) -> id,idl
    | With_Definition ([],_) | With_Module ([],_) -> assert false
  in
  let l = label_of_id id in
    try
      let rev_before,spec,after = list_split_assoc l [] sig_b in
      let before = List.rev rev_before in
      let env' = Modops.add_signature (MPself msid) before env in
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
			  Constraint.union 
			    (Constraint.union cb.const_constraints cst1)
			    cst2 in
			let body = Some (Declarations.from_val j.uj_val) in
			let cb' = {cb with 
				     const_body = body;
				     const_body_code = Cemitcodes.from_val
                            (compile_constant_body env' body false false);
                                     const_constraints = cst} in
			  cb'
		    | Some b -> 
			let cst1 = Reduction.conv env' c (Declarations.force b) in
			let cst = Constraint.union cb.const_constraints cst1 in
			let body = Some (Declarations.from_val c) in
			let cb' = {cb with 
				     const_body = body;
				     const_body_code = Cemitcodes.from_val
                            (compile_constant_body env' body false false);
                                     const_constraints = cst} in
			  cb'
	      end
	  | With_Definition (_::_,_) ->
	      let old = match spec with
		  SFBmodule msb -> msb
		| _ -> error_not_a_module (string_of_label l)
	      in
		begin
		  match old.mod_expr with
                    | None ->
			let new_with_decl = match with_decl with
			    With_Definition (_,c) -> With_Definition (idl,c)
			  | With_Module (_,c) -> With_Module (idl,c) in 
			  check_with_aux_def env' (type_of_mb env old) new_with_decl
                    | Some msb ->
			error_a_generative_module_expected l
		end
	  | _ -> anomaly "Modtyping:incorrect use of with"
    with
	Not_found -> error_no_such_label l
      | Reduction.NotConvertible -> error_with_incorrect l

and check_with_aux_mod env mtb with_decl now = 
  let initmsid,msid,sig_b = match (eval_struct env mtb) with 
    | SEBstruct(msid,sig_b) ->let msid'=(refresh_msid msid) in
	msid,msid',(subst_signature_msid msid (MPself(msid')) sig_b)
    | _ -> error_signature_expected mtb
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
	| [] -> MPself initmsid
	| i::r -> MPdot(mp_rec r,label_of_id i)
      in 
      let env' = Modops.add_signature (MPself msid) before env in
	match with_decl with
          | With_Module ([],_) -> assert false
	  | With_Module ([id], mp) ->
	      let old,alias = match spec with
		  SFBmodule msb -> Some msb,None
		| SFBalias (mp',cst) -> None,Some (mp',cst)
		| _ -> error_not_a_module (string_of_label l)
	      in
	      let mtb' = lookup_modtype mp env' in
	      let cst =
		match old,alias with
		    Some msb,None ->
		      begin
			try Constraint.union 
			  (check_subtypes env' mtb' (module_type_of_module None msb))
			  msb.mod_constraints
			with Failure _ -> error_with_incorrect (label_of_id id)
		      end
		  | None,Some (mp',None) ->
		      check_modpath_equiv env' mp mp';
		      Constraint.empty
		  | None,Some (mp',Some cst) ->
		      check_modpath_equiv env' mp mp';
		      cst
		  | _,_ ->
		      anomaly "Mod_typing:no implementation and no alias"
	      in
		if now then 
		  let mp' = scrape_alias mp env' in
		  let up_subst = update_subst_alias mtb'.typ_alias (map_mp (mp_rec [id]) mp') in
		    cst, (join (map_mp (mp_rec [id]) mp') up_subst)
		else
		cst,empty_subst
        | With_Module (_::_,mp) -> 
	    let old = match spec with
		SFBmodule msb -> msb
	      | _ -> error_not_a_module (string_of_label l)
	    in
	      begin
		match old.mod_expr with
                    None ->
                      let new_with_decl = match with_decl with
			  With_Definition (_,c) -> 
			    With_Definition (idl,c)
			| With_Module (_,c) -> With_Module (idl,c) in
		      let cst,_ =
			check_with_aux_mod env' 
			  (type_of_mb env old) new_with_decl false in
			if now then 
			  let mtb' = lookup_modtype mp env' in
			  let mp' = scrape_alias mp env' in
			  let up_subst = update_subst_alias 
			    mtb'.typ_alias (map_mp (mp_rec (List.rev (id::idl))) mp') in
			    cst, (join (map_mp (mp_rec (List.rev (id::idl))) mp') up_subst)
		else
		cst,empty_subst
		  | Some msb ->
                      error_a_generative_module_expected l
              end
	| _ -> anomaly "Modtyping:incorrect use of with"
    with
	Not_found -> error_no_such_label l
      | Reduction.NotConvertible -> error_with_incorrect l
	  
and translate_module env me =
  match me.mod_entry_expr, me.mod_entry_type with
    | None, None -> 
	anomaly "Mod_typing.translate_module: empty type and expr in module entry"
    | None, Some mte -> 
	let mtb,sub = translate_struct_entry env mte in
	{ mod_expr = None;
	  mod_type = Some mtb;
	  mod_alias = sub;
	  mod_constraints = Constraint.empty; 
	  mod_retroknowledge = []}
    | Some mexpr, _ -> 
	let meb,sub1 = translate_struct_entry env mexpr in
	let mod_typ,sub,cst =
	  match me.mod_entry_type with
	    | None ->  None,sub1,Constraint.empty
	    | Some mte -> 
		let mtb2,sub2 = translate_struct_entry env mte in
                let cst = check_subtypes env
		  {typ_expr = meb;
		   typ_strength = None;
		   typ_alias = sub1;}
		  {typ_expr = mtb2;
		   typ_strength = None;
		   typ_alias = sub2;}
		in
		  Some mtb2,sub2,cst
	in
	  { mod_type = mod_typ;
	    mod_expr = Some meb;
	    mod_constraints = cst;
	    mod_alias = sub;
	    mod_retroknowledge = []} (* spiwack: not so sure about that. It may
					cause a bug when closing nested modules.
					If it does, I don't really know how to
					fix the bug.*)


and translate_struct_entry env mse = match mse with
  | MSEident mp ->
      let mtb = lookup_modtype mp env in 
      SEBident mp,mtb.typ_alias
  | MSEfunctor (arg_id, arg_e, body_expr) ->
      let arg_b,sub = translate_struct_entry env arg_e in
      let mtb =
	{typ_expr = arg_b;
	 typ_strength = None;
	 typ_alias = sub} in
      let env' = add_module (MPbound arg_id) (module_body_of_type mtb) env in
      let body_b,sub = translate_struct_entry env' body_expr in
	SEBfunctor (arg_id, mtb, body_b),sub
  | MSEapply (fexpr,mexpr) ->
      let feb,sub1 = translate_struct_entry env fexpr in
      let feb'= eval_struct env feb
      in
      let farg_id, farg_b, fbody_b = destr_functor env feb' in
      let mtb,mp = 
	try
	  let mp = scrape_alias (path_of_mexpr mexpr) env in
	  lookup_modtype mp env,mp
	with
	  | Not_path -> error_application_to_not_path mexpr
	      (* place for nondep_supertype *) in
      let meb,sub2= translate_struct_entry env (MSEident mp) in
	if sub1 = empty_subst then 
	  let cst = check_subtypes env mtb farg_b in
	    SEBapply(feb,meb,cst),sub1
	else
	  let sub2 = match eval_struct env (SEBident mp) with
	    | SEBstruct (msid,sign) -> 
		join_alias 
		  (subst_key (map_msid msid mp) sub2)
		  (map_msid msid mp)
	    | _ -> sub2 in
	  let sub3 = join_alias sub1 (map_mbid farg_id mp None) in
	  let sub4 = update_subst sub2 sub3 in
	  let cst = check_subtypes env mtb farg_b in
	    SEBapply(feb,meb,cst),(join sub3 sub4)
  | MSEwith(mte, with_decl) ->
	let mtb,sub1 = translate_struct_entry env mte in
	let mtb',sub2 = check_with env mtb with_decl in
	  mtb',join sub1 sub2
	    

let rec add_struct_expr_constraints env = function
  | SEBident _ -> env

  | SEBfunctor (_,mtb,meb) -> 
      add_struct_expr_constraints 
	(add_modtype_constraints env mtb) meb

  | SEBstruct (_,structure_body) ->
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
  | SEBwith(meb,With_module_body(_,_,cst))->
      Environ.add_constraints cst
	(add_struct_expr_constraints env meb)	
		
and add_struct_elem_constraints env = function 
  | SFBconst cb -> Environ.add_constraints cb.const_constraints env
  | SFBmind mib -> Environ.add_constraints mib.mind_constraints env
  | SFBmodule mb -> add_module_constraints env mb
  | SFBalias (mp,Some cst) -> Environ.add_constraints cst env
  | SFBalias (mp,None) -> env
  | SFBmodtype mtb -> add_modtype_constraints env mtb

and add_module_constraints env mb = 
  let env = match mb.mod_expr with
    | None -> env
    | Some meb -> add_struct_expr_constraints env meb
  in
  let env = match mb.mod_type with
    | None -> env
    | Some mtb -> 
	add_struct_expr_constraints env mtb
  in
    Environ.add_constraints mb.mod_constraints env

and add_modtype_constraints env mtb = 
  add_struct_expr_constraints env mtb.typ_expr
      

let rec struct_expr_constraints cst = function
  | SEBident _ -> cst

  | SEBfunctor (_,mtb,meb) -> 
      struct_expr_constraints 
	(modtype_constraints cst mtb) meb

  | SEBstruct (_,structure_body) ->
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
  | SEBwith(meb,With_module_body(_,_,cst1))->
      struct_expr_constraints (Univ.Constraint.union cst1 cst) meb	
		
and struct_elem_constraints cst = function 
  | SFBconst cb -> cst
  | SFBmind mib -> cst
  | SFBmodule mb -> module_constraints cst mb
  | SFBalias (mp,Some cst1) -> Univ.Constraint.union cst1 cst
  | SFBalias (mp,None) -> cst
  | SFBmodtype mtb -> modtype_constraints cst mtb

and module_constraints cst mb = 
  let cst = match mb.mod_expr with
    | None -> cst
    | Some meb -> struct_expr_constraints cst meb in
  let cst = match mb.mod_type with
    | None -> cst
    | Some mtb -> struct_expr_constraints cst mtb in
  Univ.Constraint.union mb.mod_constraints cst

and modtype_constraints cst mtb = 
  struct_expr_constraints cst mtb.typ_expr
      

let struct_expr_constraints = struct_expr_constraints Univ.Constraint.empty
