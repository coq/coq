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
  | MSEident mb -> mb
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
	  SEBwith(mtb,With_definition_body(id,cb))
    | With_Module (id,mp) -> 
	let cst = check_with_aux_mod env mtb with_decl in
	  SEBwith(mtb,With_module_body(id,mp,cst))

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
		  match old.mod_equiv with
                    | None ->
			let new_with_decl = match with_decl with
			    With_Definition (_,c) -> With_Definition (idl,c)
			  | With_Module (_,c) -> With_Module (idl,c) in 
			  check_with_aux_def env' (type_of_mb env old) new_with_decl
                    | Some mp ->
			error_a_generative_module_expected l
		end
	  | _ -> anomaly "Modtyping:incorrect use of with"
    with
	Not_found -> error_no_such_label l
      | Reduction.NotConvertible -> error_with_incorrect l

and check_with_aux_mod env mtb with_decl = 
  let msid,sig_b = match (eval_struct env mtb) with 
    | SEBstruct(msid,sig_b) ->let msid'=(refresh_msid msid) in
	msid',(subst_signature_msid msid (MPself(msid')) sig_b)
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
          | With_Module ([],_) -> assert false
	  | With_Module ([id], mp) ->
	      let old = match spec with
		  SFBmodule msb -> msb
		| _ -> error_not_a_module (string_of_label l)
	      in
	      let mtb' = eval_struct env' (SEBident mp) in
	      let cst =
		try check_subtypes env' mtb' (type_of_mb env old)
              with Failure _ -> error_with_incorrect (label_of_id id) in
	      let _ = 
 		match old.mod_equiv with
		| None -> Some mp
		| Some mp' -> 
		    check_modpath_equiv env' mp mp';
		    Some mp
	      in
		cst
        | With_Module (_::_,_) -> 
	    let old = match spec with
		SFBmodule msb -> msb
	      | _ -> error_not_a_module (string_of_label l)
	    in
	      begin
		match old.mod_equiv with
                    None ->
                      let new_with_decl = match with_decl with
			  With_Definition (_,c) -> With_Definition (idl,c)
			| With_Module (_,c) -> With_Module (idl,c) in
			check_with_aux_mod env' (type_of_mb env old) new_with_decl 
                  | Some mp ->
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
	let mtb = translate_struct_entry env mte in
	{ mod_expr = None;
	  mod_type = Some mtb;
	  mod_equiv = None;
	  mod_constraints = Constraint.empty; 
	  mod_retroknowledge = []}
    | Some mexpr, _ -> 
	let meq_o = 
	  try       (* TODO: transparent field in module_entry *)
	    match me.mod_entry_type with
	      | None -> Some (path_of_mexpr mexpr)
	      | Some _ -> None
	  with 
	    | Not_path -> None
	in
	let meb = translate_struct_entry env mexpr in
	let mod_typ, cst =
	  match me.mod_entry_type with
	    | None ->  None, Constraint.empty
	    | Some mte -> 
		let mtb1 = translate_struct_entry env mte in
                let cst = check_subtypes env (eval_struct env meb)
		  mtb1 in
		  Some mtb1, cst
	in
	  { mod_type = mod_typ;
	    mod_expr = Some meb;
	    mod_equiv = meq_o;
	    mod_constraints = cst;
	    mod_retroknowledge = []} (* spiwack: not so sure about that. It may
					cause a bug when closing nested modules.
					If it does, I don't really know how to
					fix the bug.*)


and translate_struct_entry env mse = match mse with
  | MSEident mp -> 
      SEBident mp
  | MSEfunctor (arg_id, arg_e, body_expr) ->
      let arg_b = translate_struct_entry env arg_e in
      let env' = add_module (MPbound arg_id) (module_body_of_type arg_b) env in
      let body_b = translate_struct_entry env' body_expr in
	SEBfunctor (arg_id, arg_b, body_b)
  | MSEapply (fexpr,mexpr) ->
      let feb = translate_struct_entry env fexpr in
      let feb'= eval_struct env feb
      in
      let farg_id, farg_b, fbody_b = destr_functor env feb' in
      let _ = 
	try
	  path_of_mexpr mexpr 
	with
	  | Not_path -> error_application_to_not_path mexpr
	      (* place for nondep_supertype *) in
      let meb= translate_struct_entry env mexpr in
      let cst = check_subtypes env (eval_struct env meb) farg_b in
	SEBapply(feb,meb,cst)
  | MSEwith(mte, with_decl) ->
	let mtb = translate_struct_entry env mte in
	let mtb' = check_with env mtb with_decl in
	  mtb'


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
  | SFBmodtype mtb -> add_modtype_constraints env mtb

and add_module_constraints env mb = 
  let env = match mb.mod_expr with
    | None -> env
    | Some meb -> add_struct_expr_constraints env meb
  in
  let env = match mb.mod_type with
    | None -> env
    | Some mtb -> 
	add_modtype_constraints env mtb
  in
    Environ.add_constraints mb.mod_constraints env

and add_modtype_constraints env mtb = 
  add_struct_expr_constraints env mtb
      
