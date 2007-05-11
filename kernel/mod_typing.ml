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
  | MEident mb -> mb
  | _ -> raise Not_path

let rec replace_first p k = function 
  | [] -> [] 
  | h::t when p h -> k::t
  | h::t -> h::(replace_first p k t)

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

let type_modpath env mp = 
  strengthen env (lookup_module mp env).mod_type mp

let rec translate_modtype env mte =
  match mte with
    | MTEident ln -> MTBident ln
    | MTEfunsig (arg_id,arg_e,body_e) -> 
	let arg_b = translate_modtype env arg_e in
	let env' = 
	  add_module (MPbound arg_id) (module_body_of_type arg_b) env in
	let body_b = translate_modtype env' body_e in
	  MTBfunsig (arg_id,arg_b,body_b)
    | MTEwith (mte, with_decl) ->
	let mtb = translate_modtype env mte in
	  merge_with env mtb with_decl

and merge_with env mtb with_decl = 
  let msid,sig_b = match (Modops.scrape_modtype env mtb) with 
    | MTBsig(msid,sig_b) -> let msid'=(refresh_msid msid) in
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
      let new_spec = match with_decl with
        | With_Definition ([],_)
        | With_Module ([],_) -> assert false
	| With_Definition ([id],c) -> 
	    let cb = match spec with
		SPBconst cb -> cb
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
			SPBconst {cb with 
				    const_body = body;
			            const_body_code = Cemitcodes.from_val
                        (compile_constant_body env' body false false);
                                    const_constraints = cst}
		  | Some b -> 
		      let cst1 = Reduction.conv env' c (Declarations.force b) in
		      let cst = Constraint.union cb.const_constraints cst1 in
                      let body = Some (Declarations.from_val c) in
			SPBconst {cb with 
				    const_body = body;
				    const_body_code = Cemitcodes.from_val
                        (compile_constant_body env' body false false);
                                    const_constraints = cst}
	      end	
(* and what about msid's ????? Don't they clash ? *)
	| With_Module ([id], mp) ->
	    let old = match spec with
		SPBmodule msb -> msb
	      | _ -> error_not_a_module (string_of_label l)
	    in
	    let mtb = type_modpath env' mp in
	    let cst =
              try check_subtypes env' mtb old.msb_modtype
              with Failure _ -> error_with_incorrect (label_of_id id) in
	    let equiv = 
 	      match old.msb_equiv with
		| None -> Some mp
		| Some mp' -> 
		    check_modpath_equiv env' mp mp';
		    Some mp
	    in
	    let msb =
	      {msb_modtype = mtb; 
	       msb_equiv = equiv; 
	       msb_constraints = Constraint.union old.msb_constraints cst }
	    in
	      SPBmodule msb
	| With_Definition (_::_,_)
        | With_Module (_::_,_) -> 
	    let old = match spec with
		SPBmodule msb -> msb
	      | _ -> error_not_a_module (string_of_label l)
	    in
	      begin
		match old.msb_equiv with
                   None ->
                    let new_with_decl = match with_decl with
                       With_Definition (_,c) -> With_Definition (idl,c)
                     | With_Module (_,c) -> With_Module (idl,c) in
                    let modtype = 
                     merge_with env' old.msb_modtype new_with_decl in
                    let msb =
	              {msb_modtype = modtype; 
	               msb_equiv = None; 
	               msb_constraints = old.msb_constraints }
	            in
	             SPBmodule msb
                 | Some mp ->
                    error_a_generative_module_expected l
              end
      in
	MTBsig(msid,  before@(l,new_spec)::after)
    with
	Not_found -> error_no_such_label l
      | Reduction.NotConvertible -> error_with_incorrect l


and translate_module env  me =
  match me.mod_entry_expr, me.mod_entry_type with
    | None, None -> 
	anomaly "Mod_typing.translate_module: empty type and expr in module entry"
    | None, Some mte -> 
	let mtb = translate_modtype env mte in
	{ mod_expr = None;
	  mod_user_type = Some mtb;
	  mod_type = mtb;
	  mod_equiv = None;
	  mod_constraints = Constraint.empty;
	  mod_retroknowledge = [] } 
    | Some mexpr, _ -> 
	let meq_o = (* do we have a transparent module ? *)
	  try       (* TODO: transparent field in module_entry *)
	    match me.mod_entry_type with
	      | None -> Some (path_of_mexpr mexpr)
	      | Some _ -> None
	  with 
	    | Not_path -> None
	in
	let meb,mtb1 = translate_mexpr env mexpr in
	let mtb, mod_user_type, cst =
	  match me.mod_entry_type with
	    | None -> mtb1, None, Constraint.empty
	    | Some mte -> 
		let mtb2 = translate_modtype env mte in
                let cst = check_subtypes env mtb1 mtb2 in
		mtb2, Some mtb2, cst
	in
	  { mod_type = mtb;
	    mod_user_type = mod_user_type;
	    mod_expr = Some meb;
	    mod_equiv = meq_o;
	    mod_constraints = cst;
	    mod_retroknowledge = []} (* spiwack: not so sure about that. It may
					cause a bug when closing nested modules.
					If it does, I don't really know how to
					fix the bug.*)

(* translate_mexpr : env -> module_expr -> module_expr_body * module_type_body *)
and translate_mexpr env mexpr = match mexpr with
  | MEident mp -> 
      MEBident mp,
      type_modpath env mp
  | MEfunctor (arg_id, arg_e, body_expr) ->
      let arg_b = translate_modtype env arg_e in
      let env' = add_module (MPbound arg_id) (module_body_of_type arg_b) env in
      let (body_b,body_tb) = translate_mexpr env' body_expr in
	MEBfunctor (arg_id, arg_b, body_b), 
	MTBfunsig (arg_id, arg_b, body_tb)
  | MEapply (fexpr,mexpr) ->
      let feb,ftb = translate_mexpr env fexpr in
      let ftb = scrape_modtype env ftb in
      let farg_id, farg_b, fbody_b = destr_functor ftb in
      let meb,mtb = translate_mexpr env mexpr in
      let cst = check_subtypes env mtb farg_b in
      let mp = 
	try
	  path_of_mexpr mexpr 
	with
	  | Not_path -> error_application_to_not_path mexpr
	      (* place for nondep_supertype *)
      in
       let resolve = Modops.resolver_of_environment farg_id farg_b mp env in
	MEBapply(feb,meb,cst),
        (* This is the place where the functor formal parameter is
           substituted by the given argument to compute the type of the
           functor application. *)
	subst_modtype 
         (map_mbid farg_id mp (Some resolve)) fbody_b
 

let translate_module env me = translate_module env  me

let rec add_module_expr_constraints env = function
  | MEBident _ -> env

  | MEBfunctor (_,mtb,meb) -> 
      add_module_expr_constraints (add_modtype_constraints env mtb) meb

  | MEBstruct (_,mod_struct_body) ->
      List.fold_left 
        (fun env (l,item) -> add_struct_elem_constraints env item)
        env
        mod_struct_body

  | MEBapply (meb1,meb2,cst) ->
      Environ.add_constraints cst 
        (add_module_expr_constraints 
	  (add_module_expr_constraints env meb1) 
	  meb2)

and add_struct_elem_constraints env = function 
  | SEBconst cb -> Environ.add_constraints cb.const_constraints env
  | SEBmind mib -> Environ.add_constraints mib.mind_constraints env
  | SEBmodule mb -> add_module_constraints env mb
  | SEBmodtype mtb -> add_modtype_constraints env mtb

and add_module_constraints env mb = 
  (* if there is a body, the mb.mod_type is either inferred from the
     body and hence uninteresting or equal to the non-empty
     user_mod_type *)
  let env = match mb.mod_expr with
    | None -> add_modtype_constraints env mb.mod_type
    | Some meb -> add_module_expr_constraints env meb
  in
  let env = match mb.mod_user_type with
    | None -> env
    | Some mtb -> add_modtype_constraints env mtb
  in
    Environ.add_constraints mb.mod_constraints env

and add_modtype_constraints env = function
  | MTBident _ -> env
  | MTBfunsig (_,mtb1,mtb2) ->
      add_modtype_constraints
        (add_modtype_constraints env mtb1)
        mtb2
  | MTBsig (_,mod_sig_body) ->
      List.fold_left 
        (fun env (l,item) -> add_sig_elem_constraints env item)
        env
        mod_sig_body

and add_sig_elem_constraints env = function 
  | SPBconst cb -> Environ.add_constraints cb.const_constraints env
  | SPBmind mib -> Environ.add_constraints mib.mind_constraints env
  | SPBmodule {msb_modtype=mtb; msb_constraints=cst} -> 
      add_modtype_constraints (Environ.add_constraints cst env) mtb
  | SPBmodtype mtb -> add_modtype_constraints env mtb


