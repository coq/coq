(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

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

exception Not_path

let path_of_mexpr = function
  | MEident mb -> mb
  | _ -> raise Not_path


let rec list_fold_map2 f e = function 
  |  []  -> (e,[],[])
  |  h::t -> 
       let e',h1',h2' = f e h in
       let e'',t1',t2' = list_fold_map2 f e' t in
	 e'',h1'::t1',h2'::t2'


let rec translate_modtype env mte =
  match mte with
    | MTEident ln -> MTBident ln
    | MTEfunsig (arg_id,arg_e,body_e) -> 
	let arg_b = translate_modtype env arg_e in
	let env' = 
	  add_module (MPbound arg_id) (module_body_of_type arg_b) env in
	let body_b = translate_modtype env' body_e in
	  MTBfunsig (arg_id,arg_b,body_b)
    | MTEsig (msid,sig_e) ->
	let str_b,sig_b = translate_entry_list env msid false sig_e in
	  MTBsig (msid,sig_b)

and translate_entry_list env msid is_definition sig_e = 
  let mp = MPself msid in
  let do_entry env (l,e) = 
    let kn = make_kn mp empty_dirpath l in
    match e with
      | SPEconst ce ->
	  let cb = translate_constant env ce in
	    add_constant kn cb env, (l, SEBconst cb), (l, SPBconst cb)
      | SPEmind mie -> 
	  let mib = translate_mind env mie in
	    add_mind kn mib env, (l, SEBmind mib), (l, SPBmind mib)
      | SPEmodule me ->
	  let mb = translate_module env is_definition me in
	  let mspec = mb.mod_type, mb.mod_equiv in
	  let mp' = MPdot (mp,l) in
	    add_module mp' mb env, (l, SEBmodule mb), (l, SPBmodule mspec)
      | SPEmodtype mte ->
	  let mtb = translate_modtype env mte in
	    add_modtype kn mtb env, (l, SEBmodtype mtb), (l, SPBmodtype mtb)
  in
  let _,str_b,sig_b = list_fold_map2 do_entry env sig_e
  in
    str_b,sig_b

(* if [is_definition=true], [mod_entry_expr] may be any expression.
   Otherwise it must be a path *)

and translate_module env is_definition me =
  match me.mod_entry_expr, me.mod_entry_type with
    | None, None -> 
	anomaly "Mod_typing.translate_module: empty type and expr in module entry"
    | None, Some mte -> 
	let mtb = translate_modtype env mte in
	{ mod_expr = None;
	  mod_user_type = Some (mtb, Constraint.empty);
	  mod_type = mtb;
	  mod_equiv = None }
    | Some mexpr, _ -> 
	let meq_o = (* do we have a transparent module ? *)
	  try       (* TODO: transparent field in module_entry *)
	    Some (path_of_mexpr mexpr)
	  with 
	    | Not_path -> None
	in
	let meb,mtb1 = 
	  if is_definition then
	    translate_mexpr env mexpr
	  else 
	    let mp = 
	      try 
		path_of_mexpr mexpr 
	      with 
		| Not_path -> error_declaration_not_path mexpr
	    in
	      MEBident mp, (lookup_module mp env).mod_type
	in
	let mtb,mod_user_type =
	  match me.mod_entry_type with
	    | None -> mtb1, None
	    | Some mte -> 
		let mtb2 = translate_modtype env mte in
		  mtb2, Some (mtb2, check_subtypes env mtb1 mtb2)
	in
	  { mod_type = mtb;
	    mod_user_type = mod_user_type;
	    mod_expr = Some meb;
	    mod_equiv = meq_o }

(* translate_mexpr : env -> module_expr -> module_expr_body * module_type_body *)
and translate_mexpr env mexpr = match mexpr with
  | MEident mp -> 
      MEBident mp,
      (lookup_module mp env).mod_type
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
	MEBapply(feb,meb,cst),
	subst_modtype (map_mbid farg_id mp) fbody_b
  | MEstruct (msid,structure) ->
      let structure,signature = translate_entry_list env msid true structure in
	MEBstruct (msid,structure),
	MTBsig (msid,signature)


(* is_definition is true - me.mod_entry_expr may be any expression *)
let translate_module env me = translate_module env true me

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
  let env = match mb.mod_expr with
    | None -> env
    | Some meb -> add_module_expr_constraints env meb
  in
  let env = match mb.mod_user_type with
    | None -> env
    | Some (mtb,cst) -> 
	Environ.add_constraints cst (add_modtype_constraints env mtb)
  in
    env

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
  | SPBmodule (mtb,_) -> add_modtype_constraints env mtb
  | SPBmodtype mtb -> add_modtype_constraints env mtb


