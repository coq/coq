(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Util
open Pp
open Names
open Univ
open Term
open Declarations
open Environ
open Entries
(*i*)

let error_existing_label l = 
  error ("The label "^string_of_label l^" is already declared")

let error_declaration_not_path _ = error "Declaration is not a path"

let error_application_to_not_path _ = error "Application to not path"

let error_not_a_functor _ = error "Application of not a functor"

let error_incompatible_modtypes _ _ = error "Incompatible module types"

let error_not_equal _ _ = error "Not equal modules"

let error_not_match l _ = error ("Signature components for label "^string_of_label l^" do not match")

let error_no_such_label l = error ("No such label "^string_of_label l)

let error_incompatible_labels l l' = 
  error ("Opening and closing labels are not the same: "
	 ^string_of_label l^" <> "^string_of_label l'^" !")

let error_result_must_be_signature mtb = 
  error "The result module type must be a signature"

let error_signature_expected mtb =
  error "Signature expected"

let error_no_module_to_end _ = 
  error "No open module to end"

let error_no_modtype_to_end _ =
  error "No open module type to end"

let error_not_a_modtype_loc loc s = 
  user_err_loc (loc,"",str ("\""^s^"\" is not a module type"))

let error_not_a_module_loc loc s = 
  user_err_loc (loc,"",str ("\""^s^"\" is not a module"))

let error_not_a_module s = error_not_a_module_loc dummy_loc s

let error_not_a_constant l = 
  error ("\""^(string_of_label l)^"\" is not a constant")

let error_with_incorrect l =
  error ("Incorrect constraint for label \""^(string_of_label l)^"\"")

let rec scrape_modtype env = function
  | MTBident kn -> scrape_modtype env (lookup_modtype kn env)
  | mtb -> mtb


let module_body_of_spec (mty,mpo,cst) = 
    { mod_type = mty;
      mod_equiv = mpo;
      mod_expr = None;
      mod_user_type = None;
      mod_constraints = cst}

let module_body_of_type mtb = 
  { mod_type = mtb;
    mod_equiv = None;
    mod_expr = None;
    mod_user_type = None;
    mod_constraints = Constraint.empty}


let module_spec_of_body mb = mb.mod_type, mb.mod_equiv, mb.mod_constraints

let destr_functor = function
  | MTBfunsig (arg_id,arg_t,body_t) -> (arg_id,arg_t,body_t)
  | mtb -> error_not_a_functor mtb
 

let rec check_modpath_equiv env mp1 mp2 = 
  if mp1=mp2 then () else
  let mb1 = lookup_module mp1 env in
    match mb1.mod_equiv with
      | None ->
	  let mb2 = lookup_module mp2 env in
	    (match mb2.mod_equiv with
	      | None -> error_not_equal mp1 mp2
	      | Some mp2' -> check_modpath_equiv env mp2' mp1)
      | Some mp1' -> check_modpath_equiv env mp2 mp1'


let rec subst_modtype sub = function
  | MTBident ln -> MTBident (subst_kn sub ln)
  | MTBfunsig (arg_id, arg_b, body_b) ->
      assert (not (occur_mbid arg_id sub));
      MTBfunsig (arg_id, 
		 subst_modtype sub arg_b, 
		 subst_modtype sub body_b)
  | MTBsig (sid1, msb) -> 
      assert (not (occur_msid sid1 sub));
      MTBsig (sid1, subst_signature sub msb)

and subst_signature sub sign = 
  let subst_body = function
      SPBconst cb -> 
	SPBconst (subst_const_body sub cb)
    | SPBmind mib -> 
	SPBmind (subst_mind sub mib)
    | SPBmodule mb -> 
	SPBmodule (subst_module sub mb)
    | SPBmodtype mtb -> 
	SPBmodtype (subst_modtype sub mtb)
  in
    List.map (fun (l,b) -> (l,subst_body b)) sign

and subst_module sub (mtb,mpo,cst as mb) =
  let mtb' = subst_modtype sub mtb in
  let mpo' = option_smartmap (subst_mp sub) mpo in
    if mtb'==mtb && mpo'==mpo then mb else
      (mtb',mpo',cst)

let subst_signature_msid msid mp = 
  subst_signature (map_msid msid mp)

(* we assume that the substitution of "mp" into "msid" is already done
(or unnecessary) *)
let rec add_signature mp sign env = 
  let add_one env (l,elem) =
    let kn = make_kn mp empty_dirpath l in
      match elem with
	| SPBconst cb -> Environ.add_constant kn cb env
	| SPBmind mib -> Environ.add_mind kn mib env
	| SPBmodule mb -> 
	    add_module (MPdot (mp,l)) (module_body_of_spec mb) env 
	    (* adds components as well *)
	| SPBmodtype mtb -> Environ.add_modtype kn mtb env
  in
    List.fold_left add_one env sign


and add_module mp mb env = 
  let env = Environ.shallow_add_module mp mb env in
    match scrape_modtype env mb.mod_type with
      | MTBident _ -> anomaly "scrape_modtype does not work!"
      | MTBsig (msid,sign) -> 
	  add_signature mp (subst_signature_msid msid mp sign) env

      | MTBfunsig _ -> env


let strengthen_const env mp l cb = match cb.const_body with
  | Some _ -> cb
  | None -> {cb with const_body = 
	       let const = mkConst (make_kn mp empty_dirpath l) in 
		 Some (Declarations.from_val const)
	    }

let strengthen_mind env mp l mib = match mib.mind_equiv with
  | Some _ -> mib
  | None -> {mib with mind_equiv = Some (make_kn mp empty_dirpath l)}
    
let rec strengthen_mtb env mp mtb = match scrape_modtype env mtb with
  | MTBident _ -> anomaly "scrape_modtype does not work!"
  | MTBfunsig _ -> mtb
  | MTBsig (msid,sign) -> MTBsig (msid,strengthen_sig env msid sign mp)
and strengthen_mod env mp (mtb,mpo,cst) = 
  let mtb' = strengthen_mtb env mp mtb in
  let mpo' = match mpo with
    | Some _ -> mpo
    | None -> Some mp
  in
    (mtb',mpo',cst)
and strengthen_sig env msid sign mp = match sign with
  | [] -> []
  | (l,SPBconst cb) :: rest ->
      let item' = l,SPBconst (strengthen_const env mp l cb) in
      let rest' = strengthen_sig env msid rest mp in
	item'::rest'
  | (l,SPBmind mib) :: rest ->
      let item' = l,SPBmind (strengthen_mind env mp l mib) in
      let rest' = strengthen_sig env msid rest mp in
	item'::rest'
  | (l,SPBmodule mb) :: rest ->
      let mp' = MPdot (mp,l) in
      let item' = l,SPBmodule (strengthen_mod env mp' mb) in
      let env' = add_module 
		   (MPdot (MPself msid,l)) 
		   (module_body_of_spec mb) 
		   env 
      in
      let rest' = strengthen_sig env' msid rest mp in
	item'::rest'
  | (l,SPBmodtype mty as item) :: rest -> 
      let env' = add_modtype 
		   (make_kn (MPself msid) empty_dirpath l) 
		   mty
		   env
      in
      let rest' = strengthen_sig env' msid rest mp in
	item::rest'

let strengthen env mtb mp = strengthen_mtb env mp mtb
