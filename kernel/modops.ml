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
open Names
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

let error_no_module_to_end _ = 
  error "No open module to end"

let error_no_modtype_to_end _ =
  error "No open module type to end"

let error_not_a_modtype s = 
  error ("\""^s^"\" is not a module type")

let error_not_a_module s = 
  error ("\""^s^"\" is not a module")


let rec scrape_modtype env = function
  | MTBident ln -> scrape_modtype env (lookup_modtype ln env)
  | mtb -> mtb


let module_body mtb = 
  { mod_type = mtb;
    mod_eq = None }


let destr_functor = function
  | MTBfunsig (arg_id,arg_t,body_t) -> (arg_id,arg_t,body_t)
  | mtb -> error_not_a_functor mtb
 

let rec check_modpath_equiv env mp1 mp2 = 
  if mp1=mp2 then ();
  let mb1 = lookup_module mp1 env in
    match mb1.mod_eq with
      | None ->
	  let mb2 = lookup_module mp2 env in
	    (match mb2.mod_eq with
	      | None -> error_not_equal mp1 mp2
	      | Some mp2' -> check_modpath_equiv env mp2' mp1)
      | Some mp1' -> check_modpath_equiv env mp2 mp1'



(*
let subst_signature subst_constr subst_module subst_modtype sign = 
  let subst_body = function
      SPBconst cb -> 
	SPBconst (map_const_body subst_constr cb)
    | SPBmind mib -> 
	SPBmind (map_mind subst_constr mib)
    | SPBmodule mb -> 
	SPBmodule (subst_module mb)
    | SPBmodtype mtb -> 
	SPBmodtype (subst_modtype mtb)
  in
    List.map (fun (l,b) -> (l,subst_body b)) sign
  
let rec subst_module subst_mp subst_modtype mb =
  { mod_type = subst_modtype mb.mod_type;
    mod_eq = option_app subst_mp mb.mod_eq}


(*let rec subst_signature_mbid id mp sign
  let subst_body = function
      SPBconst cb -> 
	SPBconst (map_const_body (subst_constr_mbid id mp) cb)
    | SPBmind mib -> 
	SPBmind (map_mind (subst_constr_mbid id mp) mib)
    | SPBmodule mb -> 
	SPBmodule (subst_module_mbid id mp mb)
    | SPBmodtype mtb -> 
	SPBmodtype (subst_modtype_mbid id mp mtb)
  in
    List.map (fun (l,b) -> (l,sub_body b)) sign
*)



let rec subst_signature_mbid bid mp sign =
  subst_signature 
    (subst_constr_mbid bid mp)
    (subst_module_mbid bid mp)
    (subst_modtype_mbid bid mp)
    sign

and subst_module_mbid bid mp mb = 
  subst_module 
    (subst_mp_mbid bid mp)
    (subst_modtype_mbid bid mp) 
    mb 

and subst_modtype_mbid bid mp = function
  | MTBident ln -> MTBident (subst_kernel_name_mbid bid mp ln)
  | MTBfunsig (arg_id, arg_b, body_b) ->
      assert (arg_id <> bid);
      assert (not (occur_mbid arg_id mp));
      MTBfunsig (arg_id, 
		 subst_modtype_mbid bid mp arg_b, 
		 subst_modtype_mbid bid mp body_b)
  | MTBsig (sid, msb) -> 
      (* assert sid <> bid; *)
      assert (not (occur_msid sid mp));
      MTBsig (sid, subst_signature_mbid bid mp msb)



let rec subst_signature_msid sid mp sign =
  subst_signature 
    (subst_constr_msid sid mp)
    (subst_module_msid sid mp)
    (subst_modtype_msid sid mp)
    sign

and subst_module_msid sid mp mb = 
  subst_module 
    (subst_mp_msid sid mp) 
    (subst_modtype_msid sid mp) 
    mb 

and subst_modtype_msid sid mp = function
  | MTBident ln -> MTBident (subst_kernel_name_msid sid mp ln)
  | MTBfunsig (arg_id, arg_b, body_b) ->
      (* assert arg_id <> sid; *)
      assert (not (occur_mbid arg_id mp));
      MTBfunsig (arg_id, 
		 subst_modtype_msid sid mp arg_b, 
		 subst_modtype_msid sid mp body_b)
  | MTBsig (sid1, msb) -> 
      assert (sid<>sid1);
      assert (not (occur_msid sid1 mp));
      MTBsig (sid1, subst_signature_msid sid mp msb)

*****************************************************)
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

and subst_module sub mb =
  { mod_type = subst_modtype sub mb.mod_type;
    mod_eq = option_app (subst_mp sub) mb.mod_eq}

let subst_signature_msid msid mp = 
  subst_signature (map_msid msid mp)

(* we assume that the substitution of "mp" into "msid" is already done
(or unnecessary) *)
let rec add_signature mp sign env = 
  todo "add_signature should not be here (Modops) and should take care of universes"; 
(*  let mp = MPself msid in *)
  let add_one env (l,elem) =
    let kn = make_kn mp empty_dirpath l in
      match elem with
	| SPBconst cb -> Environ.add_constant kn cb env
	| SPBmind mib -> Environ.add_mind kn mib env
	| SPBmodule mb -> add_module (MPdot (mp,l)) mb env 
	    (* adds components as well *)
	| SPBmodtype mtb -> Environ.add_modtype kn mtb env
  in
    List.fold_left add_one env sign


and add_module mp mb env = 
  todo "universes!!!!";
  let env = Environ.shallow_add_module mp mb env in
    match scrape_modtype env mb.mod_type with
      | MTBident _ -> anomaly "scrape_modtype does not work!"
      | MTBsig (msid,sign) -> 
	  add_signature mp (subst_signature_msid msid mp sign) env

      | MTBfunsig _ -> env


(* getting names of module components *)

(* We assume the original mp is in the environment with all its
   components. This is important because of module types *)

(*
let component_names env make_dir make_path dir mp =

  let inductive_names_from_body dir ln mib names =
    let names, _ = 
      Array.fold_left
	(fun (names, n) ind ->
	   let ind_p = (ln,n) in
	   let names, _ =
	     Array.fold_left
	       (fun (names, p) l ->
		let sp = make_path dir l in
		  ((sp, ConstructRef (ind_p,p)) :: names, p+1))
	       (names, 1) ind.mind_consnames in
	   let sp = make_path dir ind.mind_typename in
	     ((sp, IndRef ind_p) :: names, n+1))
	(names, 0) mib.mind_packets
    in names
	 
  in
    
  let rec process_signature dir mp sign names = 
    let process_one names (l,elem) =
      let ln = make_ln mp l in
      let path = make_path dir l in
	match elem with
	  | SPBconst _ -> (path,ConstRef ln)::names
	  | SPBmind mib -> 
	      inductive_names_from_body dir ln mib names
	  | SPBmodule _ -> 
	      let mp' = MPdot (mp,l) in
	      let dir' = make_dir dir l in
	      let names' = (path, ModRef mp')::names in
		process_module dir' mp' names'
	  | SPBmodtype mtb -> 
	      (path, ModTypeRef ln)::names
    in
      List.fold_left process_one names sign
	
  and process_module dir mp names = 
    let mb = Environ.lookup_module mp env in
      match scrape_modtype env mb.mod_type with
	| MTBident _ -> anomaly "scrape_modtype does not work!"
	| MTBsig (_,sign) -> 
	    process_signature dir mp sign names 
	| MTBfunsig _ -> names

  in
    List.rev (process_module dir mp [])
    
*)




