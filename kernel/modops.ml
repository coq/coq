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
open Identifier
open Names
open Term
open Declarations
open Mod_declarations
open Environ
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


let map_const_body f cb = 
  { const_body = option_app f cb.const_body;
    const_type = type_app f cb.const_type;
    const_hyps = (assert (cb.const_hyps=[]); []);
    const_constraints = (* TODO *) cb.const_constraints;
    const_opaque = cb.const_opaque}
  
let map_mind_packet f mbp = 
  { mind_consnames = mbp.mind_consnames;
    mind_typename = mbp.mind_typename;
    mind_nf_lc = Array.map (type_app f) mbp.mind_nf_lc;
    mind_nf_arity = type_app f mbp.mind_nf_arity;
    mind_user_lc = option_app (Array.map (type_app f)) mbp.mind_user_lc;
    mind_user_arity = option_app (type_app f) mbp.mind_user_arity;
    mind_sort = (* TODO *) mbp.mind_sort;
    mind_nrealargs = mbp.mind_nrealargs;
    mind_kelim = (* TODO *) mbp.mind_kelim;
    mind_listrec = mbp.mind_listrec;
    mind_finite = mbp.mind_finite;
    mind_nparams = mbp.mind_nparams;
    mind_params_ctxt = mbp.mind_params_ctxt}

let map_mind f mib = 
  { mind_ntypes = mib.mind_ntypes ;
    mind_hyps = (assert (mib.mind_hyps=[]); []) ;
    mind_packets = Array.map (map_mind_packet f) mib.mind_packets ;
    mind_constraints = (* TODO *) mib.mind_constraints }

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
  
let rec subst_module subst_modpath subst_modtype mb =
  { mod_type = subst_modtype mb.mod_type;
    mod_eq = option_app subst_modpath mb.mod_eq}


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
    (subst_modpath_mbid bid mp)
    (subst_modtype_mbid bid mp) 
    mb 

and subst_modtype_mbid bid mp = function
  | MTBident ln -> MTBident (subst_longname_mbid bid mp ln)
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
    (subst_modpath_msid sid mp) 
    (subst_modtype_msid sid mp) 
    mb 

and subst_modtype_msid sid mp = function
  | MTBident ln -> MTBident (subst_longname_msid sid mp ln)
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

(* we assume that the substitution of "mp" into "msid" is already done
(or unnecessary) *)
let rec add_signature mp sign env = 
  todo "add_signature should not be here (Modops) and should take care of universes"; 
(*  let mp = MPsid msid in *)
  let add_one env (l,elem) =
    let ln = make_ln mp l in
      match elem with
	| SPBconst cb -> Environ.add_constant ln cb env
	| SPBmind mib -> Environ.add_mind ln mib env
	| SPBmodule mb -> add_module (MPdot (mp,l)) mb env 
	    (* adds components as well *)
	| SPBmodtype mtb -> Environ.add_modtype ln mtb env
  in
    List.fold_left add_one env sign


and add_module mp mb env = 
  todo "universes!!!!";
  let env = Environ.shallow_add_module mp mb env in
    match scrape_modtype env mb.mod_type with
      | MTBident _ -> anomaly "scrape_modtype does not work!"
      | MTBsig (msid,sign) -> 
	  add_signature mp (subst_signature_msid msid mp sign) env 
      | _ -> env
