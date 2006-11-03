(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

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
open Mod_subst
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

let error_result_must_be_signature () = 
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

let error_a_generative_module_expected l =
  error ("The module " ^ string_of_label l ^ " is not generative. Only " ^
         "component of generative modules can be changed using the \"with\" " ^
         "construct.")

let error_local_context lo = 
  match lo with
      None -> 
	error ("The local context is not empty.")
    | (Some l) ->
	error ("The local context of the component "^
	       (string_of_label l)^" is not empty")

let error_circular_with_module l =
  error ("The construction \"with Module "^(string_of_id l)^":=...\" is about to create\na circular module type. Their resolution is not implemented yet.\nIf you really need that feature, please report.")

let rec scrape_modtype env = function
  | MTBident kn -> scrape_modtype env (lookup_modtype kn env)
  | mtb -> mtb

(* the constraints are not important here *)
let module_body_of_spec msb = 
    { mod_type = msb.msb_modtype;
      mod_equiv = msb.msb_equiv;
      mod_expr = None;
      mod_user_type = None;
      mod_constraints = Constraint.empty}

let module_body_of_type mtb = 
  { mod_type = mtb;
    mod_equiv = None;
    mod_expr = None;
    mod_user_type = None;
    mod_constraints = Constraint.empty}


(* the constraints are not important here *)
let module_spec_of_body mb = 
  { msb_modtype = mb.mod_type; 
    msb_equiv = mb.mod_equiv; 
    msb_constraints = Constraint.empty}



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
    (* This is the case in which I am substituting a whole module.
       For instance "Module M(X). Module N := X. End M". When I apply
       M to M' I must substitute M' for X in "Module N := X". *)
  | MTBident ln -> MTBident (subst_kn sub ln)
  | MTBfunsig (arg_id, arg_b, body_b) ->
      if occur_mbid arg_id sub then failwith "capture";
      MTBfunsig (arg_id, 
		 subst_modtype sub arg_b, 
		 subst_modtype sub body_b)
  | MTBsig (sid1, msb) -> 
      if occur_msid sid1 sub then failwith "capture";
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
  let mtb' = subst_modtype sub mb.msb_modtype in
  (* This is similar to the previous case. In this case we have
     a module M in a signature that is knows to be equivalent to a module M'
     (because the signature is "K with Module M := M'") and we are substituting
     M' with some M''. *)
  let mpo' = option_smartmap (subst_mp sub) mb.msb_equiv in
    if mtb'==mb.msb_modtype && mpo'==mb.msb_equiv then mb else
      { msb_modtype=mtb'; 
	msb_equiv=mpo'; 
	msb_constraints=mb.msb_constraints}

let subst_signature_msid msid mp = 
  subst_signature (map_msid msid mp)

(* we assume that the substitution of "mp" into "msid" is already done
(or unnecessary) *)
let rec add_signature mp sign env = 
  let add_one env (l,elem) =
    let kn = make_kn mp empty_dirpath l in
    let con = make_con mp empty_dirpath l in
      match elem with
	| SPBconst cb -> Environ.add_constant con cb env
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


let rec constants_of_specification env mp sign =
 let aux (env,res) (l,elem) =
  match elem with
   | SPBconst cb -> env,((make_con mp empty_dirpath l),cb)::res
   | SPBmind _ -> env,res
   | SPBmodule mb ->
       let new_env =  add_module (MPdot (mp,l)) (module_body_of_spec mb) env in 
       new_env,(constants_of_modtype env (MPdot (mp,l))
		  (module_body_of_spec mb).mod_type) @ res
   | SPBmodtype mtb -> 
       (* module type dans un module type. 
	  Il faut au moins mettre mtb dans l'environnement (avec le bon 
	  kn pour pouvoir continuer aller deplier les modules utilisant ce 
	  mtb
	  ex: 
	  Module Type T1. 
	  Module Type T2.
	     ....
    	    End T2.
	  .....
            Declare Module M : T2.
         End T2 
	  si on ne rajoute pas T2 dans l'environement de typage 
	  on va exploser au moment du Declare Module
       *)
       let new_env = Environ.add_modtype (make_kn mp empty_dirpath l) mtb env in 
       new_env, constants_of_modtype env (MPdot(mp,l)) mtb @ res
 in
 snd (List.fold_left aux (env,[]) sign)

and constants_of_modtype env mp modtype =
 match scrape_modtype env modtype with
    MTBident _ -> anomaly "scrape_modtype does not work!"
  | MTBsig (msid,sign) ->
     constants_of_specification env mp
      (subst_signature_msid msid mp sign)
  | MTBfunsig _ -> []

(* returns a resolver for kn that maps mbid to mp *)
(* Nota: Some delta-expansions used to happen here. 
    Browse SVN if you want to know more. *)
let resolver_of_environment mbid modtype mp env =
 let constants = constants_of_modtype env (MPbound mbid) modtype in
 let resolve = List.map (fun (con,_) -> con,None) constants in 
 Mod_subst.make_resolver resolve


let strengthen_const env mp l cb = 
  match cb.const_opaque, cb.const_body with
  | false, Some _ -> cb
  | true, Some _ 
  | _, None -> 
      let const = mkConst (make_con mp empty_dirpath l) in 
      let const_subs = Some (Declarations.from_val const) in
	{cb with 
      	   const_body = const_subs;
	   const_opaque = false;
           const_body_code = Cemitcodes.from_val
             (compile_constant_body env const_subs false false)
	}

let strengthen_mind env mp l mib = match mib.mind_equiv with
  | Some _ -> mib
  | None -> {mib with mind_equiv = Some (make_kn mp empty_dirpath l)}
    
let rec strengthen_mtb env mp mtb = match scrape_modtype env mtb with
  | MTBident _ -> anomaly "scrape_modtype does not work!"
  | MTBfunsig _ -> mtb
  | MTBsig (msid,sign) -> MTBsig (msid,strengthen_sig env msid sign mp)

and strengthen_mod env mp msb = 
  { msb_modtype = strengthen_mtb env mp msb.msb_modtype;
    msb_equiv = begin match msb.msb_equiv with
      | Some _ -> msb.msb_equiv
      | None -> Some mp 
    end ;
    msb_constraints = msb.msb_constraints; }

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

