(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: modops.ml 9872 2007-05-30 16:01:18Z soubiran $ i*)

(*i*)
open Util
open Pp
open Names
open Univ
open Term
open Declarations
open Environ
(*i*)

let error_not_a_constant l = 
  error ("\""^(string_of_label l)^"\" is not a constant")

let error_not_a_functor _ = error "Application of not a functor"

let error_incompatible_modtypes _ _ = error "Incompatible module types"

let error_not_equal _ _ = error "Not equal modules"

let error_not_match l _ =
  error ("Signature components for label "^string_of_label l^" do not match")

let error_no_such_label l = error ("No such label "^string_of_label l)

let error_no_such_label_sub l l1 l2 =
  let l1 = string_of_msid l1 in
  let l2 = string_of_msid l2 in
  error (l1^" is not a subtype of "^l2^".\nThe field "^
         string_of_label l^" is missing (or invisible) in "^l1^".")

let error_not_a_module_loc loc s = 
  user_err_loc (loc,"",str ("\""^string_of_label s^"\" is not a module"))

let error_not_a_module s = error_not_a_module_loc dummy_loc s

let error_with_incorrect l =
  error ("Incorrect constraint for label \""^(string_of_label l)^"\"")

let error_a_generative_module_expected l =
  error ("The module " ^ string_of_label l ^ " is not generative. Only " ^
         "component of generative modules can be changed using the \"with\" " ^
         "construct.")

let error_signature_expected mtb =
  error "Signature expected"

let error_application_to_not_path _ = error "Application to not path"


let module_body_of_type mtb = 
  { mod_type = Some mtb.typ_expr;
    mod_expr = None;
    mod_constraints = Constraint.empty;
    mod_alias = mtb.typ_alias;
    mod_retroknowledge = []}

let module_type_of_module mp mb =
  {typ_expr = 
      (match mb.mod_type with
	| Some expr -> expr
	| None -> (match mb.mod_expr with
		     | Some expr -> expr
		     | None -> 
			 anomaly "Modops: empty expr and type"));
   typ_alias = mb.mod_alias;
   typ_strength = mp
  }



let rec list_split_assoc k rev_before = function
  | [] -> raise Not_found
  | (k',b)::after when k=k' -> rev_before,b,after
  | h::tail -> list_split_assoc k (h::rev_before) tail

let path_of_seb = function
  | SEBident mp -> mp
  | _ -> anomaly "Modops: evaluation failed."


let destr_functor env mtb =
  match mtb with
  | SEBfunctor (arg_id,arg_t,body_t) ->
      	    (arg_id,arg_t,body_t)
  | _ -> error_not_a_functor mtb


let rec check_modpath_equiv env mp1 mp2 = 
  if mp1=mp2 then () else
  let mp1 = scrape_alias mp1 env in
  let mp2 = scrape_alias mp2 env in
    if mp1=mp2 then ()
    else 
      error_not_equal mp1 mp2



let strengthen_const env mp l cb = 
  match cb.const_opaque, cb.const_body with
  | false, Some _ -> cb
  | true, Some _ 
  | _, None -> 
      let const = Const (make_con mp empty_dirpath l) in 
      let const_subs = Some (Declarations.from_val const) in
	{cb with 
      	   const_body = const_subs;
	   const_opaque = false
	}

let strengthen_mind env mp l mib = match mib.mind_equiv with
  | Some _ -> mib
  | None -> {mib with mind_equiv = Some (make_kn mp empty_dirpath l)}


let rec eval_struct env = function 
  | SEBident mp -> 
      begin
        let mp = scrape_alias mp env in
	let mtb =lookup_modtype mp env in
	match mtb.typ_expr,mtb.typ_strength with
	    mtb,None -> eval_struct env mtb
	  | mtb,Some mp -> strengthen_mtb env mp (eval_struct env mtb)
      end
  | SEBapply (seb1,seb2,_) -> 
      let svb1 = eval_struct env seb1 in
      let farg_id, farg_b, fbody_b = destr_functor env svb1 in
      let mp = path_of_seb seb2 in
      let mp = scrape_alias mp env in
      let sub_alias = (lookup_modtype mp env).typ_alias in
      let sub_alias = match eval_struct env (SEBident mp) with
	  | SEBstruct (msid,sign) -> subst_key (map_msid msid mp) sub_alias
	  | _ -> sub_alias in
      let sub_alias = update_subst_alias sub_alias 
	(map_mbid farg_id mp) in
	eval_struct env (subst_struct_expr 
			   (join sub_alias (map_mbid farg_id mp)) fbody_b)
  | SEBwith (mtb,(With_definition_body _ as wdb)) ->
      merge_with env mtb wdb empty_subst
  | SEBwith (mtb, (With_module_body (_,mp,_,_) as wdb)) ->
      let alias_in_mp =
	(lookup_modtype mp env).typ_alias in
	merge_with env mtb wdb alias_in_mp
(*  | SEBfunctor(mbid,mtb,body) -> 
      let env = add_module (MPbound mbid) (module_body_of_type mtb) env in
	SEBfunctor(mbid,mtb,eval_struct env body) *)
  | mtb -> mtb
      
and type_of_mb env mb =
  match mb.mod_type,mb.mod_expr with
      None,Some b -> eval_struct env b
    | Some t, _ -> eval_struct env t
    | _,_ -> anomaly 
	"Modops:  empty type and empty expr" 
	  
and merge_with env mtb with_decl alias= 
  let msid,sig_b = match (eval_struct env mtb) with 
    | SEBstruct(msid,sig_b) -> msid,sig_b
    | _ -> error_signature_expected mtb
  in
  let id,idl = match with_decl with 
    | With_definition_body (id::idl,_) | With_module_body (id::idl,_,_,_) -> id,idl
    | With_definition_body ([],_) | With_module_body ([],_,_,_) -> assert false
  in
  let l = label_of_id id in
    try
      let rev_before,spec,after = list_split_assoc l [] sig_b in
      let before = List.rev rev_before in
      let rec mp_rec = function
	| [] -> MPself msid
	| i::r -> MPdot(mp_rec r,label_of_id i)
      in 
      let new_spec,subst = match with_decl with
        | With_definition_body ([],_)
        | With_module_body ([],_,_,_) -> assert false
	| With_definition_body ([id],c) -> 
	    SFBconst c,None
	| With_module_body ([id], mp,typ_opt,cst) ->
	    let mp' = scrape_alias mp env in
	      SFBalias (mp,typ_opt,Some cst),
	    Some(join (map_mp (mp_rec [id]) mp') alias)
	| With_definition_body (_::_,_) 
        | With_module_body (_::_,_,_,_) -> 
	    let old = match spec with
		SFBmodule msb -> msb
	      | _ -> error_not_a_module l
	    in
            let new_with_decl,subst1 = 
	      match with_decl with
                  With_definition_body (_,c) -> With_definition_body (idl,c),None
		| With_module_body (idc,mp,t,cst) -> 
		    With_module_body (idl,mp,t,cst),
		      Some(map_mp (mp_rec idc) mp) 
	    in
	    let subst = Option.fold_right join subst1 alias in
            let modtype = 
              merge_with env (type_of_mb env old) new_with_decl alias in
            let msb =
	      { mod_expr = None;
		mod_type = Some modtype; 
		mod_constraints = old.mod_constraints;
		mod_alias = subst;
		mod_retroknowledge = old.mod_retroknowledge}
	    in
	      (SFBmodule msb),Some subst
      in
	SEBstruct(msid,  before@(l,new_spec)::
		    (Option.fold_right subst_structure subst after))
    with
	Not_found -> error_no_such_label l

and add_signature mp sign env = 
  let add_one env (l,elem) =
    let kn = make_kn mp empty_dirpath l in
    let con = make_con mp empty_dirpath l in
      match elem with
	| SFBconst cb -> Environ.add_constant con cb env
	| SFBmind mib -> Environ.add_mind kn mib env
	| SFBmodule mb -> 
	    add_module (MPdot (mp,l)) mb env 
	      (* adds components as well *)
	| SFBalias (mp1,_,cst) -> 
	    Environ.register_alias (MPdot(mp,l)) mp1 env
	| SFBmodtype mtb -> Environ.add_modtype (MPdot(mp,l)) 
	    mtb env
  in
    List.fold_left add_one env sign

and add_module mp mb env = 
  let env = Environ.shallow_add_module mp mb env in
  let env =
    Environ.add_modtype mp (module_type_of_module (Some mp) mb) env
  in
  let mod_typ = type_of_mb env mb in
    match mod_typ with
      | SEBstruct (msid,sign) -> 
	  add_signature mp (subst_signature_msid msid mp sign) env
      | SEBfunctor _ -> env
      | _ -> anomaly "Modops:the evaluation of the structure failed "
	  


and  constants_of_specification env mp sign =
 let aux (env,res) (l,elem) =
  match elem with
   | SFBconst cb -> env,((make_con mp empty_dirpath l),cb)::res
   | SFBmind _ -> env,res
   | SFBmodule mb ->
       let new_env =  add_module (MPdot (mp,l)) mb env in 
       new_env,(constants_of_modtype env (MPdot (mp,l))
		   (type_of_mb env mb)) @ res
   | SFBalias (mp1,_,cst) ->
       let new_env =  register_alias (MPdot (mp,l)) mp1 env in 
       new_env,(constants_of_modtype env (MPdot (mp,l))
		   (eval_struct env (SEBident mp1))) @ res
   | SFBmodtype mtb -> 
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
       let new_env = Environ.add_modtype (MPdot(mp,l)) mtb env in 
       new_env, (constants_of_modtype env (MPdot(mp,l)) mtb.typ_expr) @ res
 in
 snd (List.fold_left aux (env,[]) sign)

and constants_of_modtype env mp modtype =
  match (eval_struct env modtype) with
      SEBstruct (msid,sign) ->
	constants_of_specification env mp
	  (subst_signature_msid msid mp sign)
    | SEBfunctor _ -> []
    | _ -> anomaly "Modops:the evaluation of the structure failed "
    
and strengthen_mtb env mp mtb =
  let mtb1 = eval_struct env mtb in 
  match  mtb1 with
  | SEBfunctor _ -> mtb1
  | SEBstruct (msid,sign) -> 
      SEBstruct (msid,strengthen_sig env msid sign mp)
  | _ -> anomaly "Modops:the evaluation of the structure failed "

and strengthen_mod env mp mb = 
  let mod_typ = type_of_mb env mb in
    { mod_expr = mb.mod_expr;
      mod_type = Some (strengthen_mtb env mp mod_typ);
      mod_constraints = mb.mod_constraints;
      mod_alias = mb.mod_alias;
      mod_retroknowledge = mb.mod_retroknowledge}
      
and strengthen_sig env msid sign mp = match sign with
  | [] -> []
  | (l,SFBconst cb) :: rest ->
      let item' = l,SFBconst (strengthen_const env mp l cb) in
      let rest' = strengthen_sig env msid rest mp in
	item'::rest'
  | (l,SFBmind mib) :: rest ->
      let item' = l,SFBmind (strengthen_mind env mp l mib) in
      let rest' = strengthen_sig env msid rest mp in
	item'::rest'
  | (l,SFBmodule mb) :: rest ->
      let mp' = MPdot (mp,l) in
	let item' = l,SFBmodule (strengthen_mod env mp' mb) in
	let env' = add_module 
	  (MPdot (MPself msid,l)) mb env in
        let rest' = strengthen_sig env' msid rest mp in
	item':: rest'
  | ((l,SFBalias (mp1,_,cst)) as item) :: rest ->
      let env' = register_alias (MPdot(MPself msid,l)) mp1 env in
      let rest' = strengthen_sig env' msid rest mp in
	item::rest'
  | (l,SFBmodtype mty as item) :: rest -> 
      let env' = add_modtype 
		   (MPdot((MPself msid),l)) 
		   mty
		   env
      in
      let rest' = strengthen_sig env' msid rest mp in
	item::rest'

    
let strengthen env mtb mp = strengthen_mtb env mp mtb

let update_subst env mb mp =
  match type_of_mb env mb with
    | SEBstruct(msid,str) -> false, join_alias 
	(subst_key (map_msid msid mp) mb.mod_alias)
	(map_msid msid mp)
    | _ -> true, mb.mod_alias
