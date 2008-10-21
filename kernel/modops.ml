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
  error ("The label "^string_of_label l^" is already declared.")

let error_declaration_not_path _ = error "Declaration is not a path."

let error_application_to_not_path _ = error "Application to not path."

let error_not_a_functor _ = error "Application of not a functor."

let error_incompatible_modtypes _ _ = error "Incompatible module types."

let error_not_equal _ _ = error "Non equal modules."

let error_not_match l _ = error ("Signature components for label "^string_of_label l^" do not match.")

let error_no_such_label l = error ("No such label "^string_of_label l^".")

let error_incompatible_labels l l' = 
  error ("Opening and closing labels are not the same: "
	 ^string_of_label l^" <> "^string_of_label l'^" !")

let error_result_must_be_signature () = 
  error "The result module type must be a signature."

let error_signature_expected mtb =
  error "Signature expected."

let error_no_module_to_end _ = 
  error "No open module to end."

let error_no_modtype_to_end _ =
  error "No open module type to end."

let error_not_a_modtype_loc loc s = 
  user_err_loc (loc,"",str ("\""^s^"\" is not a module type."))

let error_not_a_module_loc loc s = 
  user_err_loc (loc,"",str ("\""^s^"\" is not a module."))

let error_not_a_module s = error_not_a_module_loc dummy_loc s

let error_not_a_constant l = 
  error ("\""^(string_of_label l)^"\" is not a constant.")

let error_with_incorrect l =
  error ("Incorrect constraint for label \""^(string_of_label l)^"\".")

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
	       (string_of_label l)^" is not empty.")


let error_no_such_label_sub l l1 l2 =
  error (l1^" is not a subtype of "^l2^".\nThe field "^(string_of_label l)^" is missing in "^l1^".")



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

(* the constraints are not important here *)

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

let rec check_modpath_equiv env mp1 mp2 = 
  if mp1=mp2 then () else
  let mp1 = scrape_alias mp1 env in
  let mp2 = scrape_alias mp2 env in
    if mp1=mp2 then ()
    else 
      error_not_equal mp1 mp2
	
let rec subst_with_body sub = function
  | With_module_body(id,mp,typ_opt,cst) ->
      With_module_body(id,subst_mp sub mp,Option.smartmap 
			 (subst_struct_expr sub) typ_opt,cst)
  | With_definition_body(id,cb) ->
      With_definition_body( id,subst_const_body sub cb)

and subst_modtype sub mtb =
  let typ_expr' = subst_struct_expr sub mtb.typ_expr in
    if typ_expr'==mtb.typ_expr then
      mtb
    else
      { mtb with 
	  typ_expr = typ_expr'}
	
and subst_structure sub sign = 
  let subst_body  = function
      SFBconst cb -> 
	SFBconst (subst_const_body sub cb)
    | SFBmind mib -> 
	SFBmind (subst_mind sub mib)
    | SFBmodule mb -> 
	SFBmodule (subst_module sub mb)
    | SFBmodtype mtb -> 
	SFBmodtype (subst_modtype sub mtb)
    | SFBalias (mp,typ_opt,cst) ->
	SFBalias (subst_mp sub mp,Option.smartmap 
		    (subst_struct_expr sub) typ_opt,cst)
  in
    List.map (fun (l,b) -> (l,subst_body b)) sign

and subst_module  sub mb =
  let mtb' = Option.smartmap (subst_struct_expr sub) mb.mod_type in
  (* This is similar to the previous case. In this case we have
     a module M in a signature that is knows to be equivalent to a module M'
     (because the signature is "K with Module M := M'") and we are substituting
     M' with some M''. *)
  let me' = Option.smartmap (subst_struct_expr sub) mb.mod_expr in
  let mb_alias = update_subst sub mb.mod_alias in
   let mb_alias =  if mb_alias = empty_subst then
     join_alias mb.mod_alias sub 
   else 
     join mb_alias (join_alias mb.mod_alias sub)
   in
     if mtb'==mb.mod_type && mb.mod_expr == me' 
      && mb_alias == mb.mod_alias
    then mb else
      { mod_expr = me';
	mod_type=mtb'; 
	mod_constraints=mb.mod_constraints;
	mod_alias = mb_alias;
	mod_retroknowledge=mb.mod_retroknowledge}


and subst_struct_expr sub = function
    | SEBident mp -> SEBident (subst_mp sub  mp)
    | SEBfunctor (msid, mtb, meb') -> 
	SEBfunctor(msid,subst_modtype sub mtb,subst_struct_expr sub meb')
    | SEBstruct (msid,str)->
	SEBstruct(msid, subst_structure sub str)
    | SEBapply (meb1,meb2,cst)->
	SEBapply(subst_struct_expr sub meb1,
		 subst_struct_expr sub meb2,
		 cst)
    | SEBwith (meb,wdb)-> 
	SEBwith(subst_struct_expr sub meb,
		subst_with_body sub wdb)
 

let subst_signature_msid msid mp = 
  subst_structure (map_msid msid mp)

(* spiwack: here comes the function which takes care of importing 
   the retroknowledge declared in the library *)
(* lclrk : retroknowledge_action list, rkaction : retroknowledge action *)
let add_retroknowledge msid mp =
  let subst = add_msid msid mp empty_subst in
  let subst_and_perform rkaction env =
    match rkaction with
      | Retroknowledge.RKRegister (f, e) ->
	  Environ.register env f 
	  (match e with 
	    | Const kn -> kind_of_term (subst_mps subst (mkConst kn))
	    | Ind ind -> kind_of_term (subst_mps subst (mkInd ind))
	    | _ -> anomaly "Modops.add_retroknowledge: had to import an unsupported kind of term")
  in
  fun lclrk env ->
  (* The order of the declaration matters, for instance (and it's at the
     time this comment is being written, the only relevent instance) the
     int31 type registration absolutely needs int31 bits to be registered.
     Since the local_retroknowledge is stored in reverse order (each new
     registration is added at the top of the list) we need a fold_right
     for things to go right (the pun is not intented). So we lose 
     tail recursivity, but the world will have exploded before any module
     imports 10 000 retroknowledge registration.*)
  List.fold_right subst_and_perform lclrk env



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


let rec eval_struct env = function 
  | SEBident mp -> 
      begin
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
	| SEBstruct (msid,sign) ->
	    join_alias 
	      (subst_key (map_msid msid mp) sub_alias)
	      (map_msid msid mp)
	| _ -> sub_alias in
      let sub_alias1 = update_subst sub_alias 
	(map_mbid farg_id mp (None)) in
      let resolve = resolver_of_environment farg_id farg_b mp sub_alias env in
	eval_struct env (subst_struct_expr 
			   (join sub_alias1 
			      (map_mbid farg_id mp (Some resolve))) fbody_b)
  | SEBwith (mtb,(With_definition_body _ as wdb)) ->
      let mtb',_ = merge_with env mtb wdb empty_subst in
	mtb'
  | SEBwith (mtb, (With_module_body (_,mp,_,_) as wdb)) ->
      let alias_in_mp =
	(lookup_modtype mp env).typ_alias in
      let alias_in_mp = match eval_struct env (SEBident mp) with
	| SEBstruct (msid,sign) -> subst_key (map_msid msid mp) alias_in_mp
	| _ -> alias_in_mp in
      let mtb',_ = merge_with env mtb wdb alias_in_mp in
	mtb'
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
      let env' = add_signature (MPself msid) before env in
      let new_spec,subst = match with_decl with
        | With_definition_body ([],_)
        | With_module_body ([],_,_,_) -> assert false
	| With_definition_body ([id],c) -> 
	    SFBconst c,None
	| With_module_body ([id], mp,typ_opt,cst) ->
	    let mp' = scrape_alias mp env' in
	    let new_alias = update_subst alias (map_mp (mp_rec [id]) mp') in
	      SFBalias (mp,typ_opt,Some cst),
	    Some(join (map_mp (mp_rec [id]) mp') new_alias)
	| With_definition_body (_::_,_) 
        | With_module_body (_::_,_,_,_) -> 
	    let old = match spec with
		SFBmodule msb -> msb
	      | _ -> error_not_a_module (string_of_label l)
	    in
            let new_with_decl,subst1 = 
	      match with_decl with
                  With_definition_body (_,c) -> With_definition_body (idl,c),None
		| With_module_body (idc,mp,typ_opt,cst) -> 
		    let mp' = scrape_alias mp env' in
		    With_module_body (idl,mp,typ_opt,cst),
		      Some(map_mp (mp_rec (List.rev idc)) mp') 
	    in
	    let subst = match subst1 with
	      | None -> None
	      | Some s -> Some (join s (update_subst alias s)) in
            let modtype,subst_msb = 
              merge_with env' (type_of_mb env' old) new_with_decl alias in
            let msb =
	      { mod_expr = None;
		mod_type = Some modtype; 
		mod_constraints = old.mod_constraints;
		mod_alias = begin 
		  match subst_msb with
		    |None -> empty_subst
		    |Some s -> s
		end;
		mod_retroknowledge = old.mod_retroknowledge}
	    in
	      (SFBmodule msb),subst
      in
	SEBstruct(msid,  before@(l,new_spec)::
		    (Option.fold_right subst_structure subst after)),subst
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
	  add_retroknowledge msid mp (mb.mod_retroknowledge)
	    (add_signature mp (subst_signature_msid msid mp sign) env)
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
   | SFBalias (mp1,typ_opt,cst) ->
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

(* returns a resolver for kn that maps mbid to mp. We only keep
   constants that have the inline flag *)
and  resolver_of_environment mbid modtype mp alias env =
 let constants = constants_of_modtype env (MPbound mbid) modtype.typ_expr in
 let constants = List.map (fun (l,cb) -> (l,subst_const_body alias cb)) constants in
 let rec make_resolve = function
   | [] -> []
   | (con,expecteddef)::r ->
       let con' = replace_mp_in_con (MPbound mbid) mp con in
       let con',_ = subst_con alias con' in
  (*     let con' = replace_mp_in_con (MPbound mbid) mp con' in *)
	 try
	   if expecteddef.Declarations.const_inline then
	     let constant = lookup_constant con' env in
	     if (not constant.Declarations.const_opaque) then
	       let constr = Option.map Declarations.force
		 constant.Declarations.const_body in
		 (con,constr)::(make_resolve r)
	     else make_resolve r
	   else make_resolve r
	 with Not_found -> error_no_such_label (con_label con')
 in
 let resolve = make_resolve constants in
   Mod_subst.make_resolver resolve

    
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
