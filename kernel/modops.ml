(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Created by Jacek Chrzaszcz, Aug 2002 as part of the implementation of
   the Coq module system *)
(* Inlining and more liberal use of modules and module types by Claudio
   Sacerdoti, Nov 2004 *)
(* New structure-based model of modules and miscellaneous bug fixes by
   Élie Soubiran, from Feb 2008 *)

(* This file provides with various operations on modules and module types *)

open Util
open Pp
open Names
open Univ
open Term
open Declarations
open Environ
open Entries
open Mod_subst

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

let error_not_a_module_or_modtype_loc loc s =
  user_err_loc (loc,"",str ("\""^s^"\" is not a module or module type."))

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


let error_no_such_label_sub l l1 =
  error ("The field "^(string_of_label l)^" is missing in "^l1^".")

let error_with_in_module _ = error "The syntax \"with\" is not allowed for modules."

let error_application_to_module_type _ = error "Module application to a module type."

let destr_functor env mtb =
  match mtb with
  | SEBfunctor (arg_id,arg_t,body_t) ->
      	    (arg_id,arg_t,body_t)
  | _ -> error_not_a_functor mtb

let is_functor = function
 | SEBfunctor (arg_id,arg_t,body_t) -> true
 | _ -> false

let module_body_of_type mp mtb = 
  { mod_mp = mp;
    mod_type = mtb.typ_expr;
    mod_type_alg = mtb.typ_expr_alg;
    mod_expr = None;
    mod_constraints = mtb.typ_constraints;
    mod_delta = mtb.typ_delta;
    mod_retroknowledge = []
  }

let check_modpath_equiv env mp1 mp2 = 
  if mp1=mp2 then () else
    let mb1=lookup_module  mp1 env in
    let mb2=lookup_module mp2 env in
      if (delta_of_mp mb1.mod_delta mp1)=(delta_of_mp mb2.mod_delta mp2)
      then ()
      else error_not_equal mp1 mp2
	
let rec subst_with_body sub = function
  | With_module_body(id,mp) ->
      With_module_body(id,subst_mp sub mp)
  | With_definition_body(id,cb) ->
      With_definition_body( id,subst_const_body sub cb)

and subst_modtype sub do_delta mtb=
  let mp = subst_mp sub mtb.typ_mp in
  let sub = add_mp mtb.typ_mp mp empty_delta_resolver sub in
  let typ_expr' = subst_struct_expr sub do_delta mtb.typ_expr in
  let typ_alg' = 
    Option.smartmap 
      (subst_struct_expr sub (fun x y-> x)) mtb.typ_expr_alg in
  let mtb_delta = do_delta mtb.typ_delta sub in
    if typ_expr'==mtb.typ_expr && 
      typ_alg'==mtb.typ_expr_alg && mp==mtb.typ_mp then
	mtb
    else
      {mtb with 
	 typ_mp = mp;
	 typ_expr = typ_expr';
	 typ_expr_alg = typ_alg';
	 typ_delta = mtb_delta}
	
and subst_structure sub do_delta sign = 
  let subst_body = function
      SFBconst cb -> 
	SFBconst (subst_const_body sub cb)
    | SFBmind mib -> 
	SFBmind (subst_mind sub mib)
    | SFBmodule mb -> 
	SFBmodule (subst_module sub do_delta mb)
    | SFBmodtype mtb -> 
	SFBmodtype (subst_modtype sub do_delta mtb)
  in
    List.map (fun (l,b) -> (l,subst_body b)) sign

and subst_module sub do_delta mb =
  let mp = subst_mp sub mb.mod_mp in
  let sub = if is_functor mb.mod_type && not(mp=mb.mod_mp) then
    add_mp mb.mod_mp mp
      empty_delta_resolver sub else sub in 
  let id_delta = (fun x y-> x) in
  let mtb',me' = 
    let mtb = subst_struct_expr sub do_delta mb.mod_type in 
      match mb.mod_expr with
	  None -> mtb,None
	| Some me -> if me==mb.mod_type then
	    mtb,Some mtb
	  else mtb,Option.smartmap 
	    (subst_struct_expr sub id_delta) mb.mod_expr
  in
  let typ_alg' = Option.smartmap 
    (subst_struct_expr sub id_delta) mb.mod_type_alg in
  (* Check This *)
  let mb_retro =
    Util.list_smartmap (fun (pt,c as ptc) ->
      let c' = subst_mps sub c in
      if c' == c then ptc else (pt,c')) mb.mod_retroknowledge in
  let mb_delta = do_delta mb.mod_delta sub in
    if mtb'==mb.mod_type && mb.mod_expr == me' 
      && mb_delta == mb.mod_delta && mp == mb.mod_mp 
	&& mb_retro == mb.mod_retroknowledge
    then mb else
      { mb with
	  mod_mp = mp;
	  mod_expr = me';
	  mod_type_alg = typ_alg';
	  mod_type=mtb'; 
	  mod_delta = mb_delta;
	  mod_retroknowledge = mb_retro
      }

and subst_struct_expr sub do_delta = function
    | SEBident mp -> SEBident (subst_mp sub mp)
    | SEBfunctor (mbid, mtb, meb') -> 
	SEBfunctor(mbid,subst_modtype sub do_delta mtb
		     ,subst_struct_expr sub do_delta meb')
    | SEBstruct (str)->
	SEBstruct( subst_structure sub do_delta str)
    | SEBapply (meb1,meb2,cst)->
	SEBapply(subst_struct_expr sub do_delta meb1,
		 subst_struct_expr sub do_delta meb2,
		 cst)
    | SEBwith (meb,wdb)-> 
	SEBwith(subst_struct_expr sub do_delta meb,
		subst_with_body sub wdb)

let subst_signature subst =
  subst_structure subst 
    (fun resolver subst-> subst_codom_delta_resolver subst resolver)

let subst_struct_expr subst = 
  subst_struct_expr subst
    (fun resolver subst-> subst_codom_delta_resolver subst resolver)

let add_retroknowledge l env =
  List.fold_left add_retroknowledge env l

let rec add_signature mp sign resolver env = 
  let add_one env (l,elem) =
    let kn = make_kn mp empty_dirpath l in
    let con = constant_of_kn kn in
    let mind = mind_of_kn kn in
      match elem with
	| SFBconst cb -> 
	    let con =  constant_of_delta resolver con in
	      Environ.add_constant con cb env
	| SFBmind mib -> 
	    let mind =  mind_of_delta resolver mind in
	    Environ.add_mind mind mib env
	| SFBmodule mb -> add_module mb env
	      (* adds components as well *)
	| SFBmodtype mtb -> Environ.add_modtype mtb.typ_mp mtb env
  in
    List.fold_left add_one env sign

and add_module mb env = 
  let mp = mb.mod_mp in
  let env = Environ.shallow_add_module mp mb env in
    match mb.mod_type with
      | SEBstruct (sign) -> 
	  add_retroknowledge mb.mod_retroknowledge
	    (add_signature mp sign mb.mod_delta env)
      | SEBfunctor _ -> env
      | _ -> anomaly "Modops:the evaluation of the structure failed "

let strengthen_const env mp_from l cb resolver = 
  match cb.const_body with
  | Def _ -> cb
  | _ ->
      let con = make_con mp_from empty_dirpath l in
      let con =  constant_of_delta resolver con in
      let const = mkConst con in 
      let const_subs = Def (Declarations.from_val const) in
      { cb with 
	const_body = const_subs;
	const_body_code = Cemitcodes.from_val
	  (compile_constant_body env const_subs false);
	const_inline_code = false
      }
	  

let rec strengthen_mod env mp_from mp_to mb = 
  if mp_in_delta mb.mod_mp mb.mod_delta then
    mb 
  else
    match mb.mod_type with
     | SEBstruct (sign) -> 
	 let resolve_out,sign_out = 
	   strengthen_sig env mp_from sign mp_to mb.mod_delta in
	   { mb with
	       mod_expr = Some (SEBident mp_to);
	       mod_type = SEBstruct(sign_out);
	       mod_type_alg = mb.mod_type_alg;
	       mod_constraints = mb.mod_constraints;
	       mod_delta = add_mp_delta_resolver mp_from mp_to 
	       (add_delta_resolver mb.mod_delta resolve_out) }
     | SEBfunctor _ -> mb
     | _ -> anomaly "Modops:the evaluation of the structure failed "
	 
and strengthen_sig env mp_from sign mp_to resolver =
  match sign with
    | [] -> empty_delta_resolver,[]
    | (l,SFBconst cb) :: rest ->
	let item' = 
	  l,SFBconst (strengthen_const env mp_from l cb resolver) in
	let resolve_out,rest' =
	  strengthen_sig env mp_from rest mp_to resolver in
	  resolve_out,item'::rest'
    | (_,SFBmind _ as item):: rest ->
	let resolve_out,rest' = 
	  strengthen_sig env mp_from rest mp_to resolver in
	  resolve_out,item::rest'
    | (l,SFBmodule mb) :: rest ->
	let mp_from' = MPdot (mp_from,l) in
	let mp_to' = MPdot(mp_to,l) in 
	let mb_out = 
	  strengthen_mod env mp_from' mp_to' mb in
	let item' = l,SFBmodule (mb_out) in
	let env' = add_module mb_out env in
	let resolve_out,rest' = 
	  strengthen_sig env' mp_from rest mp_to resolver in
	  add_delta_resolver resolve_out mb.mod_delta,
	item':: rest'
    | (l,SFBmodtype mty as item) :: rest -> 
	let env' = add_modtype 
	  (MPdot(mp_from,l)) mty env
	in
	let resolve_out,rest' = 
	  strengthen_sig env' mp_from rest mp_to resolver in
	  resolve_out,item::rest'
    
let strengthen env mtb mp = 
  if mp_in_delta mtb.typ_mp mtb.typ_delta then
    (* in this case mtb has already been strengthened*)
    mtb 
  else
    match mtb.typ_expr with
      | SEBstruct (sign) -> 
	  let resolve_out,sign_out =
	    strengthen_sig env mtb.typ_mp sign mp mtb.typ_delta in
	    {mtb with
	       typ_expr = SEBstruct(sign_out);
	       typ_delta = add_delta_resolver mtb.typ_delta
		(add_mp_delta_resolver mtb.typ_mp mp resolve_out)}
      | SEBfunctor _ -> mtb
      | _ -> anomaly "Modops:the evaluation of the structure failed "
	  
let module_type_of_module env mp mb =
  match mp with
      Some mp ->
	strengthen env {
	  typ_mp = mp;
	  typ_expr = mb.mod_type;
	  typ_expr_alg = None;
	  typ_constraints = mb.mod_constraints;
	  typ_delta = mb.mod_delta} mp
	  
    | None ->
	{typ_mp = mb.mod_mp;
	 typ_expr = mb.mod_type;
	 typ_expr_alg = None;
	 typ_constraints = mb.mod_constraints;
	 typ_delta = mb.mod_delta}

let complete_inline_delta_resolver env mp mbid mtb delta =
  let constants = inline_of_delta mtb.typ_delta in
  let rec make_inline delta = function
    | [] -> delta
    | kn::r -> 
	let kn = replace_mp_in_kn (MPbound mbid) mp kn in
	let con = constant_of_kn kn in
	let con' = constant_of_delta delta con in
	try
	  let constant = lookup_constant con' env in
	  match constant.Declarations.const_body with
	  | Def csubst ->
	      let constr =  Declarations.force csubst in
	      add_inline_constr_delta_resolver con constr (make_inline delta r)
	  | _ -> make_inline delta r
	with 
	  Not_found -> error_no_such_label_sub (con_label con) 
	      (string_of_mp (con_modpath con))
  in
  make_inline delta constants

let rec strengthen_and_subst_mod
    mb subst env mp_from mp_to env resolver =
     match mb.mod_type with
	 SEBstruct(str) ->
	   let mb_is_an_alias = mp_in_delta mb.mod_mp mb.mod_delta in
	   if mb_is_an_alias then 
	     subst_module subst 
	       (fun resolver subst-> subst_dom_delta_resolver subst resolver) mb 
	   else
	     let resolver,new_sig = 
	       strengthen_and_subst_struct str subst env
		 mp_from mp_from mp_to false false mb.mod_delta 
	     in
	       {mb with 
		  mod_mp = mp_to;
		  mod_expr = Some (SEBident mp_from);
		  mod_type = SEBstruct(new_sig);
		  mod_delta = add_mp_delta_resolver mp_to mp_from resolver}
       | SEBfunctor(arg_id,arg_b,body) ->
	   let subst = add_mp mb.mod_mp mp_to empty_delta_resolver subst in
	   subst_module subst 
	     (fun resolver subst-> subst_dom_codom_delta_resolver subst resolver) mb  
	
       | _ -> anomaly "Modops:the evaluation of the structure failed "
	   
and strengthen_and_subst_struct 
    str subst env mp_alias mp_from mp_to alias incl resolver =
  match str with
    | [] -> empty_delta_resolver,[]
    | (l,SFBconst cb) :: rest ->
	let item' = if alias then 
	  (* case alias no strengthening needed*)
	  l,SFBconst (subst_const_body subst cb) 
	else 
	  l,SFBconst (strengthen_const env mp_from l 
			(subst_const_body subst cb) resolver)
	in
	let con = make_con mp_from empty_dirpath l in
	let resolve_out,rest' =
	  strengthen_and_subst_struct rest subst env 
	    mp_alias mp_from mp_to alias incl resolver in
	  if incl then
	    (* If we are performing an inclusion we need to add
	       the fact that the constant mp_to.l is \Delta-equivalent
	       to resolver(mp_from.l) *)
	    let old_name = constant_of_delta resolver con in
	    (add_constant_delta_resolver
	      (constant_of_kn_equiv (make_kn mp_to empty_dirpath l) (canonical_con old_name)) 
	      resolve_out),
	item'::rest'
	  else
	    (*In this case the fact that the constant mp_to.l is 
	      \Delta-equivalent to resolver(mp_from.l) is already known
	       because resolve_out contains mp_to maps to resolver(mp_from)*)
	    resolve_out,item'::rest'
    | (l,SFBmind mib) :: rest ->
	(*Same as constant*)
	let item' = l,SFBmind (subst_mind subst mib) in
	let mind = make_mind mp_from empty_dirpath l in
	let resolve_out,rest' =
	  strengthen_and_subst_struct rest subst env 
	    mp_alias mp_from mp_to alias incl resolver in
	  if incl then
	    let old_name =  mind_of_delta resolver mind in 
	    (add_mind_delta_resolver
	      (mind_of_kn_equiv (make_kn mp_to empty_dirpath l) (canonical_mind old_name)) resolve_out),
	item'::rest'
	  else
	    resolve_out,item'::rest'
    | (l,SFBmodule mb) :: rest ->
	let mp_from' = MPdot (mp_from,l) in
	let mp_to' = MPdot(mp_to,l) in
	let mb_out = if alias then 
	  subst_module subst 
	  (fun resolver subst -> subst_dom_delta_resolver subst resolver) mb 
	else
	  strengthen_and_subst_mod
	    mb subst env mp_from' mp_to' env resolver
	in
	let item' = l,SFBmodule (mb_out) in
	let env' = add_module mb_out env in
	let resolve_out,rest' = 
	  strengthen_and_subst_struct rest subst env' 
	    mp_alias mp_from mp_to alias incl resolver in
	  (* if mb is a functor we should not derive new equivalences
	     on names, hence we add the fact that the functor can only
	     be equivalent to itself. If we adopt an applicative
	     semantic for functor this should be changed.*)
	  if is_functor mb_out.mod_type then 
	    (add_mp_delta_resolver 
	       mp_to' mp_to' resolve_out),item':: rest' 
	  else
	    add_delta_resolver resolve_out mb_out.mod_delta,
	item':: rest'
    | (l,SFBmodtype mty) :: rest -> 
	let mp_from' = MPdot (mp_from,l) in
	let mp_to' = MPdot(mp_to,l) in
	let subst' = add_mp mp_from' mp_to' empty_delta_resolver subst in
	let mty = subst_modtype subst' 
	  (fun resolver subst -> subst_dom_codom_delta_resolver subst' resolver) mty in
	let env' = add_modtype mp_from' mty env	in
	let resolve_out,rest' = strengthen_and_subst_struct rest subst env' 
	    mp_alias mp_from mp_to alias incl resolver in
	  (add_mp_delta_resolver 
	     mp_to' mp_to' resolve_out),(l,SFBmodtype mty)::rest'
    

(* Let P be a module path when we write "Module M:=P." or "Module M. Include P. End M."
   we need to perform two operations to compute the body of M. The first one is applying
   the substitution {P <- M} on the type of P and the second one is strenghtening. *)
let strengthen_and_subst_mb mb mp env include_b =
    match mb.mod_type with
	SEBstruct str ->
	  let mb_is_an_alias = mp_in_delta mb.mod_mp mb.mod_delta in
	    (*if mb.mod_mp is an alias then the strengthening is useless 
	      (i.e. it is already done)*)
	  let mp_alias = delta_of_mp mb.mod_delta mb.mod_mp in
	  let subst_resolver = map_mp mb.mod_mp mp empty_delta_resolver in
	  let new_resolver = 
	    add_mp_delta_resolver mp mp_alias
	      (subst_dom_delta_resolver subst_resolver mb.mod_delta) in
	  let subst = map_mp mb.mod_mp mp new_resolver in 
	  let resolver_out,new_sig = 
	    strengthen_and_subst_struct str subst env
	     mp_alias mb.mod_mp mp mb_is_an_alias include_b mb.mod_delta 
	  in
	    {mb with 
	       mod_mp = mp;
	       mod_type = SEBstruct(new_sig);
	       mod_expr = Some (SEBident mb.mod_mp);
	       mod_delta = if include_b then resolver_out 
	       else add_delta_resolver new_resolver resolver_out}
      | SEBfunctor(arg_id,argb,body) ->
	  let subst = map_mp mb.mod_mp mp empty_delta_resolver in
	  subst_module subst 
	    (fun resolver subst -> subst_dom_codom_delta_resolver subst resolver) mb 
      | _ -> anomaly "Modops:the evaluation of the structure failed "


let subst_modtype_and_resolver mtb mp env =
  let subst = (map_mp mtb.typ_mp mp empty_delta_resolver) in
  let new_delta = subst_dom_codom_delta_resolver subst mtb.typ_delta in 
  let full_subst = (map_mp mtb.typ_mp mp new_delta) in
    subst_modtype full_subst
      (fun resolver subst -> subst_dom_codom_delta_resolver subst resolver) mtb

let rec is_bounded_expr l = function
  | SEBident mp -> List.mem mp l
  | SEBapply (fexpr,mexpr,_) ->  
      is_bounded_expr l mexpr || is_bounded_expr l fexpr
  | _ -> false

let rec clean_struct l = function
  | (lab,SFBmodule mb) as field -> 
      let clean_typ = clean_expr l mb.mod_type in 
      let clean_impl = 
	begin try
	  if (is_bounded_expr l (Option.get mb.mod_expr)) then
	    Some clean_typ
	  else  Some (clean_expr l (Option.get mb.mod_expr))
	with
	    Option.IsNone -> None 
	end in
	  if clean_typ==mb.mod_type && clean_impl==mb.mod_expr then
	    field 
	  else 
	    (lab,SFBmodule {mb with 
			      mod_type=clean_typ;
			      mod_expr=clean_impl})
  | field -> field
      
and clean_expr l = function
 | SEBfunctor (mbid,sigt,str) as s->
     let str_clean = clean_expr l str in
     let sig_clean = clean_expr l sigt.typ_expr in 
       if  str_clean == str && sig_clean = sigt.typ_expr then
	 s else SEBfunctor (mbid,{sigt with typ_expr=sig_clean},str_clean)
  | SEBstruct str as s->
      let str_clean = Util.list_smartmap (clean_struct l) str in 
	if  str_clean == str then s else SEBstruct(str_clean)
  |  str -> str 

let rec collect_mbid l = function
  | SEBfunctor (mbid,sigt,str) as s->
      let str_clean = collect_mbid ((MPbound mbid)::l) str in 
	if  str_clean == str then s else 
      SEBfunctor (mbid,sigt,str_clean)
  | SEBstruct str as s->
      let str_clean = Util.list_smartmap (clean_struct l) str in 
	if  str_clean == str then s else SEBstruct(str_clean)
  |  _ -> anomaly "Modops:the evaluation of the structure failed "
       
       
let clean_bounded_mod_expr = function
  | SEBfunctor _ as str -> 
      let str_clean = collect_mbid [] str in 
	if  str_clean == str then str else str_clean
  | str -> str
