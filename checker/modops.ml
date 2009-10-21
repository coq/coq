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

let error_no_such_label_sub l l1 =
  let l1 = string_of_mp l1 in
  error ("The field "^
         string_of_label l^" is missing in "^l1^".")

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
    mod_retroknowledge = []}

let check_modpath_equiv env mp1 mp2 = 
  if mp1=mp2 then () else
 (*   let mb1=lookup_module  mp1 env in
    let mb2=lookup_module mp2 env in
      if (delta_of_mp mb1.mod_delta mp1)=(delta_of_mp mb2.mod_delta mp2)
      then ()
      else*) error_not_equal mp1 mp2

let rec add_signature mp sign resolver env = 
  let add_one env (l,elem) =
    let kn = make_kn mp empty_dirpath l in
    let con = constant_of_kn kn in
    let mind = mind_of_kn kn in
      match elem with
	| SFBconst cb -> 
	   (* let con =  constant_of_delta resolver con in*)
	      Environ.add_constant con cb env
	| SFBmind mib -> 
	   (* let mind =  mind_of_delta resolver mind in*)
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
	    add_signature mp sign mb.mod_delta env
      | SEBfunctor _ -> env
      | _ -> anomaly "Modops:the evaluation of the structure failed "


let strengthen_const env mp_from l cb resolver = 
  match cb.const_opaque, cb.const_body with
  | false, Some _ -> cb
  | true, Some _ 
  | _, None ->
      let con = make_con mp_from empty_dirpath l in
     (* let con =  constant_of_delta resolver con in*)
      let const = Const con in 
      let const_subs = Some (Declarations.from_val const) in
	{cb with 
	   const_body = const_subs;
	   const_opaque = false;
	}
	  

let rec strengthen_mod env mp_from mp_to mb = 
  assert(mp_from = mb.mod_mp);
(*  if mp_in_delta mb.mod_mp mb.mod_delta then
    mb 
  else*)
    match mb.mod_type with
     | SEBstruct (sign) -> 
	 let resolve_out,sign_out = 
	   strengthen_sig env mp_from sign mp_to mb.mod_delta in
	   { mb with
	       mod_expr = Some (SEBident mp_to);
	       mod_type = SEBstruct(sign_out);
	       mod_type_alg = mb.mod_type_alg;
	       mod_constraints = mb.mod_constraints;
	       mod_delta = resolve_out(*add_mp_delta_resolver mp_from mp_to 
	       (add_delta_resolver mb.mod_delta resolve_out)*);
	       mod_retroknowledge = mb.mod_retroknowledge}
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
	  resolve_out
	  (*add_delta_resolver resolve_out mb.mod_delta*),
	item':: rest'
    | (l,SFBmodtype mty as item) :: rest -> 
	let env' = add_modtype 
	  (MPdot(mp_from,l)) mty env
	in
	let resolve_out,rest' = 
	  strengthen_sig env' mp_from rest mp_to resolver in
	  resolve_out,item::rest'
    
let strengthen env mtb mp = 
(*  if mp_in_delta mtb.typ_mp mtb.typ_delta then
    (* in this case mtb has already been strengthened*)
    mtb 
  else*)
    match mtb.typ_expr with
      | SEBstruct (sign) -> 
	  let resolve_out,sign_out =
	    strengthen_sig env mtb.typ_mp sign mp mtb.typ_delta in
	    {mtb with
	       typ_expr = SEBstruct(sign_out);
	       typ_delta = resolve_out(*add_delta_resolver mtb.typ_delta
		(add_mp_delta_resolver mtb.typ_mp mp resolve_out)*)}
      | SEBfunctor _ -> mtb
      | _ -> anomaly "Modops:the evaluation of the structure failed "

let subst_and_strengthen mb mp env =
  strengthen_mod env mb.mod_mp mp 
    (subst_module (map_mp mb.mod_mp mp) mb)


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
