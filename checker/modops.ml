(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*i*)
open CErrors
open Util
open Pp
open Names
open Cic
open Declarations
(*i*)

let error_not_a_constant l =
  user_err Pp.(str ("\""^(Label.to_string l)^"\" is not a constant"))

let error_not_a_functor () = user_err Pp.(str "Application of not a functor")

let error_incompatible_modtypes _ _ = user_err Pp.(str "Incompatible module types")

let error_not_match l _ =
  user_err Pp.(str ("Signature components for label "^Label.to_string l^" do not match"))

let error_no_such_label l = user_err Pp.(str ("No such label "^Label.to_string l))

let error_no_such_label_sub l l1 =
  let l1 = ModPath.to_string l1 in
  user_err Pp.(str ("The field "^
         Label.to_string l^" is missing in "^l1^"."))

let error_not_a_module_loc ?loc s =
  user_err ?loc  (str ("\""^Label.to_string s^"\" is not a module"))

let error_not_a_module s = error_not_a_module_loc s

let error_with_module () =
  user_err Pp.(str "Unsupported 'with' constraint in module implementation")

let is_functor = function
  | MoreFunctor _ -> true
  | NoFunctor _ -> false

let destr_functor = function
  | MoreFunctor (arg_id,arg_t,body_t) -> (arg_id,arg_t,body_t)
  | NoFunctor _ -> error_not_a_functor ()

let module_body_of_type mp mtb =
  { mtb with mod_mp = mp; mod_expr = Abstract; mod_retroknowledge = ModBodyRK [] }

let rec add_structure mp sign resolver env =
  let add_one env (l,elem) =
    let kn = KerName.make2 mp l in
    let con = Constant.make1 kn in
    let mind = mind_of_delta resolver (MutInd.make1 kn) in
      match elem with
	| SFBconst cb ->
	   (* let con =  constant_of_delta resolver con in*)
	      Environ.add_constant con cb env
	| SFBmind mib ->
	   (* let mind =  mind_of_delta resolver mind in*)
	    Environ.add_mind mind mib env
	| SFBmodule mb -> add_module mb env
	      (* adds components as well *)
	| SFBmodtype mtb -> Environ.add_modtype mtb.mod_mp mtb env
  in
  List.fold_left add_one env sign

and add_module mb env =
  let mp = mb.mod_mp in
  let env = Environ.shallow_add_module mp mb env in
  match mb.mod_type with
  | NoFunctor struc -> add_structure mp struc mb.mod_delta env
  | MoreFunctor _ -> env

let add_module_type mp mtb env = add_module (module_body_of_type mp mtb) env

let strengthen_const mp_from l cb =
  match cb.const_body with
    | Def _ -> cb
    | _ ->
      let con = Constant.make2 mp_from l in
      let u =
        match cb.const_universes with
      | Monomorphic_const _ -> Univ.Instance.empty
      | Polymorphic_const auctx -> Univ.make_abstract_instance auctx
      in
      { cb with
	const_body = Def (Declarations.from_val (Const (con,u))) }

let rec strengthen_mod mp_from mp_to mb =
  if Declarations.mp_in_delta mb.mod_mp mb.mod_delta then mb
  else
    let mk_expr mp_to = Algebraic (NoFunctor (MEident mp_to)) in
    strengthen_body mk_expr mp_from mp_to mb

and strengthen_body : 'a. (_ -> 'a) -> _ -> _ -> 'a generic_module_body -> 'a generic_module_body =
  fun mk_expr mp_from mp_to mb ->
  match mb.mod_type with
  | MoreFunctor _ -> mb
  | NoFunctor sign ->
    let resolve_out,sign_out = strengthen_sig mp_from sign mp_to
    in
    { mb with
      mod_expr = mk_expr mp_to;
      mod_type = NoFunctor sign_out;
      mod_delta = resolve_out }

and strengthen_sig mp_from sign mp_to =
  match sign with
    | [] -> empty_delta_resolver,[]
    | (l,SFBconst cb) :: rest ->
        let item' = l,SFBconst (strengthen_const mp_from l cb) in
        let resolve_out,rest' = strengthen_sig mp_from rest mp_to in
	resolve_out,item'::rest'
    | (_,SFBmind _ as item):: rest ->
        let resolve_out,rest' = strengthen_sig mp_from rest mp_to in
	  resolve_out,item::rest'
    | (l,SFBmodule mb) :: rest ->
	let mp_from' = MPdot (mp_from,l) in
	let mp_to' = MPdot(mp_to,l) in
	let mb_out = strengthen_mod mp_from' mp_to' mb in
	let item' = l,SFBmodule (mb_out) in
        let resolve_out,rest' = strengthen_sig mp_from rest mp_to in
	resolve_out (*add_delta_resolver resolve_out mb.mod_delta*),
        item':: rest'
    | (_,SFBmodtype _ as item) :: rest ->
        let resolve_out,rest' = strengthen_sig mp_from rest mp_to in
        resolve_out,item::rest'

let strengthen mtb mp =
  strengthen_body ignore mtb.mod_mp mp mtb

let subst_and_strengthen mb mp =
  strengthen_mod mb.mod_mp mp (subst_module (map_mp mb.mod_mp mp) mb)

let module_type_of_module mp mb =
  let mtb =
    { mb with
      mod_expr = ();
      mod_type_alg = None;
      mod_retroknowledge = ModTypeRK }
  in
  match mp with
  | Some mp -> strengthen {mtb with mod_mp = mp} mp
  | None -> mtb
