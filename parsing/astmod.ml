(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Pp
open Util
open Identifier
open Names
open Mod_declarations
open Libnames
open Coqast
open Astterm
 
let ident_of_nvar = function
    Nvar(_,s) -> s
  | _ -> anomaly "ident_of_var: Nvar expected"

(* Since module components are not put in the nametab we try to locate
the module prefix *)
exception BadRef

let lookup_qualid (modtype:bool) qid = 
  let rec make_mp mp = function
      [] -> mp
    | h::tl -> make_mp (MPdot(mp, label_of_ident h)) tl
  in
  let rec find_module_prefix dir n =
    if n<0 then raise Not_found;
    let dir',dir'' = list_chop n dir in
    let id',dir''' = 
      match dir'' with 
	| hd::tl -> hd,tl 
	| _ -> anomaly "This list should not be empty!"
    in
    let qid' = make_qualid dir' id' in
      try 
	match Nametab.locate qid' with
	  | ModRef mp -> mp,dir'''
	  | _ -> raise BadRef
      with
	  Not_found -> find_module_prefix dir (pred n)
  in
    try Nametab.locate qid
    with Not_found -> 
      let (dir,id) = repr_qualid qid in
      let pref_mp,dir' = find_module_prefix dir (List.length dir - 1) in
      let mp = 
	List.fold_left (fun mp id -> MPdot (mp, label_of_ident id)) pref_mp dir' 
      in
	if modtype then
	  ModTypeRef (make_ln mp (label_of_ident id))
	else
	  ModRef (MPdot (mp,label_of_ident id))
	    
let transl_modtype = function 
    | Node(loc,"MODTQUALID",astl) -> 
	let qid = interp_qualid astl in
	  (try 
	     match lookup_qualid true qid with
	       | ModTypeRef ln -> MTEident ln
	       | _ -> Modops.error_not_a_modtype (string_of_qualid qid)
           with
	       BadRef -> Modops.error_not_a_modtype (string_of_qualid qid)
	     | Not_found -> Nametab.error_global_not_found_loc loc qid)
    | _ -> anomaly "TODO: transl_modtype: I can handle qualid module types only"  

 
let transl_binder (idl,mty_ast) =
      let mte = transl_modtype mty_ast in
      let add_one id = 
	let mbid = mbid_of_ident id in
	  Nametab.push (make_path [] id CCI) (ModRef(MPbid mbid));
	  (mbid,mte)
      in
	List.map add_one idl


let transl_binders astl = 
  list_map_append transl_binder astl


let rec transl_modexpr = function 
  | Node(loc,"MODEXPRQID",astl) -> 
      let qid = interp_qualid astl in
	(try 
	   match lookup_qualid true qid with
	     | ModRef mp -> MEident mp
	     | _ -> Modops.error_not_a_module (string_of_qualid qid)
	 with
	     BadRef -> Modops.error_not_a_module (string_of_qualid qid)
	   | Not_found -> Nametab.error_global_not_found_loc loc qid)
  | Node(_,"MODEXPRAPP",[ast1;ast2]) ->
      let me1 = transl_modexpr ast1 in
      let me2 = transl_modexpr ast2 in
	MEapply(me1,me2)
  | Node(_,"MODEXPRAPP",_) -> 
      anomaly "transl_modexpr: MODEXPRAPP must have two arguments"
  | _ -> anomaly "transl_modexpr: I can handle MODEXPRQID or MODEXPRAPP only..."


let interp_modexpr evd env astl ast_opt = 
  let nametab = Nametab.freeze () in   (* boueeeeee *)
  let args = transl_binders astl in
  let me_opt = option_app transl_modexpr ast_opt in
    Nametab.unfreeze nametab;
    (args,me_opt)


(* oversimplified versions for non-dependant things *)

let interp_modbinders evd env astl = 
  let interp_binder (idl, mty_ast) =
    let mte = transl_modtype mty_ast in
      List.map (fun id -> mbid_of_ident id, mte) idl
  in
    list_map_append interp_binder astl


let interp_modtype evd env astl ast = 
  (interp_modbinders evd env astl, transl_modtype ast)
