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
open Names
open Entries
open Libnames
open Coqast
open Astterm
 
let rec make_mp mp = function
    [] -> mp
  | h::tl -> make_mp (MPdot(mp, label_of_id h)) tl

(*
(* Since module components are not put in the nametab we try to locate
the module prefix *)
exception BadRef

let lookup_qualid (modtype:bool) qid = 
  let rec make_mp mp = function
      [] -> mp
    | h::tl -> make_mp (MPdot(mp, label_of_id h)) tl
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
	List.fold_left (fun mp id -> MPdot (mp, label_of_id id)) pref_mp dir' 
      in
	if modtype then
	  ModTypeRef (make_ln mp (label_of_id id))
	else
	  ModRef (MPdot (mp,label_of_id id))

*)

(* Search for the head of [qid] in [binders]. 
   If found, returns the module_path/kernel_name created from the dirpath
   and the basename. Searches Nametab otherwise.
*)

let lookup_module binders qid =
  try
    let dir,id = repr_qualid qid in
      (* dirpath in natural order *)
    let idl = List.rev (id::repr_dirpath dir) in
    let top_mp = MPbound (fst (List.assoc (List.hd idl) binders)) in
      make_mp top_mp (List.tl idl)
  with 
      Not_found -> Nametab.locate_module qid
	
let lookup_modtype binders qid =
  try
    let dir,id = repr_qualid qid in
      (* dirpath in natural order *)
    match List.rev (repr_dirpath dir) with
      | hd::tl ->
	  let top_mp = MPbound (fst (List.assoc hd binders)) in
	  let mp = make_mp top_mp tl in
	    make_kn mp empty_dirpath (label_of_id id)
      | [] -> raise Not_found 
	  (* may-be a module, but not a module type!*)
  with
      Not_found -> Nametab.locate_modtype qid

let transl_with_decl binders = function 
  | Node(loc,"WITHMODULE",[id_ast;qid_ast]) ->
      let id = match id_ast with
	  Nvar(_,id) -> id
	| _ -> anomaly "Identifier AST expected"
      in
      let qid = match qid_ast with
	| Node (loc, "QUALID", astl) -> 
  	    interp_qualid astl
	| _ -> anomaly "QUALID expected"
      in
	With_Module (id,lookup_module binders qid)
  | Node(loc,"WITHDEFINITION",[id_ast;cast]) ->
      let id = match id_ast with
	  Nvar(_,id) -> id
	| _ -> anomaly "Identifier AST expected"
      in
      let c = interp_constr Evd.empty (Global.env()) cast in
	With_Definition (id,c)
  | _ -> anomaly "Unexpected AST"

let rec transl_modtype binders = function 
  | Node(loc,"MODTYPEQID",qid_ast) -> begin match qid_ast with 
      | [Node (loc, "QUALID", astl)] -> 
  	  let qid = interp_qualid astl in begin
	      try 
	        MTEident (lookup_modtype binders qid)
	      with
	        | Not_found -> 
		    Modops.error_not_a_modtype (*loc*) (string_of_qualid qid)
	    end
      | _ -> anomaly "QUALID expected"
    end
  | Node(loc,"MODTYPEWITH",[mty_ast;decl_ast]) ->
      let mty = transl_modtype binders mty_ast in
      let decl = transl_with_decl binders decl_ast in
	MTEwith(mty,decl)
  | _ -> anomaly "TODO: transl_modtype: I can handle qualid module types only"
 

let transl_binder binders (idl,mty_ast) =
  let mte = transl_modtype binders mty_ast in
  let add_one binders id = 
    if List.mem_assoc id binders then
      error "Two identical module binders..."
    else
      let mbid = make_mbid (Lib.module_dp()) (string_of_id id) in
	(id,(mbid,mte))::binders
  in
    List.fold_left add_one binders idl 

let transl_binders = List.fold_left transl_binder


let rec transl_modexpr binders = function 
  | Node(loc,"MODEXPRQID",qid_ast) -> begin match qid_ast with 
      | [Node (loc, "QUALID", astl)] -> 
	  let qid = interp_qualid astl in begin
	    try 
	      MEident (lookup_module binders qid)
	    with
	      | Not_found -> 
		 Modops.error_not_a_module (*loc*) (string_of_qualid qid)
	  end
      | _ -> anomaly "QUALID expected"
    end
  | Node(_,"MODEXPRAPP",[ast1;ast2]) ->
      let me1 = transl_modexpr binders ast1 in
      let me2 = transl_modexpr binders ast2 in
	MEapply(me1,me2)
  | Node(_,"MODEXPRAPP",_) -> 
      anomaly "transl_modexpr: MODEXPRAPP must have two arguments"
  | _ -> anomaly "transl_modexpr: I can handle MODEXPRQID or MODEXPRAPP only..."


let interp_module_decl evd env args_ast mty_ast_o mexpr_ast_o = 
  let binders = transl_binders [] args_ast in
  let mty_o = option_app (transl_modtype binders) mty_ast_o in
  let mexpr_o = option_app (transl_modexpr binders) mexpr_ast_o in
    (List.rev binders, mty_o, mexpr_o)

