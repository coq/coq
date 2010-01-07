(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Pp
open Util
open Names
open Entries
open Libnames
open Topconstr
open Constrintern

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
let lookup_module (loc,qid) =
  try
    let mp = Nametab.locate_module qid in
      Dumpglob.dump_modref loc mp "modtype"; mp
  with
    | Not_found -> Modops.error_not_a_module_loc loc (string_of_qualid qid)

let lookup_modtype (loc,qid) =
  try
    let mp = Nametab.locate_modtype qid in
      Dumpglob.dump_modref loc mp "mod"; mp
  with
    | Not_found ->
	Modops.error_not_a_modtype_loc loc (string_of_qualid qid)

let lookup_module_or_modtype (loc,qid) =
  try
    let mp = Nametab.locate_module qid in
    Dumpglob.dump_modref loc mp "modtype"; (mp,true)
  with Not_found -> try
    let mp = Nametab.locate_modtype qid in
    Dumpglob.dump_modref loc mp "mod"; (mp,false)
  with Not_found ->
    Modops.error_not_a_module_or_modtype_loc loc (string_of_qualid qid)

let transl_with_decl env = function
  | CWith_Module ((_,fqid),qid) ->
      With_Module (fqid,lookup_module qid)
  | CWith_Definition ((_,fqid),c) ->
      With_Definition (fqid,interp_constr Evd.empty env c)

let rec interp_modexpr env = function
  | CMident qid ->
      MSEident (lookup_module qid)
  | CMapply (me1,me2) ->
      let me1 = interp_modexpr env me1 in
      let me2 = interp_modexpr env me2 in
	MSEapply(me1,me2)
  | CMwith _ -> Modops.error_with_in_module ()


let rec interp_modtype env = function
  | CMident qid ->
      MSEident (lookup_modtype qid)
  | CMapply (mty1,me) ->
      let mty' = interp_modtype env mty1 in
      let me' = interp_modexpr env me in
	MSEapply(mty',me')
  | CMwith (mty,decl) ->
      let mty = interp_modtype env mty in
      let decl = transl_with_decl env decl in
	MSEwith(mty,decl)

let rec interp_modexpr_or_modtype env = function
  | CMident qid ->
      let (mp,ismod) = lookup_module_or_modtype qid in
      (MSEident mp, ismod)
  | CMapply (me1,me2) ->
      let me1,ismod1 = interp_modexpr_or_modtype env me1 in
      let me2,ismod2 = interp_modexpr_or_modtype env me2 in
      if not ismod2 then Modops.error_application_to_module_type ();
      (MSEapply (me1,me2), ismod1)
  | CMwith (me,decl) ->
      let me,ismod = interp_modexpr_or_modtype env me in
      let decl = transl_with_decl env decl in
      if ismod then Modops.error_with_in_module ();
      (MSEwith(me,decl), ismod)
