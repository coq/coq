(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** This module registers tables for some non-logical informations
     associated declarations *)

open Names
open Term
open Sign
open Decl_kinds
open Libnames

(** Datas associated to section variables and local definitions *)

type variable_data =
    dir_path * bool (* opacity *) * Univ.constraints * logical_kind

let vartab = ref (Idmap.empty : variable_data Idmap.t)

let _ = Summary.declare_summary "VARIABLE"
  { Summary.freeze_function = (fun () -> !vartab);
    Summary.unfreeze_function = (fun ft -> vartab := ft);
    Summary.init_function = (fun () -> vartab := Idmap.empty) }

let add_variable_data id o = vartab := Idmap.add id o !vartab

let variable_path id = let (p,_,_,_) = Idmap.find id !vartab in p
let variable_opacity id = let (_,opaq,_,_) = Idmap.find id !vartab in opaq
let variable_kind id = let (_,_,_,k) = Idmap.find id !vartab in k
let variable_constraints id = let (_,_,cst,_) = Idmap.find id !vartab in cst

let variable_secpath id =
  let dir = drop_dirpath_prefix (Lib.library_dp()) (variable_path id) in
  make_qualid dir id

let variable_exists id = Idmap.mem id !vartab

(** Datas associated to global parameters and constants *)

let csttab = ref (Cmap.empty : logical_kind Cmap.t)

let _ = Summary.declare_summary "CONSTANT"
	  { Summary.freeze_function = (fun () -> !csttab);
	    Summary.unfreeze_function = (fun ft -> csttab := ft);
	    Summary.init_function = (fun () -> csttab := Cmap.empty) }

let add_constant_kind kn k = csttab := Cmap.add kn k !csttab

let constant_kind kn = Cmap.find kn !csttab

(** Miscellaneous functions. *)

let clear_proofs sign =
  List.fold_right
    (fun (id,c,t as d) signv ->
      let d = if variable_opacity id then (id,None,t) else d in
      Environ.push_named_context_val d signv) sign Environ.empty_named_context_val

let last_section_hyps dir =
  fold_named_context
    (fun (id,_,_) sec_ids ->
      try if dir=variable_path id then id::sec_ids else sec_ids
      with Not_found -> sec_ids)
    (Environ.named_context (Global.env()))
    ~init:[]
