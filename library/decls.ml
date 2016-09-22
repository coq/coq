(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** This module registers tables for some non-logical informations
     associated declarations *)

open Util
open Names
open Decl_kinds
open Libnames

module NamedDecl = Context.Named.Declaration

(** Datas associated to section variables and local definitions *)

type variable_data =
  { dir_path : DirPath.t;
    opaque : bool;
    universe_context_set : Univ.universe_context_set;
    polymorphic : bool;
    kind : logical_kind }

let vartab =
  Summary.ref (Id.Map.empty : variable_data Id.Map.t) ~name:"VARIABLE"

let add_variable_data id o = vartab := Id.Map.add id o !vartab

let variable_path id = (Id.Map.find id !vartab).dir_path
let variable_opacity id = (Id.Map.find id !vartab).opaque
let variable_kind id = (Id.Map.find id !vartab).kind
let variable_context id = (Id.Map.find id !vartab).universe_context_set
let variable_polymorphic id = (Id.Map.find id !vartab).polymorphic

let variable_secpath id =
  let dir = drop_dirpath_prefix (Lib.library_dp()) (variable_path id) in
  make_qualid dir id

let variable_exists id = Id.Map.mem id !vartab

(** Datas associated to global parameters and constants *)

let csttab = Summary.ref (Cmap.empty : logical_kind Cmap.t) ~name:"CONSTANT"

let add_constant_kind kn k = csttab := Cmap.add kn k !csttab

let constant_kind kn = Cmap.find kn !csttab

(** Miscellaneous functions. *)

let initialize_named_context_for_proof () =
  let sign = Global.named_context () in
  List.fold_right
    (fun d signv ->
      let id = NamedDecl.get_id d in
      let d = if variable_opacity id then NamedDecl.LocalAssum (id, NamedDecl.get_type d) else d in
      Environ.push_named_context_val d signv) sign Environ.empty_named_context_val

let last_section_hyps dir =
  Context.Named.fold_outside
    (fun d sec_ids ->
      let id = NamedDecl.get_id d in
      try if DirPath.equal dir (variable_path id) then id::sec_ids else sec_ids
      with Not_found -> sec_ids)
    (Environ.named_context (Global.env()))
    ~init:[]
