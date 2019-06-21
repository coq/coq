(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This module registers tables for some non-logical informations
     associated declarations *)

open Names
open Decl_kinds
open Libnames

(** Datas associated to section variables and local definitions *)

type variable_data = {
  path:DirPath.t;
  opaque:bool;
  univs:Univ.ContextSet.t;
  poly:bool;
  kind:logical_kind;
}

let vartab =
  Summary.ref (Id.Map.empty : variable_data Id.Map.t) ~name:"VARIABLE"

let add_variable_data id o = vartab := Id.Map.add id o !vartab

let variable_path id = let {path} = Id.Map.find id !vartab in path
let variable_opacity id = let {opaque} = Id.Map.find id !vartab in opaque
let variable_kind id = let {kind} = Id.Map.find id !vartab in kind
let variable_context id = let {univs} = Id.Map.find id !vartab in univs
let variable_polymorphic id = let {poly} = Id.Map.find id !vartab in poly

let variable_secpath id =
  let dir = drop_dirpath_prefix (Lib.library_dp()) (variable_path id) in
  make_qualid dir id

let variable_exists id = Id.Map.mem id !vartab

(** Datas associated to global parameters and constants *)

let csttab = Summary.ref (Cmap.empty : logical_kind Cmap.t) ~name:"CONSTANT"

let add_constant_kind kn k = csttab := Cmap.add kn k !csttab

let constant_kind kn = Cmap.find kn !csttab
