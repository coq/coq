(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
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

type variable_data =
  DirPath.t * bool (* opacity *) * Univ.ContextSet.t * polymorphic * logical_kind

let vartab =
  Summary.ref (Id.Map.empty : variable_data Id.Map.t) ~name:"VARIABLE"

let add_variable_data id o = vartab := Id.Map.add id o !vartab

let variable_path id = let (p,_,_,_,_) = Id.Map.find id !vartab in p
let variable_opacity id = let (_,opaq,_,_,_) = Id.Map.find id !vartab in opaq
let variable_kind id = let (_,_,_,_,k) = Id.Map.find id !vartab in k
let variable_context id = let (_,_,ctx,_,_) = Id.Map.find id !vartab in ctx
let variable_polymorphic id = let (_,_,_,p,_) = Id.Map.find id !vartab in p

let variable_secpath id =
  let dir = drop_dirpath_prefix (Lib.library_dp()) (variable_path id) in
  make_qualid dir id

let variable_exists id = Id.Map.mem id !vartab

(** Datas associated to global parameters and constants *)

let csttab = Summary.ref (Cmap.empty : logical_kind Cmap.t) ~name:"CONSTANT"

let add_constant_kind kn k = csttab := Cmap.add kn k !csttab

let constant_kind kn = Cmap.find kn !csttab
