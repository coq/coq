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
  DirPath.t * bool (* opacity *) * logical_kind

let vartab =
  Summary.ref (Id.Map.empty : variable_data Id.Map.t) ~name:"VARIABLE"

let add_variable_data id o = vartab := Id.Map.add id o !vartab

let variable_path id = let (p,_,_) = Id.Map.find id !vartab in p
let variable_opacity id = let (_,opaq,_) = Id.Map.find id !vartab in opaq
let variable_kind id = let (_,_,k) = Id.Map.find id !vartab in k

let variable_secpath id =
  let dir = drop_dirpath_prefix (Lib.library_dp()) (variable_path id) in
  make_qualid dir id

let variable_exists id = Id.Map.mem id !vartab

(** Datas associated to global parameters and constants *)

let csttab = Summary.ref (Cmap.empty : logical_kind Cmap.t) ~name:"CONSTANT"

let add_constant_kind kn k = csttab := Cmap.add kn k !csttab

let constant_kind kn = Cmap.find kn !csttab

let polytab = Summary.ref (Cmap.empty,Mindmap.empty) ~name:"polytab"

type poly_obj = PConst of Constant.t | PMind of MutInd.t

let poly_cache (_,(who,p)) = match who with
  | PConst c -> polytab := Util.on_fst (Cmap.add c p) !polytab
  | PMind m -> polytab := Util.on_snd (Mindmap.add m p) !polytab

let poly_subst (subst, (who, p)) =
  let who = match who with
    | PConst c -> PConst (Mod_subst.subst_constant subst c)
    | PMind m -> PMind (Mod_subst.subst_mind subst m)
  in
  (who, p)

let poly_obj = let open Libobject in
  declare_object
    (superglobal_object "polymorphism register"
       ~cache:poly_cache ~subst:(Some poly_subst) ~discharge:(fun (_,x) -> Some x))

let register_poly_const c p = Lib.add_anonymous_leaf (poly_obj (PConst c, p))

let register_poly_mind m p = Lib.add_anonymous_leaf (poly_obj (PMind m, p))

let is_polymorphic = let open GlobRef in function
  | VarRef _ -> false
  | ConstRef c -> Cmap.find c (fst !polytab)
  | IndRef (m,_) | ConstructRef ((m,_),_) -> Mindmap.find m (snd !polytab)

let mind_is_polymorphic mind = is_polymorphic (GlobRef.IndRef (mind,0))
