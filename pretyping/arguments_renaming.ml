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
open Names
open Globnames
open Term
open Constr
open Environ
open Util
open Libobject

module NamedDecl = Context.Named.Declaration
(*i*)

let name_table =
  Summary.ref (Refmap.empty : Name.t list Refmap.t)
    ~name:"rename-arguments"

type req =
  | ReqLocal
  | ReqGlobal of GlobRef.t * Name.t list

let load_rename_args _ (_, (_, (r, names))) =
  name_table := Refmap.add r names !name_table

let cache_rename_args o = load_rename_args 1 o

let classify_rename_args = function
  | ReqLocal, _ -> Dispose
  | ReqGlobal _, _ as o -> Substitute o

let subst_rename_args (subst, (_, (r, names as orig))) = 
  ReqLocal,
  let r' = fst (subst_global subst r) in 
  if r==r' then orig else (r', names)

let discharge_rename_args = function
  | _, (ReqGlobal (c, names), _ as req) ->
     (try 
       let vars = Lib.variable_section_segment_of_reference c in
       let c' = pop_global_reference c in
       let var_names = List.map (fst %> NamedDecl.get_id %> Name.mk_name) vars in
       let names' = var_names @ names in
       Some (ReqGlobal (c', names), (c', names'))
     with Not_found -> Some req)
  | _ -> None

let rebuild_rename_args x = x

let inRenameArgs = declare_object { (default_object "RENAME-ARGUMENTS" ) with
  load_function = load_rename_args;
  cache_function = cache_rename_args;
  classify_function = classify_rename_args;
  subst_function = subst_rename_args;
  discharge_function = discharge_rename_args;
  rebuild_function = rebuild_rename_args;
}

let rename_arguments local r names =
  let req = if local then ReqLocal else ReqGlobal (r, names) in
  Lib.add_anonymous_leaf (inRenameArgs (req, (r, names)))       

let arguments_names r = Refmap.find r !name_table

let rec rename_prod c = function 
  | [] -> c
  | (Name _ as n) :: tl -> 
      (match kind_of_type c with
      | ProdType (_, s, t) -> mkProd (n, s, rename_prod t tl)
      | _ -> c)
  | _ :: tl -> 
      match kind_of_type c with
      | ProdType (n, s, t) -> mkProd (n, s, rename_prod t tl)
      | _ -> c
        
let rename_type ty ref =
  try rename_prod ty (arguments_names ref)
  with Not_found -> ty

let rename_type_of_constant env c =
  let ty = Typeops.type_of_constant_in env c in
  rename_type ty (ConstRef (fst c))

let rename_type_of_inductive env ind =
  let ty = Inductiveops.type_of_inductive env ind in
  rename_type ty (IndRef (fst ind))

let rename_type_of_constructor env cstruct =
  let ty = Inductiveops.type_of_constructor env cstruct in
  rename_type ty (ConstructRef (fst cstruct))

let rename_typing env c =
  let j = Typeops.infer env c in
  let j' =
    match kind c with
    | Const (c,u) -> { j with uj_type = rename_type j.uj_type (ConstRef c) }
    | Ind (i,u) -> { j with uj_type = rename_type j.uj_type (IndRef i) }
    | Construct (k,u) -> { j with uj_type = rename_type j.uj_type (ConstructRef k) }
    | _ -> j
  in j'

