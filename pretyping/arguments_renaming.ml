(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i*)
open Names
open Libnames
open Decl_kinds
open Term
open Sign
open Evd
open Environ
open Nametab
open Mod_subst
open Errors
open Util
open Pp
open Libobject
open Nameops
(*i*)

let empty_name_table = (Refmap.empty : name list list Refmap.t)
let name_table = ref empty_name_table

let _ =
  Summary.declare_summary "rename-arguments"
    { Summary.freeze_function = (fun () -> !name_table);
      Summary.unfreeze_function = (fun r -> name_table := r);
      Summary.init_function = (fun () -> name_table := empty_name_table) }

type req =
  | ReqLocal
  | ReqGlobal of global_reference * name list list

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

let section_segment_of_reference = function
  | ConstRef con -> Lib.section_segment_of_constant con
  | IndRef (kn,_) | ConstructRef ((kn,_),_) ->
      Lib.section_segment_of_mutual_inductive kn
  | _ -> []

let discharge_rename_args = function
  | _, (ReqGlobal (c, names), _) ->
     let c' = pop_global_reference c in
     let vars = section_segment_of_reference c in
     let var_names = List.map (fun (id, _,_,_) -> Name id) vars in
     let names' = List.map (fun l -> var_names @ l) names in
     Some (ReqGlobal (c', names), (c', names'))
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
  try rename_prod ty (List.hd (arguments_names ref))
  with Not_found -> ty

let rename_type_of_constant env c =
  let ty = Typeops.type_of_constant env c in
  rename_type ty (ConstRef c)

let rename_type_of_inductive env ind =
  let ty = Inductiveops.type_of_inductive env ind in
  rename_type ty (IndRef ind)

let rename_type_of_constructor env cstruct =
  let ty = Inductiveops.type_of_constructor env cstruct in
  rename_type ty (ConstructRef cstruct)

let rename_typing env c =
  let j = Typeops.typing env c in
  match kind_of_term c with
  | Const c -> { j with uj_type = rename_type j.uj_type (ConstRef c) }
  | Ind i -> { j with uj_type = rename_type j.uj_type (IndRef i) }
  | Construct k -> { j with uj_type = rename_type j.uj_type (ConstructRef k) }
  | _ -> j

