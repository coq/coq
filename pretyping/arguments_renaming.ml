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
open Context
open Environ
open Util

module NamedDecl = Context.Named.Declaration
(*i*)

let name_table =
  Summary.ref (GlobRef.Map.empty : Name.t list GlobRef.Map.t)
    ~name:"rename-arguments"

let discharge_rename_args = function
  | (c, names as orig) when not (isVarRef c && Lib.is_in_section c) ->
     (try
       let vars = Lib.variable_section_segment_of_reference c in
       let var_names = List.map (fst %> NamedDecl.get_id %> Name.mk_name) vars in
       let names' = var_names @ names in
       Some (c, names')
     with Not_found -> Some orig)
  | _ -> None

let rename_arguments r names =
  name_table := GlobRef.Map.add r names !name_table

let arguments_names r = GlobRef.Map.find r !name_table

let rename_type ty ref =
  let name_override old_name override =
    match override with
    | Name _ as x -> {old_name with binder_name=x}
    | Anonymous -> old_name in
  let rec rename_type_aux c = function
    | [] -> c
    | rename :: rest as renamings ->
        match kind_of_type c with
        | ProdType (old, s, t) ->
            mkProd (name_override old rename, s, rename_type_aux t rest)
        | LetInType(old, s, b, t) ->
            mkLetIn (old ,s, b, rename_type_aux t renamings)
        | CastType (t,_) -> rename_type_aux t renamings
        | SortType _ -> c
        | AtomicType _ -> c in
  try rename_type_aux ty (arguments_names ref)
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

