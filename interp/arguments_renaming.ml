(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*i*)
open Names
open Globnames
open Util
open Libobject

module NamedDecl = Context.Named.Declaration
(*i*)

let name_table =
  Summary.ref (GlobRef.Map.empty : Name.t list GlobRef.Map.t)
    ~name:"rename-arguments"

type req =
  | ReqLocal
  | ReqGlobal of GlobRef.t * Name.t list

let load_rename_args _ (_, (_, (r, names))) =
  name_table := GlobRef.Map.add r names !name_table;
  Global.rename_ref r names

let cache_rename_args o = load_rename_args 1 o

let classify_rename_args = function
  | ReqLocal, _ -> Dispose
  | ReqGlobal _, _ as o -> Substitute o

let subst_rename_args (subst, (_, (r, names as orig))) =
  ReqLocal,
  let r' = fst (subst_global subst r) in
  if r==r' then orig else (r', names)

let discharge_rename_args = function
  | _, (ReqGlobal (c, names), _ as req) when not (isVarRef c && Lib.is_in_section c) ->
     (try
       let vars = Lib.variable_section_segment_of_reference c in
       let var_names = List.map (NamedDecl.get_id %> Name.mk_name) vars in
       let names' = var_names @ names in
       Some (ReqGlobal (c, names), (c, names'))
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

let rename_arguments ~local r names =
  let req = if local then ReqLocal else ReqGlobal (r, names) in
  Lib.add_anonymous_leaf (inRenameArgs (req, (r, names)))

let arguments_names r = GlobRef.Map.find r !name_table
