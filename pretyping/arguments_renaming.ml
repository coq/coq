(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*i*)
open Names
open Globnames
open Constr
open Context
open Environ
open Util
open Libobject

(*i*)

let name_table =
  Summary.ref (GlobRef.Map.empty : Name.t list GlobRef.Map.t)
    ~name:"rename-arguments"

type req =
  | ReqLocal
  | ReqGlobal

let load_rename_args _ (_, (r, names)) =
  name_table := GlobRef.Map.add r names !name_table

let cache_rename_args o = load_rename_args 1 o

let classify_rename_args = function
  | ReqLocal, _ -> Dispose
  | ReqGlobal, _ -> Substitute

let subst_rename_args (subst, (_, (r, names as orig))) =
  ReqLocal,
  let r' = fst (subst_global subst r) in
  if r==r' then orig else (r', names)

let discharge_rename_args = function
  | ReqGlobal, (c, names) as req when not (isVarRef c && Lib.is_in_section c) ->
     (try
       let var_names = Array.map_to_list (fun c -> Name (destVar c)) (Lib.section_instance c) in
       let names = var_names @ names in
       Some (ReqGlobal, (c, names))
     with Not_found -> Some req)
  | _ -> None

let inRenameArgs = declare_object { (default_object "RENAME-ARGUMENTS" ) with
  load_function = load_rename_args;
  cache_function = cache_rename_args;
  classify_function = classify_rename_args;
  subst_function = subst_rename_args;
  discharge_function = discharge_rename_args;
}

let rename_arguments local r names =
  let () = match r with
    | GlobRef.VarRef id ->
      CErrors.user_err
        Pp.(str "Arguments of section variables such as "
            ++ Id.print id
            ++ str" may not be renamed.")
    | _ -> ()
  in
  let req = if local then ReqLocal else ReqGlobal in
  Lib.add_leaf (inRenameArgs (req, (r, names)))

let arguments_names r = GlobRef.Map.find r !name_table

let rename_type ty ref =
  let name_override old_name override =
    match override with
    | Name _ as x -> {old_name with binder_name=x}
    | Anonymous -> old_name in
  let rec rename_type_aux c = function
    | [] -> c
    | rename :: rest as renamings ->
        match Constr.kind c with
        | Prod (old, s, t) ->
            mkProd (name_override old rename, s, rename_type_aux t rest)
        | LetIn (old, s, b, t) ->
            mkLetIn (old ,s, b, rename_type_aux t renamings)
        | Cast (t,_, _) -> rename_type_aux t renamings
        | _ -> c
  in
  try rename_type_aux ty (arguments_names ref)
  with Not_found -> ty

let rename_typing env c =
  let j = Typeops.infer env c in
  let j' =
    match kind c with
    | Const (c,u) -> { j with uj_type = rename_type j.uj_type (GlobRef.ConstRef c) }
    | Ind (i,u) -> { j with uj_type = rename_type j.uj_type (GlobRef.IndRef i) }
    | Construct (k,u) -> { j with uj_type = rename_type j.uj_type (GlobRef.ConstructRef k) }
    | _ -> j
  in j'

