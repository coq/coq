(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
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
  name_table := GlobRef.Map.add r names !name_table;
  Global.rename_ref r names

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
       let var_names = Array.map_to_list (fun c -> Name (Constr.destVar c)) (Lib.section_instance c) in
       let names = var_names @ names in
       Some (ReqGlobal, (c, names))
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
