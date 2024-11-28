(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open File_util

module Error = struct

  exception CannotFindMeta of string * string
  exception CannotParseMetaFile of string * string
  exception DeclaredMLModuleNotFound of string * string * string
  exception MetaLacksFieldForPackage of string * string * string

  let no_meta f package = raise @@ CannotFindMeta (f, package)
  let cannot_parse_meta_file file msg = raise @@ CannotParseMetaFile (file,msg)
  let declare_in_META f s m = raise @@ DeclaredMLModuleNotFound (f, s, m)
  let meta_file_lacks_field meta_file package field = raise @@ MetaLacksFieldForPackage (meta_file, package, field)

  let _ = CErrors.register_handler @@ function
    | CannotFindMeta (f, package) ->
      Some Pp.(str "in file" ++ spc () ++ str f ++ str "," ++ spc ()
               ++ str "could not find META." ++ str package ++ str ".")
    | CannotParseMetaFile (file, msg) ->
      Some Pp.(str "META file \"" ++ str file ++ str "\":" ++ spc ()
               ++ str "Syntax error:" ++ spc () ++ str msg)
    | DeclaredMLModuleNotFound (f, s, m) ->
      Some Pp.(str "in file " ++ str f ++ str "," ++ spc() ++ str "declared ML module" ++ spc ()
               ++ str s ++ spc () ++ str "has not been found in" ++ spc () ++ str m ++ str ".")
    | MetaLacksFieldForPackage (meta_file, package, field) ->
      Some Pp.(str "META file \"" ++ str meta_file ++ str "\"" ++ spc () ++ str "lacks field" ++ spc ()
               ++ str field ++ spc () ++ str "for package" ++ spc () ++ str package ++ str ".")
    | _ -> None
end

(* Platform build is doing something weird with META, hence we parse
   when finding, but at some point we should find, then parse. *)
let parse_META meta_file package =
  try
    let ic = open_in meta_file in
    let m = Fl_metascanner.parse ic in
    close_in ic;
    Some m
  with
  (* This should not be necessary, but there's a problem in the platform build *)
  | Sys_error _msg -> None
  (* findlib >= 1.9.3 uses its own Error exception, so we can't catch
     it without bumping our version requirements. TODO pass the message on once we bump. *)
  | _ -> Error.cannot_parse_meta_file package ""

let find_parsable_META package =
  (try
     let meta_file = Findlib.package_meta_file package in
     Option.map (fun meta -> meta_file, meta) (parse_META meta_file package)
   with Fl_package_base.No_such_package _ -> None)

let rec find_plugin_field_opt fld = function
  | [] ->
    None
  | { Fl_metascanner.def_var; def_value; Fl_metascanner.def_preds ;_ } :: rest ->
    if String.equal def_var fld
    then Some def_value
    else find_plugin_field_opt fld rest

let find_plugin_field fld def pkgs =
  Option.default def (find_plugin_field_opt fld pkgs)

let rec find_plugin meta_file plugin_name path p { Fl_metascanner.pkg_defs ; pkg_children  } =
  match p with
  | [] -> path, pkg_defs
  | p :: ps ->
    let c =
      match CList.assoc_f_opt String.equal p pkg_children with
      | None -> Error.declare_in_META meta_file (String.concat "." plugin_name) meta_file
      | Some c -> c
    in
    let path = path @ [find_plugin_field "directory" "." c.Fl_metascanner.pkg_defs] in
    find_plugin meta_file plugin_name path ps c

let findlib_resolve ~file ~package ~plugin_name =
  let (meta_file, meta) =
    match find_parsable_META package with
    | None   -> Error.no_meta file package
    | Some v -> v
  in
  let path = [find_plugin_field "directory" "." meta.Fl_metascanner.pkg_defs] in
  let path, plug = find_plugin meta_file plugin_name path plugin_name meta in
  let cmxs_file =
    let file =
      match find_plugin_field_opt "plugin" plug with
      | None -> Error.meta_file_lacks_field meta_file package "plugin"
      | Some file -> file
    in
    let add d file =
      if d = Filename.current_dir_name then file else Filename.concat d file
    in
    List.fold_right add path file
  in
  let meta_file =
    (* relativize the path if inside the current dune workspace
       if we relativize paths outside the dune workspace it fails so make sure to avoid it *)
    match Sys.getenv_opt "DUNE_SOURCEROOT" with
    | Some dune when CString.is_prefix dune meta_file ->
      normalize_path (to_relative_path meta_file)
    | _ -> meta_file
  in
  let cmxs_file =
    let meta_dir = Filename.dirname meta_file in
    normalize_path (Filename.concat meta_dir cmxs_file)
  in
  (meta_file, cmxs_file)
